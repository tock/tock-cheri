//! CHERI platforms do not need a separate MPU to enforce access to the address space
//! Access is granted by merit of passing capabilities.
//! The kernel is responsible for correctly bounding / limiting access on process creation.
//! It should be
//! 1) zero-ing any memory accessible to the process. This should be done in a few places:
//!     When a process is created (up to the brk)
//!     When a process calls brk/sbrk (from the old break to the new one)
//!     When a process is restarted TODO (part of b/266802576)
//! 2) Either zero or bound capabilities so they only cover the process on process startup (DONE)
//! 3) limiting flow of capabilities between processes via IPC TODO (b/247192904)
//! 4) Performing revocation in some cases TODO (b/280575362)
//! This module implements the MPU trait to satisfy the kernel, but it mostly does nothing. What
//! it does do is report what access control CHERI _could_ provide, assuming the kernel takes
//! the other steps.

use core::cell::Cell;
use core::fmt::{Display, Formatter};
use core::ptr::slice_from_raw_parts;
use kernel::capabilities::ProcessManagementCapability;
use kernel::cheri::{cptr, cram};
use kernel::grant::{revoke_allows, AllowRoCount, AllowRwCount, Grant, UpcallCount};
use kernel::platform::mpu::{Permissions, Region, RemoveRegionResult, MPU};
use kernel::process::{Error, Process};
use kernel::processbuffer::ReadableProcessByte;
use kernel::syscall::{CommandReturn, CommandReturnResult, SyscallDriver};
use kernel::ErrorCode::{FAIL, NOMEM};
use kernel::{ErrorCode, Kernel, ProcessId};

pub struct CheriMPU {
    grant: CheriMPUGrant,
    kernel: &'static Kernel,
    proc_manage: &'static dyn ProcessManagementCapability,
}

/// How many ranges can be revoked simultaneously.
/// If a process tries to share then unshare multiple regions at once with another process, this
/// may need to be increased.
const MAX_REVOKE_RANGES: usize = 2;

#[derive(Default, Copy, Clone)]
struct RevokeRange {
    start: usize,
    end: usize,
}

impl RevokeRange {
    pub fn contains(self, base: usize) -> bool {
        // Notes on the strictly less than end:
        // Capabilities can be zero length. Objects can be adjacent. A zero-length capability at
        // the boundary between two objects could therefore refer to either object.
        // Doing the inequality this way might result in a zero-length capability to an object
        // not being revoked because it is indistinguishable from the next object.
        // This is fine, as it cannot be used to access memory as it is zero length.
        // Users should be aware.
        base >= self.start && base < self.end
    }
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

pub mod upcalls {
    pub const ON_EPOCH: usize = 0;
}

pub mod allow_ro {
    pub const SHADOW_MAP: usize = 0;
}

pub mod allow_rw {
    pub const CTR: usize = 0;
}

pub mod commands {
    pub const SET_BASE: usize = 1;
    pub const DO_SWEEP: usize = 2;
}

#[derive(Default)]
pub struct CheriMPUGrantData {
    // base address that revocation map shadows
    revoke_base: Cell<usize>,
}

pub type CheriMPUGrant = Grant<CheriMPUGrantData, UpcallCount<1>, AllowRoCount<1>, AllowRwCount<1>>;

// Without revocation, we can't have an application decrease its brk again
#[derive(Default)]
pub struct CheriMPUConfig {
    // The largest _effective_ break we have seen.
    // Because DDC/PCC bounds setting are not exact, this is the true application break.
    // The kernel may think the break is a little less than this, but because it asks this code
    // before moving the kernel break we can still reject.
    rounded_app_brk: usize,
    // The base of the application.
    app_base: usize,
    // Ranges that need revoking
    revocation_ranges: [RevokeRange; MAX_REVOKE_RANGES],
}

impl Display for CheriMPUConfig {
    fn fmt(&self, _f: &mut Formatter<'_>) -> core::fmt::Result {
        Ok(())
    }
}

/// This alignment is the alignment of a capability, which malloc aligns to anyway.
const GRANULE_POW_2: usize = 4;
const GRANULE_SIZE: usize = 1 << GRANULE_POW_2;

/// 8 bits in a byte
const BYTES_PER_BITMAP_BYTE: usize = GRANULE_SIZE * 8;
const BITMAP_ADDRESS_MASK: usize = BYTES_PER_BITMAP_BYTE - 1;

#[derive(Copy, Clone)]
struct UserShadowMap<'a> {
    offset_base: usize,
    map: &'a [ReadableProcessByte],
}

impl<'a> UserShadowMap<'a> {
    pub fn contains(&self, base: usize) -> bool {
        // The shadow map covers a range starting at offset_base, so offset by that much
        let base = base - self.offset_base;
        // Each bit of shadow map covers GRANULE_SIZE bytes, so scale by that
        let shifted = base >> GRANULE_POW_2;
        // `Shifted` index's into bits of map, so split into a index into the map...
        let map_index = shifted >> 3;
        // ...and an index into that byte
        let byte_index = (shifted & 0x7) as u8;
        // convert byte index to mask
        let byte_mask = 1u8 << byte_index;
        // now check if the bit is set. If the map does not cover the range, default to _not_
        // revoking.
        self.map
            .get(map_index)
            .map(|byte| (byte.get() & byte_mask) != 0)
            .unwrap_or(false)
    }
}

type RevocationRange = [Cell<cptr>];

fn should_revoke(map: UserShadowMap, invalid_ranges: &[RevokeRange], base: usize) -> bool {
    map.contains(base) || invalid_ranges.iter().any(|range| range.contains(base))
}

/// Sweep a specific range
fn sweep_range(_range: &RevocationRange, _map: UserShadowMap, _invalid_ranges: &[RevokeRange]) {
    #[cfg(target_feature = "xcheri")]
    {
        for cap in _range {
            let (base, tagged) = cap.get().get_base_and_tag();
            if tagged {
                if should_revoke(_map, _invalid_ranges, base) {
                    cptr::invalidate_shared(cap)
                }
            }
        }
    }
}

fn revocation_range_from_parts(base: usize, top: usize) -> *const RevocationRange {
    let mask = core::mem::size_of::<cptr>() - 1;
    // Round down base
    let base = base & !mask;
    // Round up top
    let top = (top + mask) & !mask;
    slice_from_raw_parts(
        base as *const Cell<cptr>,
        (top - base) / core::mem::size_of::<cptr>(),
    )
}

impl CheriMPU {
    // This aligns UP base and length to the next representable range that is at least length
    // long.
    fn align_region(base: usize, length: usize) -> (usize, usize) {
        let mask = cram(length);
        let inv_mask = !mask;
        ((base + inv_mask) & mask, (length + inv_mask) & mask)
    }

    pub const fn new(
        grant: CheriMPUGrant,
        kernel: &'static Kernel,
        proc_manage: &'static dyn ProcessManagementCapability,
    ) -> Self {
        Self {
            grant,
            kernel,
            proc_manage,
        }
    }

    pub fn set_shadow_map_base(
        &self,
        data: &CheriMPUGrantData,
        base: usize,
    ) -> Result<(), ErrorCode> {
        if base & BITMAP_ADDRESS_MASK != 0 {
            return Err(ErrorCode::INVAL);
        }
        data.revoke_base.set(base);
        Ok(())
    }

    // TODO: some way of breaking this loop if a process suddenly wants scheduling
    /// Safety: the process memory that this would sweep must be valid for reads and writes
    /// Safety: no LiveARef or LivePRef may exist to any memory that might be revoked,
    /// Nor may any grants be entered via the legacy mechanism.
    pub fn revoke_sweep(
        &self,
        config: &mut CheriMPUConfig,
        proc: &dyn Process,
    ) -> Result<(), ErrorCode> {
        // NOTE: we cannot fail to revoke just because we cannot allocate a grant.
        // If we do, the user does not have enough memory to provide a shadow map, but we can
        // still revoke other capabilities that the kernel wants revoking.
        // The user will be aware revocation is not working for them as they will get a failure
        // to allow the map.
        let proc_grant = self.grant.get_for(proc.processid());

        let kern_data =
            proc_grant.map(|proc_grant| (proc_grant.get_kern_data(), proc_grant.get_grant_data()));

        // NOTE: This ARef could break the safety condition of this function.
        // that is, a user could ask us to revoke their shadow map, and at the end of this function
        // we would still have a reference to it even though revocation has finished.
        // However, because we drop this ARef at the end of this function, by the time we actually
        // return it will once again be the case that no LiveARef s exist.

        let (allow, data, ctr) = match &kern_data {
            Ok((kern_data, grant)) => (
                kern_data.get_readonly_aref(allow_ro::SHADOW_MAP),
                grant.get_pref(),
                kern_data.get_readwrite_aref(allow_rw::CTR),
            ),
            Err(_) => (Err(ErrorCode::FAIL), None, Err(ErrorCode::FAIL)),
        };

        let mut map_range = match &allow {
            Ok(live) => &*&*live,
            Err(_) => [].as_slice(),
        };

        let mut base = data.map_or(0, |data| data.revoke_base.get());

        let allowed_base = config.app_base & !BITMAP_ADDRESS_MASK;
        let allowed_top = config.rounded_app_brk & !BITMAP_ADDRESS_MASK;
        let allowed_len = allowed_top - allowed_base;

        // Clamp bottom
        let delta_bytes = if base < allowed_base {
            base = allowed_base;
            allowed_base - base
        } else {
            0
        };
        map_range = map_range
            .get(delta_bytes / BYTES_PER_BITMAP_BYTE..)
            .unwrap_or(&[]);

        // Clamp top
        let new_len = core::cmp::min(map_range.len(), allowed_len / BYTES_PER_BITMAP_BYTE);
        map_range = map_range.get(..new_len).unwrap_or(&[]);

        let map = UserShadowMap {
            offset_base: base,
            map: map_range,
        };

        let ranges = &mut config.revocation_ranges;
        // First, sweep processes own memory.
        // This includes the process itself, grants, AND the process header (including saved
        // register file)
        let proc_mem = revocation_range_from_parts(config.app_base, config.rounded_app_brk);

        sweep_range(unsafe { &*proc_mem }, map, ranges.as_slice());

        // Sweep allow-ed capabilities to see if any should be revoked.
        // NOTE: this would not be needed if cptr was stored in grants, but we strip this info
        // Safety: same requirement as safety of this function

        unsafe {
            revoke_allows(self.kernel, proc, |slice| {
                should_revoke(map, ranges, slice as *const u8 as usize)
            })?
        }

        // TODO: sweep register file, grant allows, and CLUT entries

        // Notify epoch has ticked.
        // We do so by both writing to the shared mem and sending an upcall.

        if let Ok(ctr) = ctr {
            if let Some(ctr) = ctr.align_to_u32().1.get(0) {
                let epoch = ctr.get().wrapping_add(1);
                ctr.set(epoch);
                if let Ok((kern_data, _)) = kern_data {
                    // Ignore the process being too busy to get this upcall, they will get one on next epoch
                    let _ = kern_data.schedule_upcall(upcalls::ON_EPOCH, (epoch as usize, 0, 0));
                }
            }
        }

        Ok(())
    }

    fn handle_command(
        &self,
        command_number: usize,
        arg2: usize,
        _arg3: usize,
        appid: ProcessId,
    ) -> CommandReturnResult {
        match command_number {
            commands::SET_BASE => {
                let kern_data = self.grant.get_for(appid)?;
                let new_data = kern_data.get_grant_data();
                let grant_data = new_data.get_pref().ok_or(FAIL)?;
                self.set_shadow_map_base(&*grant_data, arg2)?;
            }
            commands::DO_SWEEP => {
                self.kernel.process_map_or_external(
                    Err(ErrorCode::FAIL),
                    appid,
                    // Safety: we have created no livepref in this scope, which should be called
                    // directly from syscalls.
                    // The fact that this is called from the main kernel loop should be a safety
                    // invariant of the kernel.
                    |app| unsafe { app.revoke_regions() },
                    self.proc_manage,
                )?;
            }
            _ => {}
        }

        Ok(CommandReturn::success())
    }
}

impl MPU for CheriMPU {
    // All MPU state is stored implicitly in the saved state of the process
    type MpuConfig = CheriMPUConfig;
    // CHERI can support alignments as precise as 1
    const MIN_MPUALIGN: usize = 1;

    // This is the overly permissive aligner that finds a representable range that covers an already
    // allocated object [base,base+length)
    fn align_range(base: usize, length: usize) -> (usize, usize) {
        // The mask we get from cram is sufficient to round both length and base such that they
        // would be representable. However, this align function is not designed to allocate an
        // object, but cover one that already exists. Rounding down the base requires us to
        // increase the length by the same amount. This increase in length might change the
        // alignment requirement. Adding on a fudge factor ensures this can't happen.
        // The exact shift used here depends on the number of precision bits in the capability
        // format. 10 was chosen conservatively. It must be less than number of precision bits,
        // but can be any value smaller. Too small a value would just over-align.
        let length_and_some = length + (length >> 10);
        // The mask given by cram is all 1's in the top, and 0's in the bottom
        let mask = cram(length_and_some);
        let new_base = base & mask;
        let new_length = (length + (base - new_base) + !(mask)) & mask;
        (new_base, new_length)
    }

    fn number_total_regions(&self) -> usize {
        usize::MAX
    }

    fn allocate_region(
        &self,
        unallocated_memory_start: *const u8,
        unallocated_memory_size: usize,
        min_region_size: usize,
        _permissions: Permissions,
        _config: &mut Self::MpuConfig,
    ) -> Option<Region> {
        let (aligned_base, aligned_length) =
            Self::align_region(unallocated_memory_start as usize, min_region_size);
        if aligned_base - (unallocated_memory_start as usize) + aligned_length
            > unallocated_memory_size
        {
            None
        } else {
            Some(Region::new(aligned_base as *const u8, aligned_length))
        }
    }

    fn allocate_app_memory_region(
        &self,
        unallocated_memory_start: *const u8,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        permissions: Permissions,
        config: &mut Self::MpuConfig,
    ) -> Option<(*const u8, usize)> {
        // CHERI can always represent smaller regions as (if not more) precisely than larger ones.
        // This means it is sound to just try allocate this much memory, and then assume we could
        // put a kernel/app break somewhere sensible within it, although not anywhere.
        let memory_size = core::cmp::max(
            min_memory_size,
            initial_app_memory_size + initial_kernel_memory_size,
        );
        let result = self.allocate_region(
            unallocated_memory_start,
            unallocated_memory_size,
            memory_size,
            permissions,
            config,
        );

        result.map(|result| {
            config.app_base = result.start_address() as usize;
            let (initial_base, initial_break_len) =
                Self::align_region(config.app_base, initial_app_memory_size);
            config.rounded_app_brk = config.app_base + initial_break_len;
            // After rounding, the base of the app region should not move and should not overlap the kernel
            assert!(
                initial_base == config.app_base
                    && (initial_break_len + initial_kernel_memory_size) <= result.size()
            );

            (result.start_address(), result.size())
        })
    }

    fn remove_memory_region(
        &self,
        region: Region,
        config: &mut Self::MpuConfig,
    ) -> Result<RemoveRegionResult, ErrorCode> {
        // If we have space in our list, add it in.
        for range in config.revocation_ranges.iter_mut() {
            if range.is_empty() {
                *range = RevokeRange {
                    start: region.start_address() as usize,
                    end: region.start_address() as usize + region.size(),
                };
                return Ok(RemoveRegionResult::Async(Default::default()));
            }
        }
        Err(NOMEM)
    }

    #[allow(unused_variables)]
    fn update_app_memory_region(
        &self,
        app_memory_break: *const u8,
        kernel_memory_break: *const u8,
        permissions: Permissions,
        config: &mut Self::MpuConfig,
    ) -> Result<(), ()> {
        // What is being requested
        let (target_base, target_break) = (config.app_base, app_memory_break as usize);
        // What imprecise bounds setting would result in
        let (rounded_base, rounded_break_length) =
            Self::align_region(target_base, target_break - target_base);

        let rounded_break = rounded_base + rounded_break_length;

        let max_rounded_break = core::cmp::max(rounded_break, config.rounded_app_brk);

        // Because we might have released a capability to the application, we don't allow a kernel
        // memory break that crosses the largest rounded app brk.
        // We also don't allow the base of the capability to ever move.
        if target_base != rounded_base || max_rounded_break > (kernel_memory_break as usize) {
            Err(())
        } else {
            config.rounded_app_brk = max_rounded_break;
            Ok(())
        }
    }

    #[inline]
    unsafe fn revoke_regions(
        &self,
        config: &mut Self::MpuConfig,
        proc: &dyn Process,
    ) -> Result<(), ErrorCode> {
        let result = self.revoke_sweep(config, proc);

        // Ranges can be used again
        if result.is_ok() {
            for region in &mut config.revocation_ranges {
                *region = Default::default()
            }
        }

        result
    }

    fn enable_app_mpu(&self) {}

    fn disable_app_mpu(&self) {}

    fn new_config(&self) -> Option<Self::MpuConfig> {
        Some(Default::default())
    }

    fn reset_config(&self, config: &mut Self::MpuConfig) {
        *config = Default::default();
    }

    fn configure_mpu(&self, _config: &Self::MpuConfig) {}
}

impl SyscallDriver for CheriMPU {
    fn command(
        &self,
        command_num: usize,
        r2: usize,
        r3: usize,
        process_id: ProcessId,
    ) -> CommandReturn {
        self.handle_command(command_num, r2, r3, process_id).into()
    }

    fn allocate_grant(&self, process_id: ProcessId) -> Result<(), Error> {
        self.grant.enter(process_id, |_, _| {})
    }
}

kernel::very_simple_component!(impl for CheriMPU, new(CheriMPUGrant, &'static Kernel, &'static dyn ProcessManagementCapability));
