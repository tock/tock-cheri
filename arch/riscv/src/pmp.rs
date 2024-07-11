//! Implementation of the physical memory protection unit (PMP).
//!
//! ## Implementation
//!
//! We use the PMP Top of Region (TOR) alignment as there are alignment issues
//! with NAPOT. NAPOT would allow us to protect more memory regions (with NAPOT
//! each PMP region can be a memory region), but the problem with NAPOT is the
//! address must be aligned to the size, which results in wasted memory. To
//! avoid this wasted memory we use TOR and each memory region uses two physical
//! PMP regions.

use core::cell::Cell;
use core::fmt;
use core::{cmp, mem};
use kernel::utilities::cells::OptionalCell;

use crate::csr;
use kernel::platform::mpu;
use kernel::platform::mpu::RemoveRegionResult;
use kernel::utilities::cells::MapCell;
use kernel::utilities::registers::{self, register_bitfields};
use kernel::utilities::singleton_checker::SingletonChecker;
use kernel::ErrorCode::INVAL;
use kernel::{ErrorCode, ProcessId};
use tock_registers::interfaces::Writeable;

// Generic PMP config
register_bitfields![u8,
    pub pmpcfg [
        r OFFSET(0) NUMBITS(1) [],
        w OFFSET(1) NUMBITS(1) [],
        x OFFSET(2) NUMBITS(1) [],
        a OFFSET(3) NUMBITS(2) [
            OFF = 0,
            TOR = 1,
            NA4 = 2,
            NAPOT = 3
        ],
        l OFFSET(7) NUMBITS(1) []
    ]
];

// This is to handle a QEMU bug. QEMU tries not to do a PMP check for every instruction,
// but when a PMP check is performed, the access size is not known because QEMU
// does not know how many instructions it will translate for one basic block.
// Instead, it just checks if an entire page worth could be translated.
// This requires us to over align to the size QEMU assumes is a page.
#[cfg(feature = "page_align_pmp")]
const PMP_ALIGN: usize = 0x1000;

// I know PMP align is actually 4, but by making it 8 I can get rid of the whole "sizes less than
// 8 need to be rounded up to 8, but sizes greater than 8 to the nearest 4" nonsense.

#[cfg(not(feature = "page_align_pmp"))]
const PMP_ALIGN: usize = 8;

// Align down, return difference
fn align_down_diff(an_addr: &mut usize) -> usize {
    let diff = *an_addr % PMP_ALIGN;
    *an_addr -= diff;
    diff
}

fn align_up(an_addr: &mut usize) {
    *an_addr = *an_addr + ((0usize - *an_addr) % PMP_ALIGN)
}

fn align_region(start: &mut usize, size: &mut usize) {
    // Region start round up
    *size += align_down_diff(start);

    // Region size round up
    align_up(size);

    // Regions must be at least 8 bytes
    if *size < 8 {
        *size = if 8 > PMP_ALIGN { 8 } else { PMP_ALIGN };
    }
}

/// Main PMP struct.
///
/// Tock will ignore locked PMP regions. Note that Tock will not make any
/// attempt to avoid access faults from locked regions.
///
/// `MAX_AVAILABLE_REGIONS_OVER_TWO`: The number of PMP regions divided by 2.
///  The RISC-V spec mandates that there must be either 0, 16 or 64 PMP
///  regions implemented. If you are using this PMP struct we are assuming
///  there are more than 0 implemented. So this value should be either 8 or 32.
///
///  If however you know the exact number of PMP regions implemented by your
///  platform and it's not going to change you can just specify the number.
///  This means that Tock won't be able to dynamically handle more regions,
///  but it will reduce runtime space requirements.
///  Note: that this does not mean all PMP regions are connected.
///  Some of the regions can be WARL (Write Any Read Legal). All this means
///  is that accessing `NUM_REGIONS` won't cause a fault.
pub struct PMP<const MAX_AVAILABLE_REGIONS_OVER_TWO: usize> {
    /// The application that the MPU was last configured for. Used (along with
    /// the `is_dirty` flag) to determine if MPU can skip writing the
    /// configuration to hardware.
    last_configured_for: MapCell<ProcessId>,
    /// This is a 64-bit mask of locked regions.
    /// Each bit that is set in this mask indicates that the region is locked
    /// and cannot be used by Tock.
    locked_region_mask: Cell<u64>,
    /// This is the total number of available regions.
    /// This will be between 0 and MAX_AVAILABLE_REGIONS_OVER_TWO * 2 depending
    /// on the hardware and previous boot stages.
    num_regions: Cell<usize>,
}

fn set_pmp_region(region: &Option<PMPRegion>, with_index: usize) {
    match region {
        Some(r) => {
            let cfg_val = r.cfg.value as usize;
            let start = r.location.0 as usize;
            let size = r.location.1;

            let disable_val = (csr::pmpconfig::pmpcfg::r0::CLEAR
                + csr::pmpconfig::pmpcfg::w0::CLEAR
                + csr::pmpconfig::pmpcfg::x0::CLEAR
                + csr::pmpconfig::pmpcfg::a0::OFF)
                .value;
            let index = csr::CSR::pmp_index_to_cfg_index(2 * with_index);
            // Second region has sub_index + 1
            let sub_index = csr::CSR::pmp_index_to_cfg_sub_index(2 * with_index);
            let region_shift = sub_index * 8;
            let other_region_mask: usize = !(0xFFFFusize << region_shift);

            csr::CSR.pmpaddr_set(with_index * 2, (start) >> 2);
            csr::CSR.pmpaddr_set((with_index * 2) + 1, (start + size) >> 2);

            csr::CSR.pmpconfig_set(
                index,
                (disable_val | cfg_val << 8) << region_shift
                    | (csr::CSR.pmpconfig_get(index) & other_region_mask),
            );
        }
        None => {}
    };
}

impl<const MAX_AVAILABLE_REGIONS_OVER_TWO: usize> PMP<MAX_AVAILABLE_REGIONS_OVER_TWO> {
    pub const fn const_new(chk: &mut SingletonChecker) -> Self {
        kernel::assert_single!(chk);
        Self {
            last_configured_for: MapCell::empty(),
            num_regions: Cell::new(0),
            locked_region_mask: Cell::new(0),
        }
    }

    // Safety: singleton
    pub unsafe fn new() -> Self {
        let pmp = Self {
            last_configured_for: MapCell::empty(),
            num_regions: Cell::new(0),
            locked_region_mask: Cell::new(0),
        };
        pmp.init();
        pmp
    }

    pub fn init(&self) {
        // This scan will clear the PMP so cannot be run if we are configured
        if self.last_configured_for.is_some() {
            return;
        }
        // RISC-V PMP can support from 0 to 64 PMP regions
        // Let's figure out how many are supported.
        // We count any regions that are locked as unsupported
        let mut num_regions = 0;
        let mut locked_region_mask = 0;

        for i in 0..(MAX_AVAILABLE_REGIONS_OVER_TWO * 2) {
            let index = csr::CSR::pmp_index_to_cfg_index(i);
            let shift = csr::CSR::pmp_index_to_cfg_sub_index(i) * 8;

            // Read the current value
            let pmpcfg_og = csr::CSR.pmpconfig_get(index);

            // Flip R, W, X bits
            let pmpcfg_new = pmpcfg_og ^ (3 << shift);
            csr::CSR.pmpconfig_set(index, pmpcfg_new);

            // Check if the bits are set
            let pmpcfg_check = csr::CSR.pmpconfig_get(index);

            // Check if the changes stuck
            if pmpcfg_check == pmpcfg_og {
                // If we get here then our changes didn't stick, let's figure
                // out why

                // Check if the locked bit is set
                if pmpcfg_og & ((1 << 7) << shift) > 0 {
                    // The bit is locked. Mark this regions as not usable
                    locked_region_mask |= 1 << i;
                } else {
                    // The locked bit isn't set
                    // This region must not be connected, which means we have run out
                    // of usable regions, break the loop
                    break;
                }
            } else {
                // Found a working region
                num_regions += 1;
            }

            // Reset back to how we found it
            csr::CSR.pmpconfig_set(index, pmpcfg_og);
        }

        self.locked_region_mask.set(locked_region_mask);
        self.num_regions.set(num_regions);
    }
}

/// Struct storing configuration for a RISC-V PMP region.
#[derive(Copy, Clone)]
pub struct PMPRegion {
    location: (*const u8, usize),
    cfg: registers::FieldValue<u8, pmpcfg::Register>,
}

impl PartialEq<mpu::Region> for PMPRegion {
    fn eq(&self, other: &mpu::Region) -> bool {
        self.location.0 == other.start_address() && self.location.1 == other.size()
    }
}

impl fmt::Display for PMPRegion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn bit_str<'a>(reg: &PMPRegion, bit: u8, on_str: &'a str, off_str: &'a str) -> &'a str {
            match reg.cfg.value & bit as u8 {
                0 => off_str,
                _ => on_str,
            }
        }

        write!(
            f,
            "addr={:p}, size={:#010X}, cfg={:#X} ({}{}{})",
            self.location.0,
            self.location.1,
            u8::from(self.cfg),
            bit_str(self, pmpcfg::r::SET.value, "r", "-"),
            bit_str(self, pmpcfg::w::SET.value, "w", "-"),
            bit_str(self, pmpcfg::x::SET.value, "x", "-"),
        )
    }
}

impl PMPRegion {
    fn new(start: *const u8, size: usize, permissions: mpu::Permissions) -> PMPRegion {
        // Determine access and execute permissions
        let pmpcfg = match permissions {
            mpu::Permissions::ReadWriteExecute => {
                pmpcfg::r::SET + pmpcfg::w::SET + pmpcfg::x::SET + pmpcfg::a::TOR
            }
            mpu::Permissions::ReadWriteOnly => {
                pmpcfg::r::SET + pmpcfg::w::SET + pmpcfg::x::CLEAR + pmpcfg::a::TOR
            }
            mpu::Permissions::ReadExecuteOnly => {
                pmpcfg::r::SET + pmpcfg::w::CLEAR + pmpcfg::x::SET + pmpcfg::a::TOR
            }
            mpu::Permissions::ReadOnly => {
                pmpcfg::r::SET + pmpcfg::w::CLEAR + pmpcfg::x::CLEAR + pmpcfg::a::TOR
            }
            mpu::Permissions::ExecuteOnly => {
                pmpcfg::r::CLEAR + pmpcfg::w::CLEAR + pmpcfg::x::SET + pmpcfg::a::TOR
            }
        };

        PMPRegion {
            location: (start, size),
            cfg: pmpcfg,
        }
    }

    fn location(&self) -> (*const u8, usize) {
        self.location
    }

    /// Check if the PMP regions specified by `other_start` and `other_size`
    /// overlaps with the current region.
    /// Matching the RISC-V spec this checks pmpaddr[i-i] <= y < pmpaddr[i] for
    /// TOR ranges.
    fn overlaps(&self, other_start: *const u8, other_size: usize) -> bool {
        let other_start = other_start as usize;
        let other_end = other_start + other_size;

        let (region_start, region_size) = self.location;

        let (region_start, region_end) = {
            let region_start = region_start as usize;
            let region_end = region_start + region_size;
            (region_start, region_end)
        };

        // PMP addresses are not inclusive on the high end, that is
        //     pmpaddr[i-i] <= y < pmpaddr[i]
        if region_start < (other_end - 4) && other_start < (region_end - 4) {
            true
        } else {
            false
        }
    }
}

/// Struct storing region configuration for RISCV PMP.
pub struct PMPConfig<const MAX_AVAILABLE_REGIONS_OVER_TWO: usize> {
    /// Array of PMP regions. Each region requires two physical entries.
    regions: [Option<PMPRegion>; MAX_AVAILABLE_REGIONS_OVER_TWO],
    /// Indicates if the configuration has changed since the last time it was
    /// written to hardware.
    is_dirty: Cell<bool>,
    /// Which region index is used for app memory (if it has been configured).
    app_memory_region: OptionalCell<usize>,
}

impl<const MAX_AVAILABLE_REGIONS_OVER_TWO: usize> Default
    for PMPConfig<MAX_AVAILABLE_REGIONS_OVER_TWO>
{
    /// `NUM_REGIONS` is the number of PMP entries the hardware supports.
    ///
    /// Since we use TOR, we will use two PMP entries for each region. So the actual
    /// number of regions we can protect is `NUM_REGIONS/2`. Limitations of min_const_generics
    /// require us to pass both of these values as separate generic consts.
    fn default() -> Self {
        PMPConfig {
            regions: [None; MAX_AVAILABLE_REGIONS_OVER_TWO],
            is_dirty: Cell::new(true),
            app_memory_region: OptionalCell::empty(),
        }
    }
}

impl<const MAX_AVAILABLE_REGIONS_OVER_TWO: usize> fmt::Display
    for PMPConfig<MAX_AVAILABLE_REGIONS_OVER_TWO>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, " PMP regions:\r\n")?;
        for (n, region) in self.regions.iter().enumerate() {
            match region {
                None => write!(f, "  <unset>\r\n")?,
                Some(region) => write!(f, "  [{}]: {}\r\n", n, region)?,
            }
        }
        Ok(())
    }
}

impl<const MAX_AVAILABLE_REGIONS_OVER_TWO: usize> PMPConfig<MAX_AVAILABLE_REGIONS_OVER_TWO> {
    /// Get the first unused region
    fn unused_region_number(&self, locked_region_mask: u64) -> Option<usize> {
        for (number, region) in self.regions.iter().enumerate() {
            if !self.is_index_locked_or_app(locked_region_mask, number) && region.is_none() {
                return Some(number);
            }
        }
        None
    }

    /// Get the last unused region
    /// The app regions need to be lower then the kernel to ensure they
    /// match before the kernel ones.
    fn unused_kernel_region_number(&self, locked_region_mask: u64) -> Option<usize> {
        // It is important to enumerate first, then reverse otherwise the enumeration index
        // won't match the array index
        for (number, region) in self.regions.iter().enumerate().rev() {
            if !self.is_index_locked_or_app(locked_region_mask, number) && region.is_none() {
                return Some(number);
            }
        }
        None
    }

    /// Returns true is the specified index is either locked or corresponds to the app region
    fn is_index_locked_or_app(&self, locked_region_mask: u64, number: usize) -> bool {
        locked_region_mask & (1 << number) > 0 || self.app_memory_region.contains(&number)
    }
}

impl<const MAX_AVAILABLE_REGIONS_OVER_TWO: usize> kernel::platform::mpu::MPU
    for PMP<MAX_AVAILABLE_REGIONS_OVER_TWO>
{
    type MpuConfig = PMPConfig<MAX_AVAILABLE_REGIONS_OVER_TWO>;
    const MIN_MPUALIGN: usize = PMP_ALIGN;

    fn clear_mpu(&self) {
        // We want to disable all of the hardware entries, so we use `NUM_REGIONS` here,
        // and not `NUM_REGIONS / 2`.
        //
        // We want to keep the first region configured, so it is excluded from the loops and
        // set separately.
        for x in 1..(MAX_AVAILABLE_REGIONS_OVER_TWO * 2) {
            csr::CSR.pmpaddr_set(x, 0x0);
        }
        for x in 1..(MAX_AVAILABLE_REGIONS_OVER_TWO * 2 / mem::size_of::<usize>()) {
            csr::CSR.pmpconfig_set(x * (mem::size_of::<usize>() / 4), 0);
        }
        csr::CSR.pmpaddr_set(0, usize::MAX);
        // enable R W X fields
        csr::CSR.pmpconfig_set(
            0,
            (csr::pmpconfig::pmpcfg::r0::SET
                + csr::pmpconfig::pmpcfg::w0::SET
                + csr::pmpconfig::pmpcfg::x0::SET
                + csr::pmpconfig::pmpcfg::a0::TOR)
                .value,
        );
        // PMP is not configured for any process now
        self.last_configured_for.take();
    }

    fn enable_app_mpu(&self) {}

    fn disable_app_mpu(&self) {
        // PMP is not enabled for machine mode, so we don't have to do
        // anything
    }

    fn number_total_regions(&self) -> usize {
        self.num_regions.get() / 2
    }

    fn allocate_region(
        &self,
        unallocated_memory_start: *const u8,
        unallocated_memory_size: usize,
        min_region_size: usize,
        permissions: mpu::Permissions,
        config: &mut Self::MpuConfig,
    ) -> Option<mpu::Region> {
        for region in config.regions.iter() {
            if region.is_some() {
                if region
                    .unwrap()
                    .overlaps(unallocated_memory_start, unallocated_memory_size)
                {
                    return None;
                }
            }
        }

        let region_num = config.unused_region_number(self.locked_region_mask.get())?;

        // Logical region
        let mut start = unallocated_memory_start as usize;
        let mut size = min_region_size;

        align_region(&mut start, &mut size);

        let region = PMPRegion::new(start as *const u8, size, permissions);

        config.regions[region_num] = Some(region);
        config.is_dirty.set(true);

        Some(mpu::Region::new(start as *const u8, size))
    }

    fn remove_memory_region(
        &self,
        region: mpu::Region,
        config: &mut Self::MpuConfig,
    ) -> Result<RemoveRegionResult, ErrorCode> {
        let (index, _r) = config
            .regions
            .iter()
            .enumerate()
            .find(|(_idx, r)| r.map_or(false, |r| r == region))
            .ok_or(INVAL)?;

        if config.is_index_locked_or_app(self.locked_region_mask.get(), index) {
            return Err(INVAL);
        }

        config.regions[index] = None;
        config.is_dirty.set(true);

        Ok(RemoveRegionResult::Sync)
    }

    fn allocate_app_memory_region(
        &self,
        unallocated_memory_start: *const u8,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        permissions: mpu::Permissions,
        config: &mut Self::MpuConfig,
    ) -> Option<(*const u8, usize)> {
        // Check that no previously allocated regions overlap the unallocated memory.
        for region in config.regions.iter() {
            if region.is_some() {
                if region
                    .unwrap()
                    .overlaps(unallocated_memory_start, unallocated_memory_size)
                {
                    return None;
                }
            }
        }

        let region_num = if config.app_memory_region.is_some() {
            config.app_memory_region.unwrap_or(0)
        } else {
            config.unused_region_number(self.locked_region_mask.get())?
        };

        // App memory size is what we actual set the region to. So this region
        // has to be aligned to 4 bytes.
        let mut initial_app_memory_size: usize = initial_app_memory_size;

        align_up(&mut initial_app_memory_size);

        // Make sure there is enough memory for app memory and kernel memory.
        let mut region_size = cmp::max(
            min_memory_size,
            initial_app_memory_size + initial_kernel_memory_size,
        ) as usize;

        // The region should start as close as possible to the start of the unallocated memory.
        let mut region_start = unallocated_memory_start as usize;

        align_region(&mut region_start, &mut region_size);

        // Make sure the region fits in the unallocated memory.
        if region_start + region_size
            > (unallocated_memory_start as usize) + unallocated_memory_size
        {
            return None;
        }

        let region = PMPRegion::new(
            region_start as *const u8,
            initial_app_memory_size,
            permissions,
        );

        config.regions[region_num] = Some(region);
        config.is_dirty.set(true);

        config.app_memory_region.set(region_num);

        Some((region_start as *const u8, region_size))
    }

    fn update_app_memory_region(
        &self,
        app_memory_break: *const u8,
        kernel_memory_break: *const u8,
        permissions: mpu::Permissions,
        config: &mut Self::MpuConfig,
    ) -> Result<(), ()> {
        let region_num = config.app_memory_region.unwrap_or(0);

        let (region_start, _) = match config.regions[region_num] {
            Some(region) => region.location(),
            None => {
                // Error: Process tried to update app memory MPU region before it was created.
                return Err(());
            }
        };

        let app_memory_break = app_memory_break as usize;
        let kernel_memory_break = kernel_memory_break as usize;

        let mut region_start = region_start as usize;
        let mut region_size = app_memory_break - region_start as usize;

        // It is OK to be overly permissive in setting up the PMP as long as we do not cross the
        // kernel memory break. This is mostly to fix the QEMU bug.
        align_region(&mut region_start, &mut region_size);

        let app_memory_break = region_start + region_size;

        // Out of memory
        if app_memory_break > kernel_memory_break {
            return Err(());
        }

        let region = PMPRegion::new(region_start as *const u8, region_size, permissions);

        config.regions[region_num] = Some(region);
        config.is_dirty.set(true);

        Ok(())
    }

    fn configure_mpu(&self, config: &Self::MpuConfig, app_id: &ProcessId) {
        // Is the PMP already configured for this app?
        let last_configured_for_this_app = self
            .last_configured_for
            .map_or(false, |last_app_id| last_app_id == app_id);

        // Skip PMP configuration if it is already configured for this app and the MPU
        // configuration of this app has not changed.
        if !last_configured_for_this_app || config.is_dirty.get() {
            for (x, region) in config.regions.iter().enumerate() {
                set_pmp_region(region, x);
            }
            config.is_dirty.set(false);
            self.last_configured_for.put(*app_id);
        }
    }
}

/// This is PMP support for kernel regions
/// PMP does not allow a deny by default option, so all regions not marked
/// with the below commands will have full access.
/// This is still a useful implementation as it can be used to limit the
/// kernels access, for example removing execute permission from regions
/// we don't need to execute from and removing write permissions from
/// executable regions.
impl<const MAX_AVAILABLE_REGIONS_OVER_TWO: usize> kernel::platform::mpu::KernelMPU
    for PMP<MAX_AVAILABLE_REGIONS_OVER_TWO>
{
    type KernelMpuConfig = PMPConfig<MAX_AVAILABLE_REGIONS_OVER_TWO>;

    fn allocate_kernel_region(
        &self,
        memory_start: *const u8,
        memory_size: usize,
        permissions: mpu::Permissions,
        config: &mut Self::KernelMpuConfig,
    ) -> Option<mpu::Region> {
        for region in config.regions.iter() {
            if region.is_some() {
                if region.unwrap().overlaps(memory_start, memory_size) {
                    return None;
                }
            }
        }

        let region_num = config.unused_kernel_region_number(self.locked_region_mask.get())?;

        // Logical region
        let mut start = memory_start as usize;
        let mut size = memory_size;

        align_region(&mut start, &mut size);

        let mut region = PMPRegion::new(start as *const u8, size, permissions);
        // Once set this should be locked.
        // NOTE: Locking a TOR region also locks the one before it
        region.cfg += pmpcfg::l::SET;

        config.regions[region_num] = Some(region);

        // Mark the region as locked so that the app PMP doesn't use it.
        let mut mask = self.locked_region_mask.get();
        mask |= 1 << region_num;
        self.locked_region_mask.set(mask);

        Some(mpu::Region::new(start as *const u8, size))
    }

    fn enable_kernel_mpu(&self, config: &mut Self::KernelMpuConfig) {
        for (i, region) in config.regions.iter().rev().enumerate() {
            // Kernel use the highest regions first as when we switch we use the lowest first
            // FIXME: Should this not be num_regions? MAX_AVAILABLE_REGIONS_OVER_TWO may not be supported.
            let x = MAX_AVAILABLE_REGIONS_OVER_TWO - i - 1;
            set_pmp_region(&region, x);
        }
    }
}

// If we have a PMP and are not using it, we still need to enable it or all accesses will fail
// It does raise the question why you are using, say, the MMU, rather than the PMP. Not enough PMP entries?
pub fn pmp_permit_all() {
    // With NAPOT, the more ones, the bigger the range.
    csr::CSR.pmpaddr0.set(usize::MAX);
    csr::CSR.pmpcfg0.write(
        csr::pmpconfig::pmpcfg::r0::SET
            + csr::pmpconfig::pmpcfg::w0::SET
            + csr::pmpconfig::pmpcfg::x0::SET
            + csr::pmpconfig::pmpcfg::a0::NAPOT,
    );
}

kernel::very_simple_component!(
    impl<{const MAX_AVAILABLE_REGIONS_OVER_TWO: usize}> for PMP::<MAX_AVAILABLE_REGIONS_OVER_TWO>,
    const_new(&'a mut SingletonChecker),
    init()
);
