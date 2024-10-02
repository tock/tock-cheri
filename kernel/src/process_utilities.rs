FIXME: Rebase lost this file. Where does it go?

//! Helper functions related to Tock processes.

use core::convert::TryInto;
use core::fmt;

use crate::capabilities::ProcessManagementCapability;
use crate::config;
use crate::kernel::Kernel;
use crate::platform::chip::Chip;
use crate::platform::mpu::MPU;
use crate::process_policies::ProcessFaultPolicy;
use crate::process_standard::ProcessStandard;
use crate::{debug, ErrorCode};

/// Errors that can occur when trying to load and create processes.
pub enum ProcessLoadError {
    /// The TBF header for the process could not be successfully parsed.
    TbfHeaderParseFailure(tock_tbf::types::TbfParseError),

    /// Not enough flash remaining to parse a process and its header.
    NotEnoughFlash,

    /// Not enough memory to meet the amount requested by a process. Modify the
    /// process to request less memory, flash fewer processes, or increase the
    /// size of the region your board reserves for process memory.
    NotEnoughMemory,

    /// A process was loaded with a length in flash that the MPU does not
    /// support. The fix is probably to correct the process size, but this could
    /// also be caused by a bad MPU implementation.
    MpuInvalidFlashLength,

    /// A process specified a fixed memory address that it needs its memory
    /// range to start at, and the kernel did not or could not give the process
    /// a memory region starting at that address.
    MemoryAddressMismatch {
        actual_address: u32,
        expected_address: u32,
    },

    /// A process specified that its binary must start at a particular address,
    /// and that is not the address the binary is actually placed at.
    IncorrectFlashAddress {
        actual_address: u32,
        expected_address: u32,
    },

    /// A process requires a newer version of the kernel or did not specify
    /// a required version. Processes can include the KernelVersion TBF header stating
    /// their compatible kernel version (^major.minor).
    ///
    /// Boards may not require processes to include the KernelVersion TBF header, and
    /// the kernel supports ignoring a missing KernelVersion TBF header. In that case,
    /// this error will not be returned for a process missing a KernelVersion TBF
    /// header.
    ///
    /// `version` is the `(major, minor)` kernel version the process indicates it
    /// requires. If `version` is `None` then the process did not include the
    /// KernelVersion TBF header.
    IncompatibleKernelVersion { version: Option<(u16, u16)> },

    /// Process loading error due (likely) to a bug in the kernel. If you get
    /// this error please open a bug report.
    InternalError,
}

impl From<ProcessLoadError> for ErrorCode {
    fn from(er: ProcessLoadError) -> Self {
        match er {
            ProcessLoadError::NotEnoughMemory => ErrorCode::NOMEM,
            ProcessLoadError::IncorrectFlashAddress { .. }
            | ProcessLoadError::MemoryAddressMismatch { .. }
            | ProcessLoadError::MpuInvalidFlashLength
            | ProcessLoadError::NotEnoughFlash
            | ProcessLoadError::TbfHeaderParseFailure(_) => ErrorCode::INVAL,
            ProcessLoadError::IncompatibleKernelVersion { .. } => ErrorCode::NOSUPPORT,
            ProcessLoadError::InternalError => ErrorCode::FAIL,
        }
    }
}

impl From<tock_tbf::types::TbfParseError> for ProcessLoadError {
    /// Convert between a TBF Header parse error and a process load error.
    ///
    /// We note that the process load error is because a TBF header failed to
    /// parse, and just pass through the parse error.
    fn from(error: tock_tbf::types::TbfParseError) -> Self {
        ProcessLoadError::TbfHeaderParseFailure(error)
    }
}

impl fmt::Debug for ProcessLoadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProcessLoadError::TbfHeaderParseFailure(tbf_parse_error) => {
                write!(f, "Error parsing TBF header\n")?;
                write!(f, "{:?}", tbf_parse_error)
            }

            ProcessLoadError::NotEnoughFlash => {
                write!(f, "Not enough flash available for app linked list")
            }

            ProcessLoadError::NotEnoughMemory => {
                write!(f, "Not able to meet memory requirements requested by apps")
            }

            ProcessLoadError::MpuInvalidFlashLength => {
                write!(f, "App flash length not supported by MPU")
            }

            ProcessLoadError::MemoryAddressMismatch {
                actual_address,
                expected_address,
            } => write!(
                f,
                "App memory does not match requested address Actual:{:#x}, Expected:{:#x}",
                actual_address, expected_address
            ),

            ProcessLoadError::IncorrectFlashAddress {
                actual_address,
                expected_address,
            } => write!(
                f,
                "App flash does not match requested address. Actual:{:#x}, Expected:{:#x}",
                actual_address, expected_address
            ),

            ProcessLoadError::IncompatibleKernelVersion { version } => match version {
                Some((major, minor)) => write!(
                    f,
                    "Process is incompatible with the kernel. Running: {}.{}, Requested: {}.{}",
                    crate::KERNEL_MAJOR_VERSION,
                    crate::KERNEL_MINOR_VERSION,
                    major,
                    minor
                ),
                None => write!(f, "Process did not provide a TBF kernel version header"),
            },

            ProcessLoadError::InternalError => write!(f, "Error in kernel. Likely a bug."),
        }
    }
}

/// Helper function to load processes from flash into an array of active
/// processes. This is the default template for loading processes, but a board
/// is able to create its own `load_processes()` function and use that instead.
///
/// Processes are found in flash starting from the given address and iterating
/// through Tock Binary Format (TBF) headers. Processes are given memory out of
/// the `app_memory` buffer until either the memory is exhausted or the
/// allocated number of processes are created. This buffer is a non-static slice,
/// ensuring that this code cannot hold onto the slice past the end of this function
/// (instead, processes store a pointer and length), which necessary for later
/// creation of `ProcessBuffer`s in this memory region to be sound.
/// A reference to each process is stored in the provided `procs` array.
/// How process faults are handled by the
/// kernel must be provided and is assigned to every created process.
///
/// This function is made `pub` so that board files can use it, but loading
/// processes from slices of flash an memory is fundamentally unsafe. Therefore,
/// we require the `ProcessManagementCapability` to call this function.
///
/// Returns `Ok()` if process discovery went as expected. Returns any remaining app_memory.
/// `ProcessLoadError` if something goes wrong during TBF parsing or process
/// creation.
#[inline(always)]
pub fn load_processes_advanced<C: Chip>(
    kernel: &'static Kernel,
    chip: &'static C,
    app_flash: &'static [u8],
    // must be static so caller cannot retain this
    app_memory: &'static mut [u8],
    fault_policy: &'static dyn ProcessFaultPolicy,
    require_kernel_version: bool,
    _capability: &dyn ProcessManagementCapability,
) -> Result<Option<&'static mut [u8]>, (ProcessLoadError, Option<&'static mut [u8]>)> {
    if config::CONFIG.debug_load_processes {
        debug!(
            "Loading processes from flash={:#010X}-{:#010X} into sram={:#010X}-{:#010X}",
            app_flash.as_ptr() as usize,
            app_flash.as_ptr() as usize + app_flash.len() - 1,
            app_memory.as_ptr() as usize,
            app_memory.as_ptr() as usize + app_memory.len() - 1
        );
    }

    let mut remaining_flash = app_flash;
    let mut remaining_memory = Some(app_memory);

    // Keep trying to load processes until there are no more.
    // We intentionally keep loading even if the process array is full so that we don't silently
    // forget to load processes.
    loop {
        let flash_before = remaining_flash;
        let loaded_any = try_load_process(
            kernel,
            chip,
            fault_policy,
            require_kernel_version,
            &mut remaining_flash,
            &mut remaining_memory,
            true,
            _capability,
        )
        .map_err(|er| (er, remaining_memory.take()))?;

        // Nothing more to load
        if !loaded_any && flash_before.as_ptr() == remaining_flash.as_ptr() {
            return Ok(remaining_memory.take());
        }
    }
}

/// Tries to load a single tbf located at remaining_flash into memory at remaining_memory.
/// Returns OK(true) if a process was loaded
/// Returns OK(false) if a process was not loaded but no fatal error was encountered
fn try_load_process<'a, 'b, C: Chip>(
    kernel: &'static Kernel,
    chip: &'static C,
    fault_policy: &'static dyn ProcessFaultPolicy,
    require_kernel_version: bool,
    remaining_flash_in: &mut &'b [u8],
    // NOT static so that process.rs cannot keep a reference (if ever its interface changes)
    // This cannot be public because remaining_memory needs to be static to the caller.
    remaining_memory: &mut Option<&'a mut [u8]>,
    flash_is_static: bool,
    _capability: &dyn ProcessManagementCapability,
) -> Result<bool, ProcessLoadError> {
    let remaining_flash = *remaining_flash_in;
    // Get the first eight bytes of flash to check if there is another
    // app.
    let test_header_slice = match remaining_flash.get(0..8) {
        Some(s) => s,
        None => {
            // Not enough flash to test for another app. This just means
            // we are at the end of flash, and there are no more apps to
            // load.
            return Ok(false);
        }
    };

    // Pass the first eight bytes to tbfheader to parse out the length of
    // the tbf header and app. We then use those values to see if we have
    // enough flash remaining to parse the remainder of the header.
    let (version, header_length, entry_length) = match tock_tbf::parse::parse_tbf_header_lengths(
        test_header_slice
            .try_into()
            .or(Err(ProcessLoadError::InternalError))?,
    ) {
        Ok((v, hl, el)) => (v, hl, el),
        Err(tock_tbf::types::InitialTbfParseError::InvalidHeader(entry_length)) => {
            // If we could not parse the header, then we want to skip over
            // this app and look for the next one.
            (0, 0, entry_length)
        }
        Err(tock_tbf::types::InitialTbfParseError::UnableToParse) => {
            // Since Tock apps use a linked list, it is very possible the
            // header we started to parse is intentionally invalid to signal
            // the end of apps. This is ok and just means we have finished
            // loading apps.
            return Ok(false);
        }
    };

    // Now we can get a slice which only encompasses the length of flash
    // described by this tbf header.  We will either parse this as an actual
    // app, or skip over this region.
    let entry_flash = remaining_flash
        .get(0..entry_length as usize)
        .ok_or(ProcessLoadError::NotEnoughFlash)?;

    // Advance the flash slice for process discovery beyond this last entry.
    // This will be the start of where we look for a new process since Tock
    // processes are allocated back-to-back in flash.
    *remaining_flash_in = remaining_flash
        .get(entry_flash.len()..)
        .ok_or(ProcessLoadError::NotEnoughFlash)?;

    if header_length > 0 {
        let index = kernel.get_next_free_proc_entry()?;
        // If we found an actual app header, try to create a `Process`
        // object. We also need to shrink the amount of remaining memory
        // based on whatever is assigned to the new process if one is
        // created.

        // Try to create a process object from that app slice. If we don't
        // get a process and we didn't get a loading error (aka we got to
        // this point), then the app is a disabled process or just padding.
        let process_option = unsafe {
            ProcessStandard::create(
                kernel,
                chip,
                entry_flash,
                header_length as usize,
                version,
                remaining_memory,
                fault_policy,
                require_kernel_version,
                index,
                flash_is_static,
            )?
        };
        // Need to reassign remaining_memory in every iteration so the compiler
        // knows it will not be re-borrowed.
        process_option.map(|process| {
            if config::CONFIG.debug_load_processes {
                let addresses = process.get_addresses();
                debug!(
                        "Loaded process[{}] from flash={:#010X}-{:#010X} into sram={:#010X}-{:#010X} = {:?}",
                        index,
                        entry_flash.as_ptr() as usize,
                        entry_flash.as_ptr() as usize + entry_flash.len() - 1,
                        addresses.sram_start,
                        addresses.sram_end - 1,
                        process.get_process_name()
                    );
            }

            let _ = kernel.set_next_proc_entry_used(process);

            chip.mpu().new_process(process.processid());
        });
        return Ok(true);
    }

    // We are just skipping over this region of flash, so we have the
    // same amount of process memory to allocate from.
    Ok(false)
}

/// Public version of try_load_process that ensures remaining_memory is static.
pub fn try_load_process_pub<'b, C: Chip>(
    kernel: &'static Kernel,
    chip: &'static C,
    fault_policy: &'static dyn ProcessFaultPolicy,
    require_kernel_version: bool,
    flash: &mut &'b [u8],
    remaining_memory: &mut Option<&'static mut [u8]>,
    _capability: &dyn ProcessManagementCapability,
) -> Result<bool, ProcessLoadError> {
    try_load_process(
        kernel,
        chip,
        fault_policy,
        require_kernel_version,
        flash,
        remaining_memory,
        false,
        _capability,
    )
}

/// This is a wrapper function for `load_processes_advanced` that uses
/// the default arguments that mainstream boards should provide.
///
/// Default arguments are:
///  - `require_kernel_version`: prevent loading processes that do not provide a `KernelVersion`
#[inline(always)]
pub fn load_processes<C: Chip>(
    kernel: &'static Kernel,
    chip: &'static C,
    app_flash: &'static [u8],
    // this must be static because the caller should not be able to simply borrow the buffer and then
    // use it again afterwards. App memory will eventually come back to the kernel via the allow
    // mechanism.
    app_memory: &'static mut [u8],
    fault_policy: &'static dyn ProcessFaultPolicy,
    capability: &dyn ProcessManagementCapability,
) -> Result<(), ProcessLoadError> {
    match load_processes_advanced(
        kernel,
        chip,
        app_flash,
        app_memory,
        fault_policy,
        true,
        capability,
    ) {
        Ok(_) => Ok(()),
        Err((er, _)) => Err(er),
    }
}

/// Return (flash, ram)
/// Must call this only once as the ram is mut.
pub unsafe fn get_mems() -> (&'static [u8], &'static mut [u8]) {
    #[cfg(target_os = "none")]
    {
        // These symbols are defined in the linker script.
        extern "C" {
            /// Beginning of the ROM region containing app images.
            static _sapps: u8;
            /// End of the ROM region containing app images.
            static _eapps: u8;
            /// Beginning of the RAM region for app memory.
            static mut _sappmem: u8;
            /// End of the RAM region for app memory.
            static _eappmem: u8;
        }
        (
            core::slice::from_raw_parts(
                &_sapps as *const u8,
                &_eapps as *const u8 as usize - &_sapps as *const u8 as usize,
            ),
            core::slice::from_raw_parts_mut(
                &mut _sappmem as *mut u8,
                &_eappmem as *const u8 as usize - &_sappmem as *const u8 as usize,
            ),
        )
    }

    #[cfg(not(target_os = "none"))]
    {
        (&[], &mut [])
    }
}
