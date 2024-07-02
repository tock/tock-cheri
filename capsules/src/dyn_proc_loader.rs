//! Dynamically loads processes from allowed buffers
//!
//! Setup
//! -----
//!
//! ```
//! // Create the loader
//! let loader = capsules::dyn_proc_loader::ProcLoader::new(
//!             board_kernel.create_grant(
//!                 capsules::dyn_proc_loader::DRIVER_NUM,
//!                 &memory_allocation_cap,
//!             ),
//!             board_kernel,
//!             chip,
//!             &FAULT_RESPONSE,
//!             &process_mgmt_cap,
//! );
//! // Then load your initial processes, keeping the returned memory
//! let mem = kernel::process::load_processes_advanced(
//!     board_kernel,
//!     chip,
//!     flash,
//!     mem,
//!     &FAULT_RESPONSE,
//!     true,
//!     &process_mgmt_cap,
//!  )?;
//!
//! // Then pass to the loader
//!
//! loader.provide_mem(mem);
//! ```
//!
//! Note, this can only be used with contiguously loaded processes as otherwise they would try
//! execute from memory located inside the loader.
//!
//!
//! Usage (from userspace)
//! The general flow is as follows:
//!     User allows a single buffer (slot 0) containing a tbf
//!     User registers a callback
//!     User calls command 1 to load the process
//!     User waits for callback
//!     Capsule loads process
//!     Capsule notifies user via callback
//!     User can un-allow callback and buffer (if desired)

use crate::driver;
use core::cell::Cell;
use core::ops::Deref;
use kernel::capabilities::ProcessManagementCapability;
use kernel::grant::{AllowRoCount, AllowRwCount, Grant, UpcallCount};
use kernel::platform::chip::Chip;
use kernel::process::{try_load_process_pub, Error, ProcessFaultPolicy};
use kernel::syscall::{CommandReturn, CommandReturnResult, SyscallDriver};
use kernel::{very_simple_component, ErrorCode, Kernel, ProcessId};

pub const DRIVER_NUM: usize = driver::NUM::ProcLoader as usize;

type GrantT = Grant<(), UpcallCount<1>, AllowRoCount<1>, AllowRwCount<1>>;

pub struct ProcLoader<'a, C: Chip + 'static, const CHECK_VERSION: bool> {
    grant: GrantT,
    kernel: &'static Kernel,
    chip: &'static C,
    mem: Cell<Option<&'static mut [u8]>>,
    fault_policy: &'static dyn ProcessFaultPolicy,
    capability: &'a dyn ProcessManagementCapability,
}

very_simple_component!(impl<{C : Chip + 'static, const CHECK_VERSION : bool}> for ProcLoader::<'static, C, CHECK_VERSION>,
    new(GrantT, &'static Kernel, &'static C, &'static dyn ProcessFaultPolicy, &'static dyn ProcessManagementCapability)
);

impl<'a, C: Chip + 'static, const CHECK_VERSION: bool> ProcLoader<'a, C, CHECK_VERSION> {
    pub const fn new(
        grant: GrantT,
        kernel: &'static Kernel,
        chip: &'static C,
        fault_policy: &'static dyn ProcessFaultPolicy,
        capability: &'a dyn ProcessManagementCapability,
    ) -> Self {
        Self {
            grant,
            kernel,
            chip,
            mem: Cell::new(None),
            fault_policy,
            capability,
        }
    }

    /// Provide remaining unallocated memory to the loader.
    /// Not a part of new as this happens relatively late.
    pub fn provide_mem(&self, free_memory: Option<&'static mut [u8]>) {
        self.mem.set(free_memory)
    }

    /// ### `command_num`
    ///  - `0` Driver check, return OK()
    ///  - `1` Load process
    fn handle_command(
        &self,
        command_number: usize,
        _arg2: usize,
        _arg3: usize,
        appid: ProcessId,
    ) -> CommandReturnResult {
        match command_number {
            0 => Ok(CommandReturn::success()),
            1 => {
                let proc_grant = self.grant.get_for(appid)?;
                let kern_data = proc_grant.get_kern_data();
                let tbf = kern_data.get_readonly_aref(0)?.as_noclone();

                // Fail early
                if kern_data.could_schedule_upcall(0).is_err() {
                    return Err(ErrorCode::BUSY);
                }

                // Current process loading is really synchronous, but we still adopt the async
                // model in case it ever changes
                // SAFETY: we only use this temporarily to load the process.
                // Still, we should still refactor.
                let mut flash = tbf.deref().to_byte_slice();
                let mut mem = self.mem.take();
                let load_result = try_load_process_pub::<C>(
                    self.kernel,
                    self.chip,
                    self.fault_policy,
                    CHECK_VERSION,
                    &mut flash,
                    &mut mem,
                    self.capability,
                );
                self.mem.set(mem);
                // Handle errors
                load_result?;

                // Otherwise the process should now be loaded, create the upcall
                kern_data.schedule_upcall(0, (0, 0, 0)).unwrap();

                // Return success
                Ok(CommandReturn::success())
            }
            _ => Err(ErrorCode::NOSUPPORT),
        }
    }
}

impl<'a, C: Chip + 'static, const CHECK_VERSION: bool> SyscallDriver
    for ProcLoader<'a, C, CHECK_VERSION>
{
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
