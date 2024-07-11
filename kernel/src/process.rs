//! Types for Tock-compatible processes.

use core::cell::Cell;
use core::fmt;
use core::fmt::Write;
use core::ptr::NonNull;
use core::str;

use crate::capabilities;
use crate::cheri::cptr;
use crate::errorcode::ErrorCode;
use crate::ipc;
use crate::kernel::Kernel;
use crate::platform::mpu::{self};
use crate::processbuffer::{ReadOnlyProcessBuffer, ReadWriteProcessBuffer};
use crate::storage_permissions;
use crate::syscall::{self, Syscall, SyscallReturn};
use crate::upcall::UpcallId;
use tock_tbf::types::CommandPermissions;

// Export all process related types via `kernel::process::`.
pub use crate::process_policies::{
    PanicFaultPolicy, ProcessFaultPolicy, RestartFaultPolicy, StopFaultPolicy,
    StopWithDebugFaultPolicy, ThresholdRestartFaultPolicy, ThresholdRestartThenPanicFaultPolicy,
};
pub use crate::process_printer::{ProcessPrinter, ProcessPrinterContext, ProcessPrinterText};
pub use crate::process_standard::ProcessStandard;
pub use crate::process_utilities::{
    get_mems, load_processes, load_processes_advanced, try_load_process_pub, ProcessLoadError,
};

/// Userspace process identifier.
///
/// This should be treated as an opaque type that can be used to represent a
/// process on the board without requiring an actual reference to a `Process`
/// object. Having this `ProcessId` reference type is useful for managing
/// ownership and type issues in Rust, but more importantly `ProcessId` serves
/// as a tool for capsules to hold pointers to applications.
///
/// Since `ProcessId` implements `Copy`, having an `ProcessId` does _not_ ensure
/// that the process the `ProcessId` refers to is still valid. The process may
/// have been removed, terminated, or restarted as a new process. Therefore, all
/// uses of `ProcessId` in the kernel must check that the `ProcessId` is still
/// valid. This check happens automatically when `.index()` is called, as noted
/// by the return type: `Option<usize>`. `.index()` will return the index of the
/// process in the processes array, but if the process no longer exists then
/// `None` is returned.
///
/// Outside of the kernel crate, holders of an `ProcessId` may want to use
/// `.id()` to retrieve a simple identifier for the process that can be
/// communicated over a UART bus or syscall interface. This call is guaranteed
/// to return a suitable identifier for the `ProcessId`, but does not check that
/// the corresponding application still exists.
///
/// This type also provides capsules an interface for interacting with processes
/// since they otherwise would have no reference to a `Process`. Very limited
/// operations are available through this interface since capsules should not
/// need to know the details of any given process. However, certain information
/// makes certain capsules possible to implement. For example, capsules can use
/// the `get_editable_flash_range()` function so they can safely allow an app to
/// modify its own flash.
#[derive(Clone, Copy)]
pub struct ProcessId {
    /// Reference to the main kernel struct. This is needed for checking on
    /// certain properties of the referred app (like its editable bounds), but
    /// also for checking that the index is valid.
    pub(crate) kernel: &'static Kernel,

    /// The index in the kernel.PROCESSES[] array where this app's state is
    /// stored. This makes for fast lookup of the process and helps with
    /// implementing IPC.
    ///
    /// This value is crate visible to enable optimizations in sched.rs. Other
    /// users should call `.index()` instead.
    pub(crate) index: usize,

    /// The unique identifier for this process. This can be used to refer to the
    /// process in situations where a single number is required, for instance
    /// when referring to specific applications across the syscall interface.
    ///
    /// The combination of (index, identifier) is used to check if the app this
    /// `ProcessId` refers to is still valid. If the stored identifier in the
    /// process at the given index does not match the value saved here, then the
    /// process moved or otherwise ended, and this `ProcessId` is no longer
    /// valid.
    identifier: usize,
}

impl PartialEq for ProcessId {
    fn eq(&self, other: &ProcessId) -> bool {
        self.identifier == other.identifier
    }
}

impl Eq for ProcessId {}

impl fmt::Debug for ProcessId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.identifier)
    }
}

impl ProcessId {
    /// Create a new `ProcessId` object based on the app identifier and its
    /// index in the processes array.
    pub(crate) fn new(kernel: &'static Kernel, identifier: usize, index: usize) -> ProcessId {
        ProcessId {
            kernel: kernel,
            identifier: identifier,
            index: index,
        }
    }

    /// Create a new `ProcessId` object based on the app identifier and its
    /// index in the processes array.
    ///
    /// This constructor is public but protected with a capability so that
    /// external implementations of `Process` can use it.
    pub fn new_external(
        kernel: &'static Kernel,
        identifier: usize,
        index: usize,
        _capability: &dyn capabilities::ExternalProcessCapability,
    ) -> ProcessId {
        ProcessId {
            kernel: kernel,
            identifier: identifier,
            index: index,
        }
    }

    /// Get the location of this app in the processes array.
    ///
    /// This will return `Some(index)` if the identifier stored in this
    /// `ProcessId` matches the app saved at the known index. If the identifier
    /// does not match then `None` will be returned.
    pub(crate) fn index(&self) -> Option<usize> {
        // Do a lookup to make sure that the index we have is correct.
        if self.kernel.processid_is_valid(self) {
            Some(self.index)
        } else {
            None
        }
    }

    /// Get a `usize` unique identifier for the app this `ProcessId` refers to.
    ///
    /// This function should not generally be used, instead code should just use
    /// the `ProcessId` object itself to refer to various apps on the system.
    /// However, getting just a `usize` identifier is particularly useful when
    /// referring to a specific app with things outside of the kernel, say for
    /// userspace (e.g. IPC) or tockloader (e.g. for debugging) where a concrete
    /// number is required.
    ///
    /// Note, this will always return the saved unique identifier for the app
    /// originally referred to, even if that app no longer exists. For example,
    /// the app may have restarted, or may have been ended or removed by the
    /// kernel. Therefore, calling `id()` is _not_ a valid way to check
    /// that an application still exists.
    pub fn id(&self) -> usize {
        self.identifier
    }

    /// Returns the full address of the start and end of the flash region that
    /// the app owns and can write to. This includes the app's code and data and
    /// any padding at the end of the app. It does not include the TBF header,
    /// or any space that the kernel is using for any potential bookkeeping.
    pub fn get_editable_flash_range(&self) -> (usize, usize) {
        self.kernel.process_map_or((0, 0), *self, |process| {
            let addresses = process.get_addresses();
            (addresses.flash_non_protected_start, addresses.flash_end)
        })
    }

    /// Get the storage permissions for the process. These permissions indicate
    /// what the process is allowed to read and write. Returns `None` if the
    /// process has no storage permissions.
    pub fn get_storage_permissions(&self) -> Option<storage_permissions::StoragePermissions> {
        self.kernel
            .process_map_or(None, *self, |process| process.get_storage_permissions())
    }
}

/// This trait represents a generic process that the Tock scheduler can
/// schedule.
pub trait Process {
    /// Returns the process's identifier.
    fn processid(&self) -> ProcessId;

    /// Queue a `Task` for the process. This will be added to a per-process
    /// buffer and executed by the scheduler. `Task`s are some function the app
    /// should run, for example a upcall or an IPC call.
    ///
    /// This function returns `Ok(())` if the `Task` was successfully
    /// enqueued. If the process is no longer alive,
    /// `Err(ErrorCode::NODEVICE)` is returned. If the task could not
    /// be enqueued because there is insufficient space in the
    /// internal task queue, `Err(ErrorCode::NOMEM)` is
    /// returned. Other return values must be treated as
    /// kernel-internal errors.
    fn enqueue_task(&self, task: Task) -> Result<(), ErrorCode>;

    /// Performs the checks for enqueue_task and returns errors in the same cases,
    /// or otherwise does nothing and returns unit.
    fn could_enqueue_task(&self) -> Result<(), ErrorCode>;

    /// Returns whether this process is ready to execute.
    fn ready(&self) -> bool;

    /// Return if there are any Tasks (upcalls/IPC requests) enqueued
    /// for the process.
    fn has_tasks(&self) -> bool;

    /// Remove the scheduled operation from the front of the queue and return it
    /// to be handled by the scheduler.
    ///
    /// If there are no `Task`s in the queue for this process this will return
    /// `None`.
    fn dequeue_task(&self) -> Option<Task>;

    /// Returns the number of pending tasks. If 0 then `dequeue_task()` will
    /// return `None` when called.
    fn pending_tasks(&self) -> usize;

    /// Remove all scheduled upcalls for a given upcall id from the task
    /// queue.
    fn remove_pending_upcalls(&self, upcall_id: UpcallId);

    /// Returns the current state the process is in. Common states are "running"
    /// or "yielded".
    fn get_state(&self) -> State;

    /// Move this process from the running state to the yielded state.
    ///
    /// This will fail (i.e. not do anything) if the process was not previously
    /// running.
    fn set_yielded_state(&self);

    /// Move this process from running or yielded state into the stopped state.
    ///
    /// This will fail (i.e. not do anything) if the process was not either
    /// running or yielded.
    fn stop(&self);

    /// Move this stopped process back into its original state.
    ///
    /// This transitions a process from `StoppedRunning` -> `Running` or
    /// `StoppedYielded` -> `Yielded`.
    fn resume(&self);

    /// Put this process in the fault state. This will trigger the
    /// `FaultResponse` for this process to occur.
    fn set_fault_state(&self);

    /// Returns how many times this process has been restarted.
    fn get_restart_count(&self) -> usize;

    /// Get the name of the process. Used for IPC.
    fn get_process_name(&self) -> &str;

    /// Get the completion code if the process has previously terminated.
    ///
    /// If the process has never terminated then there has been no opportunity
    /// for a completion code to be set, and this will return `None`.
    ///
    /// If the process has previously terminated this will return `Some()`. If
    /// the last time the process terminated it did not provide a completion
    /// code (e.g. the process faulted), then this will return `Some(None)`. If
    /// the last time the process terminated it did provide a completion code,
    /// this will return `Some(Some(completion_code))`.
    fn get_completion_code(&self) -> Option<Option<u32>>;

    /// Try and reclaim all grant memory.
    /// This can fail because there still exist grant references within the kernel.
    /// The eventual plan is to try restart after some interval (to allow hardware to finish
    /// with references naturally).
    /// For now, panic is fine if this fails.
    fn try_release_grants(&self) -> Result<(), ()>;

    /// Stop and clear a process's state, putting it into the `Terminated`
    /// state.
    ///
    /// This will end the process, but does not reset it such that it could be
    /// restarted and run again. This function instead frees grants and any
    /// queued tasks for this process, but leaves the debug information about
    /// the process and other state intact.
    ///
    /// When a process is terminated, an optional `completion_code` should be
    /// stored for the process. If the process provided the completion code
    /// (e.g. via the exit syscall), then this function should be called with
    /// a completion code of `Some(u32)`. If the kernel is terminating the
    /// process and therefore has no completion code from the process, it should
    /// provide `None`.
    fn terminate(&self, completion_code: Option<u32>);

    /// Terminates and attempts to restart the process. The process and current
    /// application always terminate. The kernel may, based on its own policy,
    /// restart the application using the same process, reuse the process for
    /// another application, or simply terminate the process and application.
    ///
    /// This function can be called when the process is in any state. It
    /// attempts to reset all process state and re-initialize it so that it can
    /// be reused.
    ///
    /// Restarting an application can fail for two general reasons:
    ///
    /// 1. The kernel chooses not to restart the application, based on its
    ///    policy.
    ///
    /// 2. The kernel decides to restart the application but fails to do so
    ///    because Some state can no long be configured for the process. For
    ///    example, the syscall state for the process fails to initialize.
    ///
    /// After `restart()` runs the process will either be queued to run its the
    /// application's `_start` function, terminated, or queued to run a
    /// different application's `_start` function.
    ///
    /// As the process will be terminated before being restarted, this function
    /// accepts an optional `completion_code`. If the process provided a
    /// completion code (e.g. via the exit syscall), then this should be called
    /// with `Some(u32)`. If the kernel is trying to restart the process and the
    /// process did not provide a completion code, then this should be called
    /// with `None`.
    fn try_restart(&self, completion_code: Option<u32>);

    // memop operations

    /// Change the location of the program break and reallocate the MPU region
    /// covering program memory.
    ///
    /// This will fail with an error if the process is no longer active. An
    /// inactive process will not run again without being reset, and changing
    /// the memory pointers is not valid at this point.
    fn brk(&self, new_break: *const u8) -> Result<cptr, Error>;

    /// Change the location of the program break, reallocate the MPU region
    /// covering program memory, and return the previous break address.
    ///
    /// This will fail with an error if the process is no longer active. An
    /// inactive process will not run again without being reset, and changing
    /// the memory pointers is not valid at this point.
    fn sbrk(&self, increment: isize) -> Result<cptr, Error>;

    /// How many writeable flash regions defined in the TBF header for this
    /// process.
    fn number_writeable_flash_regions(&self) -> usize;

    /// Get the offset from the beginning of flash and the size of the defined
    /// writeable flash region.
    fn get_writeable_flash_region(&self, region_index: usize) -> (usize, usize);

    /// Debug function to update the kernel on where the stack starts for this
    /// process. Processes are not required to call this through the memop
    /// system call, but it aids in debugging the process.
    fn update_stack_start_pointer(&self, stack_pointer: *const u8);

    /// Debug function to update the kernel on where the process heap starts.
    /// Also optional.
    fn update_heap_start_pointer(&self, heap_pointer: *const u8);

    /// Creates a [`ReadWriteProcessBuffer`] from the given offset and size in
    /// process memory.
    ///
    /// ## Returns
    ///
    /// In case of success, this method returns the created
    /// [`ReadWriteProcessBuffer`].
    ///
    /// In case of an error, an appropriate ErrorCode is returned:
    ///
    /// - If the memory is not contained in the process-accessible memory space
    ///   / `buf_start_addr` and `size` are not a valid read-write buffer (any
    ///   byte in the range is not read/write accessible to the process),
    ///   [`ErrorCode::INVAL`].
    /// - If the process is not active: [`ErrorCode::FAIL`].
    /// - For all other errors: [`ErrorCode::FAIL`].
    fn build_readwrite_process_buffer(
        &self,
        buf_start_addr: *mut u8,
        size: usize,
    ) -> Result<ReadWriteProcessBuffer, ErrorCode>;

    /// Creates a [`ReadOnlyProcessBuffer`] from the given offset and size in
    /// process memory.
    ///
    /// ## Returns
    ///
    /// In case of success, this method returns the created
    /// [`ReadOnlyProcessBuffer`].
    ///
    /// In case of an error, an appropriate ErrorCode is returned:
    ///
    /// - If the memory is not contained in the process-accessible memory space
    ///   / `buf_start_addr` and `size` are not a valid read-only buffer (any
    ///   byte in the range is not read-accessible to the process),
    ///   [`ErrorCode::INVAL`].
    /// - If the process is not active: [`ErrorCode::FAIL`].
    /// - For all other errors: [`ErrorCode::FAIL`].
    fn build_readonly_process_buffer(
        &self,
        buf_start_addr: *const u8,
        size: usize,
    ) -> Result<ReadOnlyProcessBuffer, ErrorCode>;

    /// Set a single byte within the process address space at `addr` to `value`.
    /// Return true if `addr` is within the RAM bounds currently exposed to the
    /// process (thereby writable by the process itself) and the value was set,
    /// false otherwise.
    ///
    /// ### Safety
    ///
    /// This function verifies that the byte to be written is in the process's
    /// accessible memory. However, to avoid undefined behavior the caller needs
    /// to ensure that no other references exist to the process's memory before
    /// calling this function.
    unsafe fn set_byte(&self, addr: *mut u8, value: u8) -> bool;

    /// Return the permissions for this process for a given `driver_num`.
    ///
    /// The returned `CommandPermissions` will indicate if any permissions for
    /// individual command numbers are specified. If there are permissions set
    /// they are returned as a 64 bit bitmask for sequential command numbers.
    /// The offset indicates the multiple of 64 command numbers to get permissions for.
    fn get_command_permissions(&self, driver_num: usize, offset: usize) -> CommandPermissions;

    /// Get the storage permissions for the process.
    ///
    /// Returns `None` if the process has no storage permissions.
    fn get_storage_permissions(&self) -> Option<storage_permissions::StoragePermissions>;

    // mpu

    /// Configure the MPU to use the process's allocated regions.
    ///
    /// It is not valid to call this function when the process is inactive (i.e.
    /// the process will not run again).
    fn setup_mpu(&self);

    /// Disable MMU configuration specific to this process.
    fn disable_mmu(&self);

    /// Allocate a new MPU region for the process that is at least
    /// `min_region_size` bytes and lies within the specified stretch of
    /// unallocated memory.
    ///
    /// It is not valid to call this function when the process is inactive (i.e.
    /// the process will not run again).
    fn add_mpu_region(
        &self,
        unallocated_memory_start: *const u8,
        unallocated_memory_size: usize,
        min_region_size: usize,
    ) -> Option<mpu::Region>;

    /// Align a region so that the MPU could enforce it
    /// FIXME: I hate that this is in process, but ProcessStandard seems to be the only thing
    /// that knows about the type of the MPU. Really, Kernel should be parameterised in the
    /// Chip, rather than its individual methods, so the type does not get lost.
    /// b/280426926
    fn align_mpu_region(&self, base: usize, length: usize) -> (usize, usize);

    /// Removes an MPU region from the process that has been previouly added with
    /// `add_mpu_region`.
    ///
    /// It is not valid to call this function when the process is inactive (i.e.
    /// the process will not run again).
    fn remove_mpu_region(&self, region: mpu::Region) -> Result<mpu::RemoveRegionResult, ErrorCode>;

    /// Actually revoke regions previously requested with remove_memory_region
    /// Safety: no LiveARef or LivePRef may exist to any memory that might be revoked,
    /// Nor may any grants be entered via the legacy mechanism if allowed memory might be revoked.
    unsafe fn revoke_regions(&self) -> Result<(), ErrorCode>;

    // grants

    /// Allocate memory from the grant region and store the reference in the
    /// proper grant pointer index.
    ///
    /// This function must check that doing the allocation does not cause
    /// the kernel memory break to go below the top of the process accessible
    /// memory region allowed by the MPU. Note, this can be different from the
    /// actual app_brk, as MPU alignment and size constraints may result in the
    /// MPU enforced region differing from the app_brk.
    ///
    /// This will return `None` and fail if:
    /// - The process is inactive, or
    /// - There is not enough available memory to do the allocation, or
    /// - The grant_num is invalid, or
    /// - The grant_num already has an allocated grant.
    fn allocate_grant(
        &self,
        grant_num: usize,
        driver_num: usize,
        size: usize,
        align: usize,
    ) -> Option<NonNull<u8>>;

    /// Allocate memory from the grant region that is `size` bytes long and
    /// aligned to `align` bytes. This is used for creating custom grants which
    /// are not recorded in the grant pointer array, but are useful for capsules
    /// which need additional process-specific dynamically allocated memory.
    ///
    /// If successful, return a Some() with an identifier that can be used with
    /// `enter_custom_grant()` to get access to the memory and the pointer to
    /// the memory which must be used to initialize the memory.
    fn allocate_custom_grant(
        &self,
        size: usize,
        align: usize,
    ) -> Option<(ProcessCustomGrantIdentifier, NonNull<u8>)>;

    /// Get the grant based on `grant_num` for this process, getting access
    /// to the actual memory for the object stored as the grant.
    ///
    /// This will return an `Err` if the process is inactive of the `grant_num`
    /// is invalid, if the grant has not been allocated.
    /// If this returns `Ok()` then the pointer points to the
    /// previously allocated memory for this grant, or NULL.
    fn get_grant_mem(&self, grant_num: usize) -> Result<Option<NonNull<u8>>, Error>;

    /// Enter a custom grant based on the `identifier`.
    ///
    /// This retrieves a pointer to the previously allocated custom grant based
    /// on the identifier returned when the custom grant was allocated.
    ///
    /// This returns an error if the custom grant is no longer accessible, or
    /// if the process is inactive.
    fn enter_custom_grant(
        &self,
        identifier: ProcessCustomGrantIdentifier,
    ) -> Result<*mut u8, Error>;

    /// Return the count of the number of allocated grant pointers if the
    /// process is active. This does not count custom grants. This is used
    /// to determine if a new grant has been allocated after a call to
    /// `SyscallDriver::allocate_grant()`.
    ///
    /// Useful for debugging/inspecting the system.
    fn grant_allocated_count(&self) -> Option<usize>;

    /// Get the grant number (grant_num) associated with a given driver number
    /// if there is a grant associated with that driver_num.
    fn lookup_grant_from_driver_num(&self, driver_num: usize) -> Result<usize, Error>;

    // subscribe

    /// Verify that an Upcall function pointer is within process-accessible
    /// memory.
    ///
    /// Returns `true` if the upcall function pointer is valid for this process,
    /// and `false` otherwise.
    fn is_valid_upcall_function_pointer(&self, upcall_fn: *const u8) -> bool;

    // functions for processes that are architecture specific

    /// Get extra arguments for commands. The value returned is indeterminate if
    /// this is not called in the context of a driver handling a command.
    fn get_extra_syscall_arg(&self, ndx: usize) -> Option<usize>;

    /// Set the return value the process should see when it begins executing
    /// again after the syscall.
    ///
    /// It is not valid to call this function when the process is inactive (i.e.
    /// the process will not run again).
    ///
    /// This can fail, if the UKB implementation cannot correctly set the return
    /// value. An example of how this might occur:
    ///
    /// 1. The UKB implementation uses the process's stack to transfer values
    ///    between kernelspace and userspace.
    /// 2. The process calls memop.brk and reduces its accessible memory region
    ///    below its current stack.
    /// 3. The UKB implementation can no longer set the return value on the
    ///    stack since the process no longer has access to its stack.
    ///
    /// If it fails, the process will be put into the faulted state.
    fn set_syscall_return_value(&self, return_value: SyscallReturn);

    /// Set the function that is to be executed when the process is resumed.
    ///
    /// It is not valid to call this function when the process is inactive (i.e.
    /// the process will not run again).
    fn set_process_function(&self, callback: FunctionCall);

    /// Context switch to a specific process.
    ///
    /// This will return `None` if the process is inactive and cannot be
    /// switched to.
    fn switch_to(&self) -> Option<syscall::ContextSwitchReason>;

    /// Return process state information related to the location in memory
    /// of various process data structures.
    fn get_addresses(&self) -> ProcessAddresses;

    /// Return process state information related to the size in memory of
    /// various process data structures.
    fn get_sizes(&self) -> ProcessSizes;

    /// Write stored state as a binary blob into the `out` slice. Returns the number of bytes
    /// written to `out` on success.
    ///
    /// Returns `ErrorCode::SIZE` if `out` is too short to hold the stored state binary
    /// representation. Returns `ErrorCode::FAIL` on an internal error.
    fn get_stored_state(&self, out: &mut [u8]) -> Result<usize, ErrorCode>;

    /// Print out the full state of the process: its memory map, its
    /// context, and the state of the memory protection unit (MPU).
    fn print_full_process(&self, writer: &mut dyn Write);

    // debug

    /// Returns how many syscalls this app has called.
    fn debug_syscall_count(&self) -> usize;

    /// Returns how many upcalls for this process have been dropped.
    fn debug_dropped_upcall_count(&self) -> usize;

    /// Returns how many times this process has exceeded its timeslice.
    fn debug_timeslice_expiration_count(&self) -> usize;

    /// Increment the number of times the process has exceeded its timeslice.
    fn debug_timeslice_expired(&self);

    /// Increment the number of times the process called a syscall and record
    /// the last syscall that was called.
    fn debug_syscall_called(&self, last_syscall: Syscall);

    /// Return the last syscall the process called. Returns `None` if the
    /// process has not called any syscalls or the information is unknown.
    fn debug_syscall_last(&self) -> Option<Syscall>;
}

/// Opaque identifier for custom grants allocated dynamically from a process's
/// grant region.
///
/// This type allows Process to provide a handle to a custom grant within a
/// process's memory that `ProcessGrant` can use to access the custom grant
/// memory later.
///
/// We use this type rather than a direct pointer so that any attempt to access
/// can ensure the process still exists and is valid, and that the custom grant
/// has not been freed.
///
/// The fields of this struct are private so only Process can create this
/// identifier.
#[derive(Copy, Clone)]
pub struct ProcessCustomGrantIdentifier {
    pub(crate) offset: usize,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// The process has been removed and no longer exists. For example, the
    /// kernel could stop a process and re-claim its resources.
    NoSuchApp,
    /// The process does not have enough memory to complete the requested
    /// operation.
    OutOfMemory,
    /// The provided memory address is not accessible or not valid for the
    /// process.
    AddressOutOfBounds,
    /// The process is inactive (likely in a fault or exit state) and the
    /// attempted operation is therefore invalid.
    InactiveApp,
    /// This likely indicates a bug in the kernel and that some state is
    /// inconsistent in the kernel.
    KernelError,
    /// Indicates some process data, such as a Grant, is already borrowed.
    AlreadyInUse,
}

impl From<Error> for Result<(), ErrorCode> {
    fn from(err: Error) -> Result<(), ErrorCode> {
        match err {
            Error::OutOfMemory => Err(ErrorCode::NOMEM),
            Error::AddressOutOfBounds => Err(ErrorCode::INVAL),
            Error::NoSuchApp => Err(ErrorCode::INVAL),
            Error::InactiveApp => Err(ErrorCode::FAIL),
            Error::KernelError => Err(ErrorCode::FAIL),
            Error::AlreadyInUse => Err(ErrorCode::FAIL),
        }
    }
}

impl From<Error> for ErrorCode {
    fn from(err: Error) -> ErrorCode {
        match err {
            Error::OutOfMemory => ErrorCode::NOMEM,
            Error::AddressOutOfBounds => ErrorCode::INVAL,
            Error::NoSuchApp => ErrorCode::INVAL,
            Error::InactiveApp => ErrorCode::FAIL,
            Error::KernelError => ErrorCode::FAIL,
            Error::AlreadyInUse => ErrorCode::FAIL,
        }
    }
}

/// Various states a process can be in.
///
/// This is made public in case external implementations of `Process` want
/// to re-use these process states in the external implementation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum State {
    /// Process expects to be running code. The process may not be currently
    /// scheduled by the scheduler, but the process has work to do if it is
    /// scheduled.
    Running,

    /// Process stopped executing and returned to the kernel because it called
    /// the `yield` syscall. This likely means it is waiting for some event to
    /// occur, but it could also mean it has finished and doesn't need to be
    /// scheduled again.
    Yielded,

    /// The process is stopped, and its previous state was Running. This is used
    /// if the kernel forcibly stops a process when it is in the `Running`
    /// state. This state indicates to the kernel not to schedule the process,
    /// but if the process is to be resumed later it should be put back in the
    /// running state so it will execute correctly.
    StoppedRunning,

    /// The process is stopped, and it was stopped while it was yielded. If this
    /// process needs to be resumed it should be put back in the `Yield` state.
    StoppedYielded,

    /// The process faulted and cannot be run.
    Faulted,

    /// The process exited with the `exit-terminate` system call and cannot be
    /// run.
    Terminated,

    /// The process has never actually been executed. This of course happens
    /// when the board first boots and the kernel has not switched to any
    /// processes yet. It can also happen if an process is terminated and all of
    /// its state is reset as if it has not been executed yet.
    Unstarted,
}

/// A wrapper around `Cell<State>` is used by `Process` to prevent bugs arising
/// from the state duplication in the kernel work tracking and process state
/// tracking.
pub(crate) struct ProcessStateCell<'a> {
    state: Cell<State>,
    kernel: &'a Kernel,
}

impl<'a> ProcessStateCell<'a> {
    pub(crate) fn new(kernel: &'a Kernel) -> Self {
        Self {
            state: Cell::new(State::Unstarted),
            kernel,
        }
    }

    pub(crate) fn get(&self) -> State {
        self.state.get()
    }

    pub(crate) fn update(&self, new_state: State) {
        let old_state = self.state.get();

        if old_state == State::Running && new_state != State::Running {
            self.kernel.decrement_work();
        } else if new_state == State::Running && old_state != State::Running {
            self.kernel.increment_work()
        }
        self.state.set(new_state);
    }
}

/// The action the kernel should take when a process encounters a fault.
///
/// When an exception occurs during a process's execution (a common example is a
/// process trying to access memory outside of its allowed regions) the system
/// will trap back to the kernel, and the kernel has to decide what to do with
/// the process at that point.
///
/// The actions are separate from the policy on deciding which action to take. A
/// separate process-specific policy should determine which action to take.
#[derive(Copy, Clone)]
pub enum FaultAction {
    /// Generate a `panic!()` call and crash the entire system. This is useful
    /// for debugging applications as the error is displayed immediately after
    /// it occurs.
    Panic,

    /// Attempt to cleanup and restart the process which caused the fault. This
    /// resets the process's memory to how it was when the process was started
    /// and schedules the process to run again from its init function.
    Restart,

    /// Stop the process by no longer scheduling it to run.
    Stop,
}

/// Tasks that can be enqueued for a process.
///
/// This is public for external implementations of `Process`.
#[derive(Copy, Clone)]
pub enum Task {
    /// Function pointer in the process to execute. Generally this is a upcall
    /// from a capsule.
    FunctionCall(FunctionCall),
    /// An IPC operation that needs additional setup to configure memory access.
    IPC((ProcessId, ipc::IPCUpcallType)),
}

/// Enumeration to identify whether a function call for a process comes directly
/// from the kernel or from a upcall subscribed through a `Driver`
/// implementation.
///
/// An example of a kernel function is the application entry point.
#[derive(Copy, Clone, Debug)]
pub enum FunctionCallSource {
    /// For functions coming directly from the kernel, such as `init_fn`.
    Kernel,
    /// For functions coming from capsules or any implementation of `Driver`.
    Driver(UpcallId),
}

/// Struct that defines a upcall that can be passed to a process. The upcall
/// takes four arguments that are `Driver` and upcall specific, so they are
/// represented generically here.
///
/// Likely these four arguments will get passed as the first four register
/// values, but this is architecture-dependent.
///
/// A `FunctionCall` also identifies the upcall that scheduled it, if any, so
/// that it can be unscheduled when the process unsubscribes from this upcall.
#[derive(Copy, Clone, Debug)]
pub struct FunctionCall {
    pub source: FunctionCallSource,
    pub argument0: usize,
    pub argument1: usize,
    pub argument2: usize,
    pub argument3: cptr,
    pub pc: cptr,
}

/// Collection of process state information related to the memory addresses
/// of different elements of the process.
pub struct ProcessAddresses {
    /// The address of the beginning of the process's region in nonvolatile
    /// memory.
    pub flash_start: usize,
    /// The address of the beginning of the region the process has access to in
    /// nonvolatile memory. This is after the TBF header and any other memory
    /// the kernel has reserved for its own use.
    pub flash_non_protected_start: usize,
    /// The address immediately after the end of the region allocated for this
    /// process in nonvolatile memory.
    pub flash_end: usize,

    /// The address of the beginning of the process's allocated region in
    /// memory.
    pub sram_start: usize,
    /// The address of the application break. This is the address immediately
    /// after the end of the memory the process has access to.
    pub sram_app_brk: usize,
    /// The lowest address of any allocated grant. This is the start of the
    /// region the kernel is using for its own internal state on behalf of this
    /// process.
    pub sram_grant_start: usize,
    /// The address immediately after the end of the region allocated for this
    /// process in memory.
    pub sram_end: usize,

    /// The address of the start of the process's heap, if known. Note, managing
    /// this is completely up to the process, and the kernel relies on the
    /// process explicitly notifying it of this address. Therefore, its possible
    /// the kernel does not know the start address, or its start address could
    /// be incorrect.
    pub sram_heap_start: Option<usize>,
    /// The address of the top (or start) of the process's stack, if known.
    /// Note, managing the stack is completely up to the process, and the kernel
    /// relies on the process explicitly notifying it of where it started its
    /// stack. Therefore, its possible the kernel does not know the start
    /// address, or its start address could be incorrect.
    pub sram_stack_top: Option<usize>,
    /// The lowest address the kernel has seen the stack pointer. Note, the
    /// stack is entirely managed by the process, and the process could
    /// intentionally obscure this address from the kernel. Also, the stack may
    /// have reached a lower address, this is only the lowest address seen when
    /// the process calls a syscall.
    pub sram_stack_bottom: Option<usize>,
}

/// Collection of process state related to the size in memory of various process
/// structures.
pub struct ProcessSizes {
    /// The number of bytes used for the grant pointer table.
    pub grant_pointers: usize,
    /// The number of bytes used for the pending upcall queue.
    pub upcall_list: usize,
    /// The number of bytes used for the process control block (i.e. the
    /// `ProcessX` struct).
    pub process_control_block: usize,
}
