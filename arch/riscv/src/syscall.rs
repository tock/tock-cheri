//! Kernel-userland system call interface for RISC-V architecture.

use core::convert::TryInto;
use core::fmt::{Display, Formatter, Write};
use core::mem::size_of;
use core::ops::Range;

use crate::csr::mcause;
use kernel;
use kernel::cheri::*;
use kernel::errorcode::ErrorCode;
use kernel::syscall::ContextSwitchReason;

// Sadly, CHERI macros are not namespaced
use kernel::utilities::singleton_checker::SingletonChecker;
use kernel::*;

/// This holds all of the state that the kernel must keep for the process when
/// the process is not executing.
#[derive(Default)]
#[repr(C)]
pub struct RiscvStoredState {
    /// Store all of the app registers.
    regs: [cptr; 31],

    /// This holds the PC value of the app when the exception/syscall/interrupt
    /// occurred. We also use this to set the PC that the app should start
    /// executing at when it is resumed/started.
    pc: cptr,

    /// This holds the default data capability. Switched with the kernel DDC if we trap from an app.
    #[cfg(target_feature = "xcheri")]
    ddc: cptr,

    /// We need to store the mcause CSR between when the trap occurs and after
    /// we exit the trap handler and resume the context switching code.
    mcause: usize,

    /// We need to store the mtval CSR for the process in case the mcause
    /// indicates a fault. In that case, the mtval contains useful debugging
    /// information.
    mtval: usize,
}

pub struct DdcDisplay<'a> {
    _state: &'a RiscvStoredState,
}

impl<'a> Display for DdcDisplay<'a> {
    fn fmt(&self, _f: &mut Formatter<'_>) -> core::fmt::Result {
        #[cfg(target_feature = "xcheri")]
        {
            return _f.write_fmt(format_args!("DDC: {:#010X}", self._state.ddc));
        }
        #[cfg(not(target_feature = "xcheri"))]
        core::fmt::Result::Ok(())
    }
}

impl RiscvStoredState {
    pub fn get_ddc_display(&self) -> DdcDisplay {
        DdcDisplay { _state: self }
    }
}

// Because who would ever need offsetof?
#[cfg(target_feature = "xcheri")]
pub const CAUSE_OFFSET: usize = size_of::<cptr>() * 33;
#[cfg(not(target_feature = "xcheri"))]
pub const CAUSE_OFFSET: usize = size_of::<cptr>() * 32;

// Named offsets into the stored state registers.  These needs to be kept in
// sync with the register save logic in _start_trap() as well as the register
// restore logic in switch_to_process() below.
const R_RA: usize = 0;
const R_SP: usize = 1;
const R_A0: usize = 9;
const R_A1: usize = 10;
const R_A2: usize = 11;
const R_A3: usize = 12;
const R_A4: usize = 13;

/// Values for encoding the stored state buffer in a binary slice.
const VERSION: usize = 1;
const STORED_STATE_SIZE: usize = size_of::<RiscvStoredState>() as usize;
#[cfg(any(target_arch = "riscv32"))]
const TAG: [u8; 4] = [b'r', b'v', b'5', b'i'];
#[cfg(any(target_arch = "riscv64", not(target_os = "none")))]
const TAG: [u8; 8] = [b'r', b'v', b'5', b'i', b'r', b'v', b'5', b'i'];
const METADATA_LEN: usize = 3;

// TODO: CHERI. This seems to be for swap or some such. Needs thinking about.

const VERSION_IDX: usize = 0;
const SIZE_IDX: usize = 1;
const TAG_IDX: usize = 2;
const PC_IDX: usize = 3;
const MCAUSE_IDX: usize = 4;
const MTVAL_IDX: usize = 5;
const REGS_IDX: usize = 6;
const REGS_RANGE: Range<usize> = REGS_IDX..REGS_IDX + 31;

const USIZE_SZ: usize = size_of::<usize>();
fn usize_byte_range(index: usize) -> Range<usize> {
    index * USIZE_SZ..(index + 1) * USIZE_SZ
}

fn usize_from_u8_slice(slice: &[u8], index: usize) -> Result<usize, ErrorCode> {
    let range = usize_byte_range(index);
    Ok(usize::from_le_bytes(
        slice
            .get(range)
            .ok_or(ErrorCode::SIZE)?
            .try_into()
            .or(Err(ErrorCode::FAIL))?,
    ))
}

fn write_usize_to_u8_slice(val: usize, slice: &mut [u8], index: usize) {
    let range = usize_byte_range(index);
    slice[range].copy_from_slice(&val.to_le_bytes());
}

impl core::convert::TryFrom<&[u8]> for RiscvStoredState {
    type Error = ErrorCode;
    fn try_from(ss: &[u8]) -> Result<RiscvStoredState, Self::Error> {
        if ss.len() == size_of::<RiscvStoredState>() + METADATA_LEN * USIZE_SZ
            && usize_from_u8_slice(ss, VERSION_IDX)? == VERSION
            && usize_from_u8_slice(ss, SIZE_IDX)? == STORED_STATE_SIZE
            && usize_from_u8_slice(ss, TAG_IDX)? == usize::from_le_bytes(TAG)
        {
            let mut res = RiscvStoredState {
                regs: [0usize.into(); 31],
                pc: (usize_from_u8_slice(ss, PC_IDX)? as usize).into(),
                #[cfg(target_feature = "xcheri")]
                ddc: 0usize.into(),
                mcause: usize_from_u8_slice(ss, MCAUSE_IDX)?,
                mtval: usize_from_u8_slice(ss, MTVAL_IDX)?,
            };
            for (i, v) in (REGS_RANGE).enumerate() {
                res.regs[i] = (usize_from_u8_slice(ss, v)? as usize).into();
            }
            Ok(res)
        } else {
            Err(ErrorCode::FAIL)
        }
    }
}

/// Implementation of the `UserspaceKernelBoundary` for the RISC-V architecture.
pub struct SysCall(());

impl SysCall {
    pub const unsafe fn new() -> SysCall {
        SysCall(())
    }
    pub const fn const_new(chk: &mut SingletonChecker) -> Self {
        assert_single!(chk);
        Self(())
    }
}

kernel::very_simple_component!(impl for SysCall, const_new(&'a mut SingletonChecker));

impl kernel::syscall::UserspaceKernelBoundary for SysCall {
    type StoredState = RiscvStoredState;

    fn initial_process_app_brk_size(&self) -> usize {
        // The RV32I UKB implementation does not use process memory for any
        // context switch state. Therefore, we do not need any process-accessible
        // memory to start with to successfully context switch to the process the
        // first time.
        0
    }

    unsafe fn initialize_process(
        &self,
        accessible_memory_start: *const u8,
        _app_brk: *const u8,
        state: &mut Self::StoredState,
    ) -> Result<(), ()> {
        // Need to clear the stored state when initializing.
        state.regs.iter_mut().for_each(|x| *x = usize::into(0));
        // CHERI note: this PC cannot be executed. It will always be replaced with an initial fn.
        state.pc = usize::into(0);
        #[cfg(target_feature = "xcheri")]
        {
            let start = accessible_memory_start as usize;

            state
                .ddc
                .set_addr_from_ddc_restricted(start, start, (_app_brk as usize) - start);
        }

        state.mcause = 0;

        // The first time the process runs we need to set the initial stack
        // pointer in the sp register.
        //
        // We do not pre-allocate any stack for RV32I processes.
        state.regs[R_SP] = usize::into(accessible_memory_start as usize);

        // We do not use memory for UKB, so just return ok.
        Ok(())
    }

    unsafe fn get_extra_syscall_arg(
        &self,
        ndx: usize,
        _accessible_memory_start: *const u8,
        _app_brk: *const u8,
        state: &Self::StoredState,
    ) -> Option<usize> {
        // A4 was the last argument used by the standard syscall. We can get at least another 3,
        // and then we might want to go to the stack.
        if ndx >= 3 {
            return None;
        }
        Some(state.regs[R_A4 + 1 + ndx].into())
    }

    unsafe fn set_syscall_return_value(
        &self,
        _accessible_memory_start: *const u8,
        _app_brk: *const u8,
        state: &mut Self::StoredState,
        return_value: kernel::syscall::SyscallReturn,
    ) -> Result<(), ()> {
        // Encode the system call return value into registers,
        // available for when the process resumes

        // We need to use a bunch of split_at_mut's to have multiple
        // mutable borrows into the same slice at the same time.
        //
        // Since the compiler knows the size of this slice, and these
        // calls will be optimized out, we use one to get to the first
        // register (A0)
        let (_, r) = state.regs.split_at_mut(R_A0);

        // This comes with the assumption that the respective
        // registers are stored at monotonically increasing indices
        // in the register slice
        let (a0slice, r) = r.split_at_mut(R_A1 - R_A0);
        let (a1slice, r) = r.split_at_mut(R_A2 - R_A1);
        let (a2slice, a3slice) = r.split_at_mut(R_A3 - R_A2);

        // Really we need to write out own version of this that zeros other bits
        // Then the above ugly coerce would not be needed
        return_value.encode_syscall_return_cptr(
            &mut a0slice[0],
            &mut a1slice[0],
            &mut a2slice[0],
            &mut a3slice[0],
        );

        // We do not use process memory, so this cannot fail.
        Ok(())
    }

    unsafe fn set_process_function(
        &self,
        _accessible_memory_start: *const u8,
        _app_brk: *const u8,
        state: &mut RiscvStoredState,
        callback: kernel::process::FunctionCall,
    ) -> Result<(), ()> {
        // Set the register state for the application when it starts
        // executing. These are the argument registers.
        state.regs[R_A0] = callback.argument0.into();
        state.regs[R_A1] = callback.argument1.into();
        state.regs[R_A2] = callback.argument2.into();
        state.regs[R_A3] = callback.argument3.into();

        // We also need to set the return address (ra) register so that the new
        // function that the process is running returns to the correct location.
        // Note, however, that if this function happens to be the first time the
        // process is executing then `state.pc` is invalid/useless, but the
        // application must ignore it anyway since there is nothing logically
        // for it to return to. So this doesn't hurt anything.
        state.regs[R_RA] = state.pc;

        // Save the PC we expect to execute.
        // On CHERI we are basically forcing a jump, so caller better have the correct bounds.
        state.pc = callback.pc;

        Ok(())
    }

    // Mock implementation for tests on Travis-CI.
    #[cfg(not(any(target_os = "none")))]
    unsafe fn switch_to_process(
        &self,
        _accessible_memory_start: *const u8,
        _app_brk: *const u8,
        _state: &mut RiscvStoredState,
    ) -> (ContextSwitchReason, Option<*const u8>) {
        // Convince lint that 'mcause' and 'R_A4' are used during test build
        let _cause = mcause::Trap::from(_state.mcause as usize);
        let _arg4 = _state.regs[R_A4];
        unimplemented!()
    }

    #[cfg(all(target_os = "none"))]
    unsafe fn switch_to_process(
        &self,
        _accessible_memory_start: *const u8,
        _app_brk: *const u8,
        state: &mut RiscvStoredState,
    ) -> (ContextSwitchReason, Option<*const u8>) {
        // We need to ensure that the compiler does not reorder
        // kernel memory writes to after the userspace context switch
        // to ensure we provide a consistent memory view of
        // application-accessible buffers.
        //
        // The compiler will not be able to reorder memory accesses
        // beyond this point, as the "nomem" option on the asm!-block
        // is not set, hence the compiler has to assume the assembly
        // will issue arbitrary memory accesses (acting as a compiler
        // fence).
        kernel::easm!("
          // Before switching to the app we need to save the kernel registers to
          // the kernel stack. We then save the stack pointer in the mscratch
          // CSR (0x340) so we can retrieve it after returning to the kernel
          // from the app.
          //
          // A few values get saved to the kernel stack, including an app
          // register temporarily after entering the trap handler. Here is a
          // memory map to make it easier to keep track:
          //
          // ```
          // 34 * SZ(sp):          <- original stack pointer
          // 3..32 * SZ(sp) : saved registers
          // 2 * SZ(sp): _return_to_kernel (100) (address to resume after trap)
          // 1 * SZ(sp): *state   (Per-process StoredState struct)
          // 0 * SZ(sp): app s0   <- new stack pointer
          // ```

          addi sp, sp, -34*{CLEN_BYTES}  // Move the stack pointer down to make room.",
          ;stptr!() ptrregn!("1") ", 3*{CLEN_BYTES}(sp)    // Save all of the registers on the kernel stack.",
          FOR_RANGE("regn" in 3 .. 32 :
                stptr!() ptrregn!() "\\()\\regn, (\\regn+1)*{CLEN_BYTES}(sp)"
          ),
          ; stx!() " a0, 1*{CLEN_BYTES}(sp)    // Store process state pointer on stack as well.
                              // We need to have this available for after the app
                              // returns to the kernel so we can store its
                              // registers.

          // From here on we can't allow the CPU to take interrupts
          // anymore, as that might result in the trap handler
          // believing that a context switch to userspace already
          // occurred (as mscratch is non-zero). Restore the userspace
          // state fully prior to enabling interrupts again
          // (implicitly using mret).
          //
          // If this is executed _after_ setting mscratch, this result
          // in the race condition of [PR
          // 2308](https://github.com/tock/tock/pull/2308)

          // Therefore, clear the following bits in mstatus first:
          //   0x00000008 -> bit 3 -> MIE (disabling interrupts here)
          // + 0x00001800 -> bits 11,12 -> MPP (switch to usermode on mret)
          li t0, 0x00001808
          csrrc x0, 0x300, t0      // clear bits in mstatus, don't care about read

          // Afterwards, set the following bits in mstatus:
          //   0x00000080 -> bit 7 -> MPIE (enable interrupts on mret)
          li t0, 0x00000080
          csrrs x0, 0x300, t0      // set bits in mstatus, don't care about read


          // Store the address to jump back to on the stack so that the trap
          // handler knows where to return to after the app stops executing.

          la   t0, 100f",
          ; ".if " is_cheri!() "
              // On CHERI, we must add some bounds information
              cspecialr ct1, pcc
              csetaddr  ct0, ct1, t0
          .endif
          " stptr!() ptrreg!("t0") ", 2*{CLEN_BYTES}(sp)",
          csr_op!("mscratch" <- "sp"),
          "                   // Save stack pointer in mscratch. This allows
                              // us to find it when the app returns back to
                              // the kernel.

          // We have to set the mepc CSR with the PC we want the app to start
          // executing at. This has been saved in Riscv32iStoredState for us
          // (either when the app returned back to the kernel or in the
          // `set_process_function()` function).
          // Retrieve the PC from Riscv32iStoredState",
          ; ldptr!() ptrreg!("t0") ", 31*{CLEN_BYTES}(a0)",
          csr_op!("mepc" <- "t0"), "// Set mepc CSR. This is the PC we want to go to.

          // Restore all of the app registers from what we saved. If this is the
          // first time running the app then most of these values are
          // irrelevant, However we do need to set the four arguments to the
          // `_start_ function in the app. If the app has been executing then this
          // allows the app to correctly resume.
          mv   t0,  a0       // Save the state pointer to a specific register.",
          FOR_RANGE("regn" in 1 .. 32 :
                ".if \\regn != 5
                    " ldptr!() ptrregn!() "\\()\\regn, (\\regn-1)*{CLEN_BYTES}(t0)
                 .endif"
          ),
          ; ".if " is_cheri!() "
              // Load processes DDC. We cannot restore it before the last load has happened.
              // We can use mtdc as a scratch register (have it hold ct1), so ct1 can hold ddc.
              // DDC should currently hold the kernel DDC, which should eventually go in mtdc
              cspecialw   mtdc, ct1
              " ldptr!() ptrreg!("t1") ", 32*{CLEN_BYTES}(t0)
          .endif
          " ldptr!() ptrregn!(5) ", 4*{CLEN_BYTES}(t0) // t0. Do last since we overwrite our pointer.
          .if " is_cheri!() "
              // Currently:
              //    mtdc holds ct1
              //    ct1 holds ddc
              //    ddc holds mdtc
              cspecialrw ct1, ddc, ct1
              cspecialrw ct1, mtdc, ct1
          .endif

          // Call mret to jump to where mepc points, switch to user mode, and
          // start running the app.
          mret




          // This is where the trap handler jumps back to after the app stops
          // executing.
        100: // _return_to_kernel

          // We have already stored the app registers in the trap handler. We
          // can restore the kernel registers before resuming kernel code.",
          ; ldptr!() ptrregn!(1) ", 3*{CLEN_BYTES}(sp)",
          FOR_RANGE("regn" in 3 .. 32 :
              ldptr!() ptrregn!() "\\()\\regn, (\\regn+1)*{CLEN_BYTES}(sp)"
          ),

          "addi sp, sp, 34*{CLEN_BYTES}   // Reset kernel stack pointer",

          // The register to put the state struct pointer in is not
          // particularly relevant, however we must avoid using t0
          // as that is overwritten prior to being accessed
          // (although stored and later restored) in the assembly
          CLEN_BYTES = const size_of::<cptr>(),
          in("a0") state as *mut RiscvStoredState,
        );

        let ret = match mcause::Trap::from(state.mcause as usize) {
            mcause::Trap::Interrupt(_intr) => {
                // An interrupt occurred while the app was running.
                ContextSwitchReason::Interrupted
            }
            mcause::Trap::Exception(excp) => {
                match excp {
                    // The SiFive HiFive1 board allegedly does not support
                    // u-mode, so the m-mode ecall is handled here too.
                    mcause::Exception::UserEnvCall | mcause::Exception::MachineEnvCall => {
                        // Need to increment the PC so when we return we start at the correct
                        // instruction. The hardware does not do this for us.
                        state.pc += 4;

                        let syscall = kernel::syscall::Syscall::from_register_arguments(
                            usize::from(state.regs[R_A4]) as u8,
                            usize::from(state.regs[R_A0]),
                            state.regs[R_A1],
                            state.regs[R_A2],
                            state.regs[R_A3],
                        );

                        match syscall {
                            Some(s) => ContextSwitchReason::SyscallFired { syscall: s },
                            None => ContextSwitchReason::Fault,
                        }
                    }
                    _ => {
                        // All other exceptions result in faulted state
                        ContextSwitchReason::Fault
                    }
                }
            }
        };
        let new_stack_pointer = state.regs[R_SP];
        (ret, Some(new_stack_pointer.as_ptr() as *const u8))
    }

    unsafe fn print_context(
        &self,
        _accessible_memory_start: *const u8,
        _app_brk: *const u8,
        state: &RiscvStoredState,
        writer: &mut dyn Write,
    ) {
        let _ = writer.write_fmt(format_args!(
            "\
             \r\n R0 : {:#010X}    R16: {:#010X}\
             \r\n R1 : {:#010X}    R17: {:#010X}\
             \r\n R2 : {:#010X}    R18: {:#010X}\
             \r\n R3 : {:#010X}    R19: {:#010X}\
             \r\n R4 : {:#010X}    R20: {:#010X}\
             \r\n R5 : {:#010X}    R21: {:#010X}\
             \r\n R6 : {:#010X}    R22: {:#010X}\
             \r\n R7 : {:#010X}    R23: {:#010X}\
             \r\n R8 : {:#010X}    R24: {:#010X}\
             \r\n R9 : {:#010X}    R25: {:#010X}\
             \r\n R10: {:#010X}    R26: {:#010X}\
             \r\n R11: {:#010X}    R27: {:#010X}\
             \r\n R12: {:#010X}    R28: {:#010X}\
             \r\n R13: {:#010X}    R29: {:#010X}\
             \r\n R14: {:#010X}    R30: {:#010X}\
             \r\n R15: {:#010X}    R31: {:#010X}\
             \r\n PC : {:#010X}    {}           \
             \r\n\
             \r\n mcause: {:#010X} (",
            <cptr as From<usize>>::from(0usize),
            state.regs[15],
            state.regs[0],
            state.regs[16],
            state.regs[1],
            state.regs[17],
            state.regs[2],
            state.regs[18],
            state.regs[3],
            state.regs[19],
            state.regs[4],
            state.regs[20],
            state.regs[5],
            state.regs[21],
            state.regs[6],
            state.regs[22],
            state.regs[7],
            state.regs[23],
            state.regs[8],
            state.regs[24],
            state.regs[9],
            state.regs[25],
            state.regs[10],
            state.regs[26],
            state.regs[11],
            state.regs[27],
            state.regs[12],
            state.regs[28],
            state.regs[13],
            state.regs[29],
            state.regs[14],
            state.regs[30],
            state.pc,
            state.get_ddc_display(),
            state.mcause,
        ));
        let cause = mcause::Trap::from(state.mcause as usize);
        crate::print_mcause(cause, writer);
        let _ = writer.write_fmt(format_args!(
            ")\
             \r\n mtval:  {:#010X} (",
            state.mtval,
        ));
        crate::print_mtval(cause, state.mtval, writer);
        let _ = writer.write_fmt(format_args!(")\r\n\r\n",));
    }

    fn store_context(&self, state: &RiscvStoredState, out: &mut [u8]) -> Result<usize, ErrorCode> {
        const USIZE_SZ: usize = size_of::<usize>();
        if out.len() >= size_of::<RiscvStoredState>() + METADATA_LEN * USIZE_SZ {
            write_usize_to_u8_slice(VERSION, out, VERSION_IDX);
            write_usize_to_u8_slice(STORED_STATE_SIZE, out, SIZE_IDX);
            write_usize_to_u8_slice(usize::from_le_bytes(TAG), out, TAG_IDX);
            write_usize_to_u8_slice(usize::from(state.pc), out, PC_IDX);
            write_usize_to_u8_slice(state.mcause, out, MCAUSE_IDX);
            write_usize_to_u8_slice(state.mtval, out, MTVAL_IDX);
            for (i, v) in state.regs.iter().enumerate() {
                write_usize_to_u8_slice(usize::from(*v), out, REGS_IDX + i);
            }
            // +3 for pc, mcause, mtval
            Ok((state.regs.len() + 3 + METADATA_LEN) * USIZE_SZ)
        } else {
            Err(ErrorCode::SIZE)
        }
    }
}
