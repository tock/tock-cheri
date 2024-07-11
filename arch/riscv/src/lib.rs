//! Shared support for RISC-V architectures.

#![crate_name = "riscv"]
#![crate_type = "rlib"]
#![feature(asm_const, naked_functions, split_array)]
#![feature(const_trait_impl, const_mut_refs, const_slice_split_at_mut)]
#![feature(const_type_id)]
#![feature(const_default_impls)]
#![feature(macro_metavar_expr)]
#![no_std]

pub mod csr;
pub mod plic;
pub mod pmp;
pub mod support;
pub mod syscall;

// Is there a case when sizeof(usize) is not XLEN?
// There is some confusion in the code base as to which one to use

#[cfg(target_arch = "riscv32")]
pub const XLEN: usize = 32;
#[cfg(any(target_arch = "riscv64", not(target_os = "none")))]
pub const XLEN: usize = 64;

#[cfg(not(any(
    target_arch = "riscv32",
    target_arch = "riscv64",
    not(target_os = "none")
)))]
compile_error!("No target architecture defined");

#[cfg(target_feature = "xcheri")]
pub const CLEN_BYTES: usize = 2 * XLEN;

// CLEN_BYTES is not really defined on non CHERI. On non-CHERI this just means XLEN.
#[cfg(not(target_feature = "xcheri"))]
pub const CLEN_BYTES: usize = XLEN;

use core::fmt::Write;

use kernel::utilities::registers::interfaces::{Readable, Writeable};

extern "C" {
    // Where the end of the stack region is (and hence where the stack should
    // start).
    static _estack: usize;

    // Boundaries of the .bss section.
    static mut _szero: usize;
    static mut _ezero: usize;

    // Where the .data section is stored in flash.
    static mut _etext: usize;

    // Boundaries of the .data section.
    static mut _srelocate: usize;
    static mut _erelocate: usize;

    // The global pointer, value set in the linker script
    static __global_pointer: usize;
}

/// Entry point of all programs (`_start`).
///
/// This assembly does three functions:
///
/// 1. It initializes the stack pointer, the frame pointer (needed for closures
///    to work in start_rust) and the global pointer.
/// 2. It initializes the .bss and .data RAM segments. This must be done before
///    any Rust code runs. See <https://github.com/tock/tock/issues/2222> for more
///    information.
/// 3. Finally it calls `main()`, the main entry point for Tock boards.
#[cfg(target_os = "none")]
#[link_section = ".riscv.start"]
#[export_name = "_start"]
#[naked]
pub extern "C" fn _start() {
    use kernel::*;
    unsafe {
        kernel::easm! ("
            // Set the global pointer register using the variable defined in the
            // linker script. This register is only set once. The global pointer
            // is a method for sharing state between the linker and the CPU so
            // that the linker can emit code with offsets that are relative to
            // the gp register, and the CPU can successfully execute them.
            //
            // https://gnu-mcu-eclipse.github.io/arch/riscv/programmer/#the-gp-global-pointer-register
            // https://groups.google.com/a/groups.riscv.org/forum/#!msg/sw-dev/60IdaZj27dY/5MydPLnHAQAJ
            // https://www.sifive.com/blog/2017/08/28/all-aboard-part-3-linker-relaxation-in-riscv-toolchain/
            // Likely not a good idea to allow the linker to use global pointer to derive global pointer
            .option push
            .option norelax
            la   gp, {gp}$           // Set the global pointer. Value set in linker script.
            .option pop
            // Initialize the stack pointer register. This comes directly from
            // the linker script.
            la   sp, {estack}

            // Set s0 (the frame pointer) to the start of the stack.
            add  s0, sp, zero

            // Initialize mscratch to 0 so that we know that we are currently
            // in the kernel. This is used for the check in the trap handler.
            csrw 0x340, zero  // CSR=0x340=mscratch

            // INITIALIZE MEMORY

            // Start by initializing .bss memory. The Tock linker script defines
            // `_szero` and `_ezero` to mark the .bss segment.
            la a0, {sbss}               // a0 = first address of .bss
            la a1, {ebss}               // a1 = first address after .bss

          100: // bss_init_loop
            beq  a0, a1, 101f           // If a0 == a1, we are done.",
            ; stx!() " zero, 0(a0)      // *a0 = 0. Write 0 to the memory location in a0.
            addi a0, a0, {XLEN_BYTES}   // a0 = a0 + XLEN_BYTES. Increment pointer to next word.
            j 100b                      // Continue the loop.

          101: // bss_init_done


            // Now initialize .data memory. This involves coping the values right at the
            // end of the .text section (in flash) into the .data section (in RAM).
            la a0, {sdata}              // a0 = first address of data section in RAM
            la a1, {edata}              // a1 = first address after data section in RAM
            la a2, {etext}              // a2 = address of stored data initial values

          200: // data_init_loop
            beq  a0, a1, 201f           // If we have reached the end of the .data
                                        // section then we are done.",
            ; ldx!() " a3, 0(a2)        // a3 = *a2. Load value from initial values into a3.
            " stx!() " a3, 0(a0)        // *a0 = a3. Store initial value into
                                        // next place in .data.
            addi a0, a0, {XLEN_BYTES}   // a0 = a0 + XLEN_BYTES. Increment to next word in memory.
            addi a2, a2, {XLEN_BYTES}   // a2 = a2 + XLEN_BYTES. Increment to next word in flash.
            j 200b                      // Continue the loop.

          201: // data_init_done

            // With that initial setup out of the way, we now branch to the main
            // code, likely defined in a board's main.rs.
            j main
        ",
        gp = sym __global_pointer,
        estack = sym _estack,
        sbss = sym _szero,
        ebss = sym _ezero,
        sdata = sym _srelocate,
        edata = sym _erelocate,
        etext = sym _etext,
        XLEN_BYTES = const XLEN / 8,
        options(noreturn)
        );
    }
}

/// The various privilege levels in RISC-V.
pub enum PermissionMode {
    User = 0x0,
    Supervisor = 0x1,
    Reserved = 0x2,
    Machine = 0x3,
}

/// Tell the MCU what address the trap handler is located at.
///
/// This is a generic implementation. There may be board specific versions as
/// some platforms have added more bits to the `mtvec` register.
///
/// The trap handler is called on exceptions and for interrupts.
pub unsafe fn configure_trap_handler(mode: PermissionMode) {
    match mode {
        PermissionMode::Machine => csr::CSR.mtvec.write(
            csr::mtvec::mtvec::trap_addr.val(_start_trap as usize >> 2)
                + csr::mtvec::mtvec::mode::CLEAR,
        ),
        PermissionMode::Supervisor => csr::CSR.stvec.write(
            csr::stvec::stvec::trap_addr.val(_start_trap as usize >> 2)
                + csr::stvec::stvec::mode::CLEAR,
        ),
        PermissionMode::User => csr::CSR.utvec.write(
            csr::utvec::utvec::trap_addr.val(_start_trap as usize >> 2)
                + csr::utvec::utvec::mode::CLEAR,
        ),
        PermissionMode::Reserved => (
            // TODO some sort of error handling?
            ),
    }
}

// Mock implementation for tests on Travis-CI.
#[cfg(not(any(target_os = "none")))]
pub extern "C" fn _start_trap() {
    unimplemented!()
}

/// This is the trap handler function. This code is called on all traps,
/// including interrupts, exceptions, and system calls from applications.
///
/// Tock uses only the single trap handler, and does not use any vectored
/// interrupts or other exception handling. The trap handler has to determine
/// why the trap handler was called, and respond accordingly. Generally, there
/// are two reasons the trap handler gets called: an interrupt occurred or an
/// application called a syscall.
///
/// In the case of an interrupt while the kernel was executing we only need to
/// save the kernel registers and then run whatever interrupt handling code we
/// need to. If the trap happens while and application was executing, we have to
/// save the application state and then resume the `switch_to()` function to
/// correctly return back to the kernel.
#[cfg(all(target_os = "none"))]
#[link_section = ".riscv.trap"]
#[export_name = "_start_trap"]
#[naked]
pub extern "C" fn _start_trap() {
    use kernel::*;
    unsafe {
        kernel::easm!(
            "
            // The first thing we have to do is determine if we came from user
            // mode or kernel mode, as we need to save state and proceed
            // differently. We cannot, however, use any registers because we do
            // not want to lose their contents. So, we rely on `mscratch`. If
            // mscratch is 0, then we came from the kernel. If it is >0, then it
            // contains the kernel's stack pointer and we came from an app.
            //
            // We use the csrrw instruction to save the current stack pointer
            // so we can retrieve it if necessary.
            //
            // If we could enter this trap handler twice (for example,
            // handling an interrupt while an exception is being
            // handled), storing a non-zero value in mscratch
            // temporarily could cause a race condition similar to the
            // one of PR 2308[1].
            // However, as indicated in section 3.1.6.1 of the RISC-V
            // Privileged Spec[2], MIE will be set to 0 when taking a
            // trap into machine mode. Therefore, this can only happen
            // when causing an exception in the trap handler itself.
            //
            // [1] https://github.com/tock/tock/pull/2308
            // [2] https://github.com/riscv/riscv-isa-manual/releases/download/draft-20201222-42dc13a/riscv-privileged.pdf
            // Even though this may be a hybrid kernel, we still need to use mcscratch
            // in case ths user cared about their CSP",
            csr_op!("sp" <- "mscratch" <- "sp"),
            "bnez  sp, 300f      // If sp != 0 then we must have come from an app.


        // _from_kernel:
            // Swap back the zero value for the stack pointer in mscratch",
            csr_op!("sp" <- "mscratch" <- "sp"),
            "// Now, since we want to use the stack to save kernel registers, we
            // first need to make sure that the trap wasn't the result of a
            // stack overflow, in which case we can't use the current stack
            // pointer. We also, however, cannot modify any of the current
            // registers until we save them, and we cannot save them to the
            // stack until we know the stack is valid. So, we use the mscratch
            // trick again to get one register we can use.

            // Save t0's contents to mscratch",
            csr_op!("mscratch" <- "t0"),
            "// Load the address of the bottom of the stack (`_sstack`) into our
            // newly freed-up t0 register.
            .type _sstack, object
            la    t0, _sstack

            // Compare the kernel stack pointer to the bottom of the stack. If
            // the stack pointer is above the bottom of the stack, then continue
            // handling the fault as normal.
            bgtu sp, t0, 100f                   // branch if sp > t0

            // If we get here, then we did encounter a stack overflow. We are
            // going to panic at this point, but for that to work we need a
            // valid stack to run the panic code. We do this by just starting
            // over with the kernel stack and placing the stack pointer at the
            // top of the original stack.
            la   sp, _estack


        100: // _from_kernel_continue

            // Restore t0, and make sure mscratch is set back to 0 (our flag
            // tracking that the kernel is executing).",
            "li t0, 0",
            csr_op!("t0" <- "mscratch" <- "t0"),"// t0=mscratch, mscratch=0

            // Make room for the caller saved registers we need to restore after
            // running any trap handler code.
            addi sp, sp, -16*{CLEN_BYTES}

            // Save all of the caller saved registers.",
            FOR_EACH("Reg" in ["ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"] :
                stptr!() ptrreg!() "\\()\\Reg, FOR_N*{CLEN_BYTES}(sp)"
            ), "

            // Jump to board-specific trap handler code. Likely this was an
            // interrupt and we want to disable a particular interrupt, but each
            // board/chip can customize this as needed.
            jal ra, _start_trap_rust_from_kernel

            // Restore the registers from the stack.",
            FOR_EACH("Reg" in ["ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"] :
                ldptr!() ptrreg!() "\\()\\Reg, FOR_N*{CLEN_BYTES}(sp)"
            ), "

            // Reset the stack pointer.
            addi sp, sp, 16*{CLEN_BYTES}

            // mret returns from the trap handler. The PC is set to what is in
            // mepc and execution proceeds from there. Since we did not modify
            // mepc we will return to where the exception occurred.
            mret



            // Handle entering the trap handler from an app differently.
        300: // _from_app

            // At this point all we know is that we entered the trap handler
            // from an app. We don't know _why_ we got a trap, it could be from
            // an interrupt, syscall, or fault (or maybe something else).
            // Therefore we have to be very careful not to overwrite any
            // registers before we have saved them.
            //
            // We ideally want to save registers in the per-process stored state
            // struct. However, we don't have a pointer to that yet, and we need
            // to use a temporary register to get that address. So, we save s0
            // to the kernel stack before we can it to the proper spot.",

            ; ".if " is_cheri!() "
                // On CHERI, no loads and stores can happen until we switch DDC.
                // Do a little juggle to swap mtdc and ddc (does not clobber ct0).
                // When we have some registers spare we will restore mtdc
                cspecialrw  ct0, mtdc, ct0
                cspecialrw  ct0, ddc, ct0
                cspecialrw  ct0, mtdc, ct0
            .endif",

            ; stptr!() ptrreg!("s0") ", 0*{CLEN_BYTES}(sp)
            // Ideally it would be better to save all of the app registers once
            // we return back to the `switch_to_process()` code. However, we
            // also potentially need to disable an interrupt in case the app was
            // interrupted, so it is safer to just immediately save all of the
            // app registers.
            //
            // We do this by retrieving the stored state pointer from the kernel
            // stack and storing the necessary values in it.",
            ; ldx!() " s0,  1*{CLEN_BYTES}(sp)  // Load the stored state pointer into s0.",
            ; stptr!()  ptrregn!("1") ",  0*{CLEN_BYTES}(s0)  // ra",
            FOR_RANGE("regn" in 3 .. 32 :
                ".if \\regn != 8 // s0
                " stptr!() ptrregn!() "\\()\\regn, (\\regn-1)*{CLEN_BYTES}(s0)
                .endif"
            ),
            // Now retrieve the original value of s0 and save that as well.",
            ;ldptr!() ptrreg!("t0") ",  0*{CLEN_BYTES}(sp)",
            ;stptr!() ptrreg!("t0") ",  7*{CLEN_BYTES}(s0)  // s0,fp
            // We also need to store the app stack pointer, mcause, and mepc. We
            // need to store mcause because we use that to determine why the app
            // stopped executing and returned to the kernel. We store mepc
            // because it is where we need to return to in the app at some
            // point. We need to store mtval in case the app faulted and we need
            // mtval to help with debugging.",
            ; ".if " is_cheri!() "
              // We now need to save the trapped DDC (which is in mtdc)
              // and restore mtdc it to what it was for the next trap
              cspecialr ct0, ddc
              cspecialrw ct0, mtdc, ct0
              sc        ct0, 32*{CLEN_BYTES}(s0)
           .endif",
            csr_op!("mscratch" -> "t0"),
            ;stptr!() ptrreg!("t0") ", 1*{CLEN_BYTES}(s0)  // Save the app sp to the stored state struct",
            csr_op!("mepc" -> "t0"),
            ;stptr!() ptrreg!("t0") ", 31*{CLEN_BYTES}(s0)  // Save the PC to the stored state struct
            csrr t0, 0x343    // CSR=0x343=mtval",
            ;stx!() " t0, ({CAUSE_OFFSET} + {XLEN_BYTES})(s0) // Save mtval to the stored state struct

            // Save mcause last, as we depend on it being loaded in t0 below
            csrr t0, 0x342    // CSR=0x342=mcause",
            ;stx!() " t0, ({CAUSE_OFFSET})(s0) // Save mcause to the stored state struct, leave in t0

            // Now we need to check if this was an interrupt, and if it was,
            // then we need to disable the interrupt before returning from this
            // trap handler so that it does not fire again. If mcause is greater
            // than or equal to zero this was not an interrupt (i.e. the most
            // significant bit is not 1).
            bge  t0, zero, 200f
            // Copy mcause into a0 and then call the interrupt disable function.
            mv   a0, t0
            jal  ra, _disable_interrupt_trap_rust_from_app

        200: // _from_app_continue
            // Now determine the address of _return_to_kernel and resume the
            // context switching code. We need to load _return_to_kernel into
            // mepc so we can use it to return to the context switch code.",
            ;ldptr!() ptrreg!("t0") ", 2 * {CLEN_BYTES}(sp) // Load _return_to_kernel into t0.",
            csr_op!("mepc" <- "t0"),
            // Ensure that mscratch is 0. This makes sure that we know that on
            // a future trap that we came from the kernel.
            "li t0, 0",
            csr_op!("mscratch" <- "t0"),"

            // Need to set mstatus.MPP to 0b11 so that we stay in machine mode.
            csrr t0, 0x300    // CSR=0x300=mstatus
            li   t1, 0x1800   // Load 0b11 to the MPP bits location in t1
            or   t0, t0, t1   // Set the MPP bits to one
            csrw 0x300, t0    // CSR=0x300=mstatus

            // Use mret to exit the trap handler and return to the context
            // switching code.
            mret
        ",
            CLEN_BYTES = const core::mem::size_of::<kernel::cheri::cptr>(),
            XLEN_BYTES = const XLEN / 8,
            CAUSE_OFFSET = const crate::syscall::CAUSE_OFFSET,
            options(noreturn)
        );
    }
}

/// RISC-V semihosting needs three exact instructions in uncompressed form.
///
/// See https://github.com/riscv/riscv-semihosting-spec/blob/main/riscv-semihosting-spec.adoc#11-semihosting-trap-instruction-sequence
/// for more details on the three instructions.
///
/// In order to work with semihosting we include the assembly here
/// where we are able to disable compressed instruction support. This
/// follows the example used in the Linux kernel:
/// https://elixir.bootlin.com/linux/v5.12.10/source/arch/riscv/include/asm/jump_label.h#L21
/// as suggested by the RISC-V developers:
/// https://groups.google.com/a/groups.riscv.org/g/isa-dev/c/XKkYacERM04/m/CdpOcqtRAgAJ
#[cfg(all(target_os = "none"))]
pub unsafe fn semihost_command(command: usize, arg0: usize, arg1: usize) -> usize {
    use core::arch::asm;
    let res;
    asm!(
    "
      .option push
      .option norelax
      .option norvc
      slli x0, x0, 0x1f
      ebreak
      srai x0, x0, 7
      .option pop
      ",
    in("a0") command,
    in("a1") arg0,
    in("a2") arg1,
    lateout("a0") res,
    );
    res
}

// Mock implementation for tests on Travis-CI.
#[cfg(not(any(target_os = "none")))]
pub unsafe fn semihost_command(_command: usize, _arg0: usize, _arg1: usize) -> usize {
    unimplemented!()
}

/// Print a readable string for an mcause reason.
pub unsafe fn print_mcause(mcval: csr::mcause::Trap, writer: &mut dyn Write) {
    match mcval {
        csr::mcause::Trap::Interrupt(interrupt) => match interrupt {
            csr::mcause::Interrupt::UserSoft => {
                let _ = writer.write_fmt(format_args!("User software interrupt"));
            }
            csr::mcause::Interrupt::SupervisorSoft => {
                let _ = writer.write_fmt(format_args!("Supervisor software interrupt"));
            }
            csr::mcause::Interrupt::MachineSoft => {
                let _ = writer.write_fmt(format_args!("Machine software interrupt"));
            }
            csr::mcause::Interrupt::UserTimer => {
                let _ = writer.write_fmt(format_args!("User timer interrupt"));
            }
            csr::mcause::Interrupt::SupervisorTimer => {
                let _ = writer.write_fmt(format_args!("Supervisor timer interrupt"));
            }
            csr::mcause::Interrupt::MachineTimer => {
                let _ = writer.write_fmt(format_args!("Machine timer interrupt"));
            }
            csr::mcause::Interrupt::UserExternal => {
                let _ = writer.write_fmt(format_args!("User external interrupt"));
            }
            csr::mcause::Interrupt::SupervisorExternal => {
                let _ = writer.write_fmt(format_args!("Supervisor external interrupt"));
            }
            csr::mcause::Interrupt::MachineExternal => {
                let _ = writer.write_fmt(format_args!("Machine external interrupt"));
            }
            csr::mcause::Interrupt::Unknown => {
                let _ = writer.write_fmt(format_args!("Reserved/Unknown"));
            }
        },
        csr::mcause::Trap::Exception(exception) => match exception {
            csr::mcause::Exception::InstructionMisaligned => {
                let _ = writer.write_fmt(format_args!("Instruction access misaligned"));
            }
            csr::mcause::Exception::InstructionFault => {
                let _ = writer.write_fmt(format_args!("Instruction access fault"));
            }
            csr::mcause::Exception::IllegalInstruction => {
                let _ = writer.write_fmt(format_args!("Illegal instruction"));
            }
            csr::mcause::Exception::Breakpoint => {
                let _ = writer.write_fmt(format_args!("Breakpoint"));
            }
            csr::mcause::Exception::LoadMisaligned => {
                let _ = writer.write_fmt(format_args!("Load address misaligned"));
            }
            csr::mcause::Exception::LoadFault => {
                let _ = writer.write_fmt(format_args!("Load access fault"));
            }
            csr::mcause::Exception::StoreMisaligned => {
                let _ = writer.write_fmt(format_args!("Store/AMO address misaligned"));
            }
            csr::mcause::Exception::StoreFault => {
                let _ = writer.write_fmt(format_args!("Store/AMO access fault"));
            }
            csr::mcause::Exception::UserEnvCall => {
                let _ = writer.write_fmt(format_args!("Environment call from U-mode"));
            }
            csr::mcause::Exception::SupervisorEnvCall => {
                let _ = writer.write_fmt(format_args!("Environment call from S-mode"));
            }
            csr::mcause::Exception::MachineEnvCall => {
                let _ = writer.write_fmt(format_args!("Environment call from M-mode"));
            }
            csr::mcause::Exception::InstructionPageFault => {
                let _ = writer.write_fmt(format_args!("Instruction page fault"));
            }
            csr::mcause::Exception::LoadPageFault => {
                let _ = writer.write_fmt(format_args!("Load page fault"));
            }
            csr::mcause::Exception::StorePageFault => {
                let _ = writer.write_fmt(format_args!("Store/AMO page fault"));
            }
            #[cfg(target_feature = "xcheri")]
            csr::mcause::Exception::CHERIPageException => {
                let _ = writer.write_fmt(format_args!("CHERI page exception"));
            }
            #[cfg(target_feature = "xcheri")]
            csr::mcause::Exception::CHERIException => {
                let _ = writer.write_fmt(format_args!("CHERI Exception"));
            }
            csr::mcause::Exception::Unknown => {
                let _ = writer.write_fmt(format_args!("Reserved"));
            }
        },
    }
}

/// Print a readable string for an mcause reason.
pub unsafe fn print_mtval(_mcval: csr::mcause::Trap, _mtval: usize, _writer: &mut dyn Write) {
    // Cheri exceptions have more information in the xtval register
    #[cfg(target_feature = "xcheri")]
    {
        use crate::csr::mtval::mtval;
        if let csr::mcause::Trap::Exception(ex) = _mcval {
            if ex == csr::mcause::Exception::CHERIPageException
                || ex == csr::mcause::Exception::CHERIException
            {
                let mtval =
                    tock_registers::LocalRegisterCopy::<usize, mtval::Register>::new(_mtval);

                let _ = _writer.write_fmt(format_args!("Cause = ",));

                // Print CHERI cause
                match mtval.read_as_enum(mtval::cause) {
                    Some(mtval::cause::Value::NONE) => {
                        let _ = _writer.write_fmt(format_args!("none"));
                    }
                    Some(mtval::cause::Value::LENGTH) => {
                        let _ = _writer.write_fmt(format_args!("length"));
                    }
                    Some(mtval::cause::Value::TAG) => {
                        let _ = _writer.write_fmt(format_args!("tag"));
                    }
                    Some(mtval::cause::Value::SEAL) => {
                        let _ = _writer.write_fmt(format_args!("seal"));
                    }
                    Some(mtval::cause::Value::TYPE) => {
                        let _ = _writer.write_fmt(format_args!("type"));
                    }
                    Some(mtval::cause::Value::PERM_SOFT) => {
                        let _ = _writer.write_fmt(format_args!("permit software defined"));
                    }
                    Some(mtval::cause::Value::REPRESENT) => {
                        let _ = _writer.write_fmt(format_args!("representability"));
                    }
                    Some(mtval::cause::Value::UNALIGNED) => {
                        let _ = _writer.write_fmt(format_args!("unaligned base"));
                    }
                    Some(mtval::cause::Value::GLOBAL) => {
                        let _ = _writer.write_fmt(format_args!("global"));
                    }
                    Some(mtval::cause::Value::PERM_EXECUTE) => {
                        let _ = _writer.write_fmt(format_args!("permit execute"));
                    }
                    Some(mtval::cause::Value::PERM_LOAD) => {
                        let _ = _writer.write_fmt(format_args!("permit load"));
                    }
                    Some(mtval::cause::Value::PERM_STORE) => {
                        let _ = _writer.write_fmt(format_args!("permit store"));
                    }
                    Some(mtval::cause::Value::PERM_LOAD_CAP) => {
                        let _ = _writer.write_fmt(format_args!("permit load cap"));
                    }
                    Some(mtval::cause::Value::PERM_STORE_CAP) => {
                        let _ = _writer.write_fmt(format_args!("permit store cap"));
                    }
                    Some(mtval::cause::Value::PERM_STORE_LOCAL_CAP) => {
                        let _ = _writer.write_fmt(format_args!("permit store local cap"));
                    }
                    Some(mtval::cause::Value::PERM_SEAL) => {
                        let _ = _writer.write_fmt(format_args!("permit seal"));
                    }
                    Some(mtval::cause::Value::PERM_ASR) => {
                        let _ = _writer.write_fmt(format_args!("permit access system registers"));
                    }
                    Some(mtval::cause::Value::PERM_CINVOKE) => {
                        let _ = _writer.write_fmt(format_args!("permit cinvoke"));
                    }
                    Some(mtval::cause::Value::PERM_CINVOKE_IDC) => {
                        let _ = _writer.write_fmt(format_args!("permit cinvoke IDC access"));
                    }
                    Some(mtval::cause::Value::PERM_UNSEAL) => {
                        let _ = _writer.write_fmt(format_args!("permit unseal"));
                    }
                    Some(mtval::cause::Value::PERM_SET_CID) => {
                        let _ = _writer.write_fmt(format_args!("permit set compartment ID"));
                    }
                    None => {
                        let _ = _writer.write_fmt(format_args!("invalid unknown"));
                    }
                }

                let _ = _writer.write_fmt(format_args!(", reg = ",));

                if let Some(mtval::cap_idx_type::Value::GPR) =
                    mtval.read_as_enum(mtval::cap_idx_type)
                {
                    // Just print GPR as a number
                    let _ = _writer.write_fmt(format_args!("C{}", mtval.read(mtval::cap_idx)));
                } else {
                    // CSRs have less formulaic names
                    match mtval.read_as_enum(mtval::cap_idx) {
                        Some(mtval::cap_idx::Value::PCC) => {
                            let _ = _writer.write_fmt(format_args!("PCC"));
                        }
                        Some(mtval::cap_idx::Value::DDC) => {
                            let _ = _writer.write_fmt(format_args!("DDC"));
                        }
                        Some(_) => {
                            let _ = _writer.write_fmt(format_args!("valid unknown"));
                        }
                        None => {
                            let _ = _writer.write_fmt(format_args!("invalid unknown"));
                        }
                    }
                }
            }
        }
    }
}

/// Prints out RISCV machine state, including basic system registers
/// (mcause, mstatus, mepc, mtval, interrupt status).
pub unsafe fn print_riscv_state(writer: &mut dyn Write) {
    let mcval: csr::mcause::Trap = core::convert::From::from(csr::CSR.mcause.extract());
    let _ = writer.write_fmt(format_args!("\r\n---| RISC-V Machine State |---\r\n"));
    let _ = writer.write_fmt(format_args!("Last cause (mcause): "));
    print_mcause(mcval, writer);
    let interrupt = csr::CSR.mcause.read(csr::mcause::mcause::is_interrupt);
    let code = csr::CSR.mcause.read(csr::mcause::mcause::reason);
    let _ = writer.write_fmt(format_args!(
        " (interrupt={}, exception code={:#010X})",
        interrupt, code
    ));
    let _ = writer.write_fmt(format_args!(
        "\r\nLast value (mtval):  {:#010X}\
         \r\n\
         \r\nSystem register dump:\
         \r\n mepc:    {:#010X}    mstatus:     {:#010X}\
         \r\n mcycle:  {:#010X}    minstret:    {:#010X}",
        csr::CSR.mtval.get(),
        csr::CSR.mepc.get(),
        csr::CSR.mstatus.get(),
        csr::CSR.mcycle.get(),
        csr::CSR.minstret.get(),
    ));
    let mstatus = csr::CSR.mstatus.extract();
    let uie = mstatus.is_set(csr::mstatus::mstatus::uie);
    let sie = mstatus.is_set(csr::mstatus::mstatus::sie);
    let mie = mstatus.is_set(csr::mstatus::mstatus::mie);
    let upie = mstatus.is_set(csr::mstatus::mstatus::upie);
    let spie = mstatus.is_set(csr::mstatus::mstatus::spie);
    let mpie = mstatus.is_set(csr::mstatus::mstatus::mpie);
    let spp = mstatus.is_set(csr::mstatus::mstatus::spp);
    let mpp = mstatus.read(csr::mstatus::mstatus::mpp);
    let _ = writer.write_fmt(format_args!(
        "\r\n mstatus: {:#010X}\
         \r\n  uie:    {:5}  upie:   {}\
         \r\n  sie:    {:5}  spie:   {}\
         \r\n  mie:    {:5}  mpie:   {}\
         \r\n  spp:    {}\
         \r\n  mpp:    {}",
        mstatus.get(),
        uie,
        upie,
        sie,
        spie,
        mie,
        mpie,
        spp,
        mpp,
    ));
    let e_usoft = csr::CSR.mie.is_set(csr::mie::mie::usoft);
    let e_ssoft = csr::CSR.mie.is_set(csr::mie::mie::ssoft);
    let e_msoft = csr::CSR.mie.is_set(csr::mie::mie::msoft);
    let e_utimer = csr::CSR.mie.is_set(csr::mie::mie::utimer);
    let e_stimer = csr::CSR.mie.is_set(csr::mie::mie::stimer);
    let e_mtimer = csr::CSR.mie.is_set(csr::mie::mie::mtimer);
    let e_uext = csr::CSR.mie.is_set(csr::mie::mie::uext);
    let e_sext = csr::CSR.mie.is_set(csr::mie::mie::sext);
    let e_mext = csr::CSR.mie.is_set(csr::mie::mie::mext);

    let p_usoft = csr::CSR.mip.is_set(csr::mip::mip::usoft);
    let p_ssoft = csr::CSR.mip.is_set(csr::mip::mip::ssoft);
    let p_msoft = csr::CSR.mip.is_set(csr::mip::mip::msoft);
    let p_utimer = csr::CSR.mip.is_set(csr::mip::mip::utimer);
    let p_stimer = csr::CSR.mip.is_set(csr::mip::mip::stimer);
    let p_mtimer = csr::CSR.mip.is_set(csr::mip::mip::mtimer);
    let p_uext = csr::CSR.mip.is_set(csr::mip::mip::uext);
    let p_sext = csr::CSR.mip.is_set(csr::mip::mip::sext);
    let p_mext = csr::CSR.mip.is_set(csr::mip::mip::mext);
    let _ = writer.write_fmt(format_args!(
        "\r\n mie:   {:#010X}   mip:   {:#010X}\
         \r\n  usoft:  {:6}              {:6}\
         \r\n  ssoft:  {:6}              {:6}\
         \r\n  msoft:  {:6}              {:6}\
         \r\n  utimer: {:6}              {:6}\
         \r\n  stimer: {:6}              {:6}\
         \r\n  mtimer: {:6}              {:6}\
         \r\n  uext:   {:6}              {:6}\
         \r\n  sext:   {:6}              {:6}\
         \r\n  mext:   {:6}              {:6}\r\n",
        csr::CSR.mie.get(),
        csr::CSR.mip.get(),
        e_usoft,
        p_usoft,
        e_ssoft,
        p_ssoft,
        e_msoft,
        p_msoft,
        e_utimer,
        p_utimer,
        e_stimer,
        p_stimer,
        e_mtimer,
        p_mtimer,
        e_uext,
        p_uext,
        e_sext,
        p_sext,
        e_mext,
        p_mext
    ));
}
