//! Support for the 32-bit RISC-V architecture.

#![crate_name = "rv32i"]
#![crate_type = "rlib"]
#![feature(asm_const, naked_functions)]
#![no_std]

#[cfg(any(target_arch = "riscv32", not(target_os = "none")))]
pub mod clic;
#[cfg(any(target_arch = "riscv32", not(target_os = "none")))]
pub mod epmp;
pub mod machine_timer;

// Re-export some shared libraries so that dependent crates do not have to have
// both rv32i and riscv as dependencies.
pub use riscv::configure_trap_handler;
pub use riscv::csr;
pub use riscv::pmp;
pub use riscv::print_riscv_state;
pub use riscv::support;
pub use riscv::syscall;
pub use riscv::PermissionMode;
