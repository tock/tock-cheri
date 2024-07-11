//! Implementations for generic SiFive MCU peripherals.

#![no_std]
#![crate_name = "sifive"]
#![crate_type = "rlib"]
#![feature(const_refs_to_cell)]
#![feature(const_trait_impl)]
#![feature(macro_metavar_expr)]
#![feature(const_mut_refs)]

pub mod clint;
pub mod gpio;
pub mod plic;
pub mod prci;
pub mod pwm;
pub mod rtc;
pub mod uart;
pub mod watchdog;
