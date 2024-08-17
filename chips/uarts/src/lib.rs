#![crate_name = "uarts"]
#![crate_type = "rlib"]
#![no_std]
#![feature(
    macro_metavar_expr,
    const_trait_impl,
    const_mut_refs,
    const_slice_split_at_mut
)]
#![feature(const_precise_live_drops)]

pub mod ns16550;
pub mod primecell;
mod uart;
mod uart_zero;
