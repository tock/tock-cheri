#![feature(nonnull_slice_from_raw_parts)]
#![feature(slice_ptr_len)]
#![feature(slice_ptr_get)]
#![feature(const_trait_impl)]
#![crate_type = "rlib"]
#![no_std]

pub mod const_env;
pub mod default_array;
pub mod divorce;
pub mod misc_macros;
pub mod never;
pub mod overload_impl;
pub mod potatoes;
pub mod take_borrow;
pub mod tpanic;
pub mod trait_alias;
pub mod unsigned_allocators;
