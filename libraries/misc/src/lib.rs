// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Google LLC 2024.

#![feature(slice_ptr_get)]
#![cfg_attr(
    target_feature = "xcheri",
    feature(slice_ptr_len),
    feature(nonnull_slice_from_raw_parts)
)]
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
