// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2024.

#![forbid(unsafe_code)]
#![cfg_attr(
    all(target_feature = "xcheri", feature = "use_static_init"),
    feature(const_refs_to_cell),
    feature(const_trait_impl),
    feature(macro_metavar_expr),
    feature(const_mut_refs)
)]
#![no_std]

pub mod process_checker;
pub mod process_policies;
pub mod process_printer;
pub mod storage_permissions;
