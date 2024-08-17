// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Google LLC 2024.

//! This file helps Tock build with stale toolchains
//! The current set of toolchains that need support are:
//! nightly-2024-07-08 (default for Tock)
//! Cheri toolchain (rust 1.67)

#[cfg(target_feature = "xcheri")]
pub mod cheri_fills {
    pub mod core {
        pub mod ptr {
            #[inline(always)]
            #[must_use]
            pub const fn from_ref<T: ?Sized>(r: &T) -> *const T {
                r
            }

            #[inline(always)]
            #[must_use]
            pub const fn from_mut<T: ?Sized>(r: &mut T) -> *mut T {
                r
            }
        }
    }
}

#[cfg(target_feature = "xcheri")]
pub use cheri_fills::*;

#[cfg(not(target_feature = "xcheri"))]
pub use core;
