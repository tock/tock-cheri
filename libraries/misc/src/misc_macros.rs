// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Google LLC 2024.

//! Contains lots of small macros that don't really belong anywhere else

/// This macro is horrendously unsafe and intended just for testing
/// When you call this, you are making the declaration that nothing derived from this
/// reference will ever be shared between threads.
/// For testing, if you have no global state apart from that within thread_local!, this is true.
#[macro_export]
macro_rules! leak_thread_local {
    ($e : expr) => {
        ($e).with(|re| core::ptr::NonNull::from(re)).as_ref()
    };
}
