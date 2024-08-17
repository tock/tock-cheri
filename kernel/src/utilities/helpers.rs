// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Helper macros.

/// Create an object with the given capability.
///
/// ```ignore
/// use kernel::capabilities::ProcessManagementCapability;
/// use kernel;
///
/// let process_mgmt_cap = create_capability!(ProcessManagementCapability);
/// ```
///
/// This helper macro cannot be called from `#![forbid(unsafe_code)]` crates,
/// and is used by trusted code to generate a capability that it can either use
/// or pass to another module.
#[macro_export]
macro_rules! create_capability {
    ($T:ty $(,)?) => {{
        struct Cap;
        #[allow(unsafe_code)]
        unsafe impl $T for Cap {}
        Cap
    }};
}

/// Can create a capability with static storage.
/// Usage:
/// ```ignore
/// use kernel::capabilities::ProcessManagementCapability;
/// create_static_capability(MY_CAP = MyCap : ProcessManagementCapability);
/// ```
/// MyCap can be any type name you don't use elsewhere.
#[macro_export]
macro_rules! create_static_capability {
    (static $id : ident : $t : ident = $T:ty $(,)?) => {
        struct $t;
        #[allow(unsafe_code)]
        unsafe impl $T for $t {}
        static $id: $t = { $t };
    };
}

/// Count the number of passed expressions.
///
/// Useful for constructing variable sized arrays in other macros.
/// Taken from the Little Book of Rust Macros.
///
/// ```ignore
/// use kernel:count_expressions;
///
/// let count: usize = count_expressions!(1+2, 3+4);
/// ```
#[macro_export]
macro_rules! count_expressions {
    () => (0usize);
    ($head:expr $(,)?) => (1usize);
    ($head:expr, $($tail:expr),* $(,)?) => (1usize + count_expressions!($($tail),*));
}

/// Compute a POSIX-style CRC32 checksum of a slice.
///
/// Online calculator: <https://crccalc.com/>
pub fn crc32_posix(b: &[u8]) -> u32 {
    let mut crc: u32 = 0;

    for c in b {
        crc ^= (*c as u32) << 24;

        for _i in 0..8 {
            if crc & (0b1 << 31) > 0 {
                crc = (crc << 1) ^ 0x04c11db7;
            } else {
                crc <<= 1;
            }
        }
    }
    !crc
}

/// A safe (const) array initialisation pattern with an accumulator.
/// Usage:
/// ```ignore
///     let (acc, array) = new_const_array!([ArrayT; N], a_init, |acc, ndx| {...});
///
///     // The array will filled as if the following were written:
///     let acc = a_init;
///     let mut ndx = 0;
///     let (elem0, acc) = {...}; ndx +=1;
///     let (elem1, acc) = {...}; ndx +=1;
///     ...
///     let (elemN, acc) = {...}; ndx +=1;
///     return (acc, [elem0, elem1, ..., elemN])
/// ```
/// const fn pointer / trait bounds are still a little broken, so I have provided this as a macro
/// instead of a function.
#[macro_export]
macro_rules! new_const_array {
    ([$T : ty; $N : expr], $a_init : expr, |$acc : ident, $ndx : ident| {$($t : tt )*}) => {
        {
            const UNINIT_ELEM: MaybeUninit<$T> = MaybeUninit::uninit();
            let mut _uninit_array = [UNINIT_ELEM; $N];
            let mut $acc = $a_init;
            let mut $ndx = 0;
            while $ndx < $N {
                let (elem, next_acc) = {
                    // Shadowing the variables in this loop stops them from being modified by a
                    // naughty bit of user code.
                    let $ndx = $ndx;
                    let _uninit_array = [UNINIT_ELEM; $N];
                    {
                        $($t)*
                    }
                };
                _uninit_array[$ndx] = MaybeUninit::new(elem);
                $acc = next_acc;
                $ndx +=1;
            }
            unsafe {
                // Because the loop may have broken
                if ($ndx != $N) {
                    panic!();
                }
                // The loop above sets every element
                ($acc, MaybeUninit::array_assume_init(_uninit_array))
            }
        }
    };
}
