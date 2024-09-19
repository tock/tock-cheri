// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Google LLC 2024.

/// A panic that interacts better with testing.
/// If we are running unit tests and already panicking, this prints the message but does not panic.
/// Otherwise, it will panic as normal.
/// This behaviour can be configured when testing other creates using the global_test feature.
#[macro_export]
macro_rules! tpanic {
    ($($t : tt)*) => {
        {
            #[cfg(any(test, feature = "global_test"))]
            {
                extern crate std;
                if std::thread::panicking() {
                    std::println!($($t)*);
                } else {
                    panic!($($t)*);
                }
            }
            #[cfg(not(any(test, feature = "global_test")))]
            {
                panic!($($t)*);
            }
        }
    };
}
