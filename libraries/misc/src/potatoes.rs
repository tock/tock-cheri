//! Type markers for linear-types
//! Types that contain these markers should not be copied or dropped (apart from a set of methods
//! that officially consume them
//! Note that because Drop is never guaranteed to be called you should only rely on this for
//! safety if leaking the containing type is also safe.

use crate::tpanic;

#[derive(Debug)]
#[must_use]
pub struct HotPotato {
    #[cfg(feature = "track_potatoes")]
    created_at: &'static core::panic::Location<'static>,
}

/// Really just a marker to try make a type linear.
/// Sad that Rust does not have support for this statically even though this is
/// completely checked at compile time.
/// Note, currently, HotPotato can catch errors, NOT enforce safety.
/// We cannot stop users from manually dropping getting rid of the with std::mem::forget,
/// or do the same to containing types.
impl Drop for HotPotato {
    #[track_caller]
    #[inline(always)]
    fn drop(&mut self) {
        #[cfg(feature = "track_potatoes")]
        {
            tpanic!(
                "\nCreated here: {}\nDropping this is likely an error.\n",
                self.created_at
            );
        }
        #[cfg(not(feature = "track_potatoes"))]
        {
            tpanic!("Dropping this is likely an error");
        }
    }
}

impl HotPotato {
    #[inline(always)]
    pub fn consume(self) {
        core::mem::forget(self);
    }

    #[track_caller]
    pub fn new() -> HotPotato {
        HotPotato {
            #[cfg(feature = "track_potatoes")]
            created_at: core::panic::Location::caller(),
        }
    }
}

/// Debug version of HotPotato. Does not panic in release.
#[derive(Debug)]
#[must_use]
pub struct DebugPotato {
    #[cfg(feature = "track_potatoes")]
    created_at: &'static core::panic::Location<'static>,
}

impl Drop for DebugPotato {
    #[track_caller]
    #[inline(always)]
    fn drop(&mut self) {
        #[cfg(feature = "track_potatoes")]
        {
            tpanic!(
                "\nCreated here: {}\nDropping this is likely an error.\n",
                self.created_at
            );
        }
    }
}

impl DebugPotato {
    #[inline(always)]
    pub fn consume(self) {
        core::mem::forget(self);
    }

    #[track_caller]
    pub fn new() -> Self {
        Self {
            #[cfg(feature = "track_potatoes")]
            created_at: core::panic::Location::caller(),
        }
    }
}
