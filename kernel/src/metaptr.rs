// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Google LLC 2024.

//! Defines the MetaPtr type

use core::fmt::{Formatter, LowerHex, UpperHex};
use core::ops::AddAssign;

use crate::cheri::{cheri_perms, cptr, CPtrOps};
use crate::config::CONFIG;
use crate::TIfCfg;

type InnerType = TIfCfg!(is_cheri, cptr, usize);

/// A pointer with target specific metadata.
/// This should be used any time the kernel wishes to grant authority to the user, or any time
/// the user should be required to prove validity of a pointer.
#[derive(Default, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct MetaPtr {
    ptr: InnerType,
}

#[derive(Copy, Clone, PartialEq)]
pub enum MetaPermissions {
    Any,
    Read,
    Write,
    ReadWrite,
    Execute,
}

impl From<MetaPtr> for usize {
    #[inline]
    fn from(from: MetaPtr) -> Self {
        from.ptr.cfg_into()
    }
}

impl From<usize> for MetaPtr {
    #[inline]
    fn from(from: usize) -> Self {
        Self {
            ptr: InnerType::cfg_from(from),
        }
    }
}

impl UpperHex for MetaPtr {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        UpperHex::fmt(&self.ptr, f)
    }
}

impl LowerHex for MetaPtr {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        LowerHex::fmt(&self.ptr, f)
    }
}

impl AddAssign<usize> for MetaPtr {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        self.ptr.map_mut(
            |cheri| cheri.add_assign(rhs),
            |non_cheri| non_cheri.add_assign(rhs),
        );
    }
}

impl MetaPtr {
    #[inline]
    pub fn cheri_perms_for(perms: MetaPermissions) -> usize {
        match perms {
            MetaPermissions::Any => 0,
            MetaPermissions::Read => cheri_perms::DEFAULT_R,
            MetaPermissions::Write => cheri_perms::STORE,
            MetaPermissions::ReadWrite => cheri_perms::DEFAULT_RW,
            MetaPermissions::Execute => cheri_perms::EXECUTE,
        }
    }

    #[inline]
    pub fn as_ptr(&self) -> *const () {
        self.ptr.map_ref(
            |cheri| cheri.as_ptr(),
            |non_cheri| (*non_cheri) as *const (),
        )
    }

    /// Convert to a raw pointer, checking that metadata allows a particular set of permissions over
    /// a given number of bytes.
    /// If the metadata does not allow for this, returns null.
    /// If no such metadata exists, this succeeds.
    #[inline]
    pub fn as_ptr_checked(&self, length: usize, perms: MetaPermissions) -> *const () {
        self.ptr.map_ref(
            |cheri| cheri.as_ptr_checked(length, Self::cheri_perms_for(perms)),
            |non_cheri| (*non_cheri) as *const (),
        )
    }

    #[inline]
    pub fn new_with_metadata(
        ptr: *const (),
        base: usize,
        length: usize,
        perms: MetaPermissions,
    ) -> Self {
        Self {
            ptr: if CONFIG.is_cheri {
                let mut result = cptr::default();
                if perms == MetaPermissions::Execute {
                    result.set_addr_from_pcc_restricted(ptr as usize, base, length);
                } else {
                    result.set_addr_from_ddc_restricted(
                        ptr as usize,
                        base,
                        length,
                        Self::cheri_perms_for(perms),
                    );
                }
                InnerType::new_true(result)
            } else {
                InnerType::new_false(ptr as usize)
            },
        }
    }

    #[inline]
    pub fn map_or<U, F>(&self, default: U, f: F) -> U
    where
        F: FnOnce(&Self) -> U,
    {
        let addr: usize = (*self).into();

        if addr == 0 {
            default
        } else {
            f(self)
        }
    }

    #[inline]
    pub fn map_or_else<U, D, F>(&self, default: D, f: F) -> U
    where
        D: FnOnce() -> U,
        F: FnOnce(&Self) -> U,
    {
        let addr: usize = (*self).into();

        if addr == 0 {
            default()
        } else {
            f(self)
        }
    }
}
