// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Google LLC 2024.

//! Divorce library.
//!
//! Divorcing from a type is like borrowing it, but rather than the borrow checker statically
//! verifying that the borrow does not outlive the value, you must manually "reunite" the borrow
//! (called the subset) and what was left of the original value (called the "remainder").
//!
//! To stop you from forgetting to reunite the two, or dropping the remainder too early, dropping
//! a remainder panics.
//!
//! It is intended for DMA where the foreign interfaces is very constrained (i.e. it is
//! hardware) and cannot understand the semantics of lifetimes or smart pointers, and async
//! is not available / not preferred.
//!
//! LifelessRef<> is a transparent for a raw pointer and can safely be passed to hardware.
//! However, it is safer to do so as they cannot be arbitrarily forged. The existence of a
//! LifelessRef implies the existence of another value that does have the appropriate lifetime.
//!
//! The following example shows how a driver might pass a 256 byte buffer to asynchronous hardware
//!
//! ```rust
//! use std::cell::Ref;
//! use misc::divorce::{Divorceable, Divorced, LifelessRef, Reunitable};
//!
//!
//! struct State {
//!     in_progress : Option<Divorced<Ref<'static, [u8;256]>, LifelessRef<[u8;256]>>>,
//! }
//!
//! fn pass_to_hardware(ptr : LifelessRef<[u8;256]>) {
//!   // ... program some registers for an async workload,
//!   // calls on_work_finish at some point in the future. ...
//! }
//!
//! fn work_start(state: &mut State, r: Ref<'static, [u8;256]>) {
//!     // If we just borrowed here, one of two things would have happened:
//!     // 1) The borrow would only last as long as it would take to extract a raw pointer. This
//!     // would lead to (r) being dropped at the end of the function, dropping the reference count
//!     // and leading to hardware (possibly) having a dangling pointer.
//!     // 2) The borrow would last too long, and we would get an error trying to store it to
//!     // in_progress later.
//!     // Instead, divorce gives us two types. One that we have to look after ourselves (remainder),
//!     // and one we can pass to hardware (sub).
//!     let (remainder, subset) = r.divorce();
//!     pass_to_hardware(subset);
//!     // Note, if state.in_progress were already something it would be dropped. If that were an
//!     // in progress transaction, we would get the panic as expected.
//!     state.in_progress = Some(remainder);
//!     // Had we forgotten to handle the remainder, the function would panic here to remind us we
//!     // need to store it somewhere. However, here we assigned it to state to handle later.
//! }
//!
//! // This would be called on an interrupt from the driver. The unsafe portion that bridges
//! // the gap between hardware and rust is re-constructing the "LifelessRef<[u8;256]>".
//! // The driver must "claim" (which is unsafe, as possibly it is wrong) that a particular
//! // reference has been finished with by the hardware.
//! fn on_work_finish(state: &mut State, subset : LifelessRef<[u8;256]>) {
//!     let remainder = state.in_progress.take().unwrap();
//!
//!     // We get the original reference back, with any lifetime/semantics preserved.
//!     // Reunite does its best to check that the length/address of the subset match, however
//!     // there is no provenance tracking.
//!     let original_r : Ref<'static, [u8;256]> = remainder.reunite(subset);
//! }
//! ```

use crate::divorce::private::DivorceableIntoFrom;
use crate::potatoes::HotPotato;
use core::cell::Ref;
use core::cell::{Cell, RefMut};
use core::ptr::{slice_from_raw_parts, slice_from_raw_parts_mut, NonNull};

/// A Divorced<T, S> is one that needs to be reunited with its subset S to
/// reconstruct a T before it can be dropped.
/// The intent for these are cases where some portion of a
/// type needs to be passed to an interface (such as low-level hardware)
/// which cannot understand the semantics of the larger type.
/// Once the subset has been passed back, the types can be reunited to form
/// the original.
/// This is much like a borrow, but borrows block the source from being moved, and need to be
/// verified statically. This does not work well with event based code.
/// The divorced type can be moved / stored anywhere the original T could.
/// Remainder should be a same size / aligned type as T, and can preferably be
/// T in some cases.
pub struct Divorced<T, Subset>
where
    T: Divorceable<Subset>,
{
    // Divorced types should be reunited and never dropped
    potato: HotPotato,
    value: T::Remainder,
    // A divorced type has all the lifetime requirements of T
    marker: core::marker::PhantomData<(T, Subset)>,
}

/// You cannot have a private trait in a public interface, this module is private and so protects
/// the DivorceableIntoFrom trait from use outside this module.
mod private {
    pub trait DivorceableIntoFrom<Remainder> {
        /// Convert between the T and Remainder for the Divorced type.
        fn into_divorced(self) -> Remainder;
        fn from_divorced(t2: Remainder) -> Self;
    }
}

/// Subset: The type of the subset of Self that can be divorced from it
pub trait Divorceable<Subset>: DivorceableIntoFrom<Self::Remainder> {
    /// What remains after removing the subset, although to make matches as precise as
    /// possible it should fundamentally be transmutable with Self.
    type Remainder;
    /// A handy type that is what will remain after divorcing the subset
    /// When default associated types are stable do the following:
    // type DivorceT = Divorced<Self, Subset>
    /// For now, every implementer has to do it themself.
    type DivorceT;

    /// Get the subset of the type that can be divorced from it
    fn divorceable_subset(&self) -> Subset;

    /// Divorce the subset from the type
    #[must_use]
    #[track_caller]
    fn divorce(self) -> (Divorced<Self, Subset>, Subset)
    where
        Self: Sized,
    {
        let subset = self.divorceable_subset();
        (
            Divorced::<Self, Subset> {
                potato: HotPotato::new(),
                value: self.into_divorced(),
                marker: core::marker::PhantomData,
            },
            subset,
        )
    }

    /// Safety check that a divorced subset can be reunited
    /// Because `Divorced<Self>` contains the entire `Self`,
    /// this does not allow arbitrary construction of `Self`.
    /// However, depending on whether `T` is a copyable type
    /// match may give false positives. How bad that is
    /// depends on the exact `T`. In the best case, it just
    /// gives some slightly dodgy provenance issues.
    fn matches(divorced: &Divorced<Self, Subset>, subset: &Subset) -> bool
    where
        Self: Sized;
}

/// Undo divorce. Separate trait so a default implementation can be given.
pub trait Reunitable {
    type Original;
    type With;
    /// Reunite the subset with what it was divorced from
    fn reunite(self, subset: Self::With) -> Self::Original;
}

// Default implementation for all Divorced types
impl<S, T: Divorceable<S>> Reunitable for Divorced<T, S> {
    type Original = T;
    type With = S;
    fn reunite(self, subset: S) -> T {
        assert!(Divorceable::<S>::matches(&self, &subset));
        self.potato.consume();
        T::from_divorced(self.value)
    }
}

// Where Divorced can contain the entire type, the conversion is trivial.
// The only reason the types would not be the same is if T contains references
// that need converting to pointers for the sake of soundness.
impl<T> DivorceableIntoFrom<T> for T {
    fn into_divorced(self) -> Self {
        self
    }
    fn from_divorced(s: Self) -> Self {
        s
    }
}

/// This is effectively meant to be a reference divorced from a lifetime.
/// Unlike a pointer (which has no lifetime), the lifetime of this reference is
/// just elsewhere.
/// This is a lot like a borrow of the original reference, but it allows the original value
/// can be moved around and the borrow can be of an indeterminate period.
/// These references can be passed across boundaries that do not understand lifetimes while
/// keeping some of the lifetime within rust so the compiler can spot errors.
/// The advantage over the raw pointer this wraps is that even "safe" code can
/// arbitrarily construct pointers. LifelessRefs can only be constructed by
/// divorcing them from a real reference.
/// Interfaces can therefore trust that a LifelessRef does in fact point to some valid object,
/// as somewhere else there is a type that has the correct lifetime and is not allowed to
/// go out of scope. Note, in some cases, std::mem::forget may still allow for unsafe behaviour.
/// Note, this type CANNOT be copy as it is paired with another object that would need copying too.
/// I might add a "pairwise clone" to Divorced<>
///
#[repr(transparent)]
pub struct LifelessRef<T: ?Sized> {
    value: NonNull<T>,
}
/// Same as LifelessRef, but the reference it was formed from was "mutable".
#[repr(transparent)]
pub struct LifelessRefMut<T: ?Sized> {
    value: NonNull<T>,
}

#[inline(always)]
fn split_nonnull_slice<T>(slice: NonNull<[T]>, mid: usize) -> (NonNull<[T]>, NonNull<[T]>) {
    let len = slice.len();
    assert!(mid <= len);
    let ptr = slice.as_mut_ptr();
    // SAFETY: slice was already non-null and we did the assert on length
    unsafe {
        let first = NonNull::<[T]>::new_unchecked(slice_from_raw_parts_mut(ptr, mid));
        let second =
            NonNull::<[T]>::new_unchecked(slice_from_raw_parts_mut(ptr.add(mid), len - mid));
        (first, second)
    }
}

impl<T> LifelessRef<[T]> {
    /// Number of elements in the slice
    pub fn len(&self) -> usize {
        self.value.len()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Base address of the slice
    pub fn base(&self) -> usize {
        self.value.as_ptr().as_mut_ptr() as usize
    }
    /// Split into two ranges, mid is the start of the second range
    pub fn split_at(self, mid: usize) -> (Self, Self) {
        let (first, second) = split_nonnull_slice(self.value, mid);
        (LifelessRef { value: first }, LifelessRef { value: second })
    }
    /// Get the wrapped pointer. This is not really unsafe, it is just a potential footshoot.
    /// # Safety:
    /// Do not ever actually dereference the result of this. If you want to do that,
    /// call the safe consume() method.
    pub unsafe fn peek_value(&self) -> NonNull<[T]> {
        self.value
    }
}

impl<T> LifelessRefMut<[T]> {
    /// Number of elements in the slice
    pub fn len(&self) -> usize {
        self.value.len()
    }
    /// Base address of the slice
    pub fn base(&self) -> usize {
        self.value.as_ptr().as_mut_ptr() as usize
    }
    /// Split into two ranges, mid is the start of the second range
    pub fn split_at(self, mid: usize) -> (Self, Self) {
        let (first, second) = split_nonnull_slice(self.value, mid);
        (
            LifelessRefMut { value: first },
            LifelessRefMut { value: second },
        )
    }
    /// Get the wrapped pointer. This is not really unsafe, it is just a potential footshoot.
    /// Safety: do not ever actually dereference the result of this. If you want to do that,
    /// call the safe consume() method.
    pub unsafe fn peek_value(&self) -> NonNull<[T]> {
        self.value
    }
}

impl<T, const N: usize> LifelessRef<[T; N]> {
    /// Convert array reference to slice reference
    pub fn as_slice(self) -> LifelessRef<[T]> {
        // Safety: self.value.as_ptr() will never be null as it is a NonNull
        unsafe {
            LifelessRef {
                value: NonNull::<[T]>::new_unchecked(slice_from_raw_parts(
                    self.value.as_ptr() as *const T,
                    N,
                ) as *mut [T]),
            }
        }
    }
}

impl<T, const N: usize> LifelessRefMut<[T; N]> {
    /// Convert array reference to slice reference
    pub fn as_slice(self) -> LifelessRefMut<[T]> {
        // Safety: self.value.as_ptr() will never be null as it is a NonNull
        unsafe {
            LifelessRefMut {
                value: NonNull::<[T]>::new_unchecked(core::ptr::slice_from_raw_parts_mut(
                    self.value.as_ptr() as *mut T,
                    N,
                )),
            }
        }
    }
}

/// Collection of traits that both LifelessRef and LifelessRefMut have
pub trait LifelessRefTraits<T: ?Sized> {
    // SAFETY: The caller promises they called consume on exactly the same value
    // If they did not, then the damage is still limited by the fact the ref will not match
    // what it was divorced from
    unsafe fn remake(value: NonNull<T>) -> Self;
    fn consume(self) -> NonNull<T>;
}

impl<T: ?Sized> LifelessRefTraits<T> for LifelessRef<T> {
    unsafe fn remake(value: NonNull<T>) -> Self {
        LifelessRef { value }
    }
    fn consume(self) -> NonNull<T> {
        self.value
    }
}

impl<T: ?Sized> LifelessRefTraits<T> for LifelessRefMut<T> {
    unsafe fn remake(value: NonNull<T>) -> Self {
        LifelessRefMut { value }
    }
    fn consume(self) -> NonNull<T> {
        self.value
    }
}

/// Can cast into a more general lifeless reference.
/// The way back is possibly unsafe (e.g., slice to array), but is OK to do immediately before a
/// reunite.
pub trait LifelessCast<T>: Sized {
    /// (safely) cast to a T
    fn cast(self) -> T;
    /// (possibly unsafely) cast back to the original LifelessRef type
    /// This should only be used immediately before trying to reunite with a divorced type
    unsafe fn cast_back(lifeless: T) -> Self {
        Self::try_cast_back(lifeless).unwrap()
    }
    /// Non-panicking version of cast_back. Returns None if cast would be illegal.
    unsafe fn try_cast_back(lifeless: T) -> Option<Self>;
}

// Allow downgrading a LifelessRefMut into a LifelessRef
// Possibly also apply another cast at the same time.
impl<T: ?Sized, V: ?Sized> LifelessCast<LifelessRef<V>> for LifelessRefMut<T>
where
    LifelessRef<T>: LifelessCast<LifelessRef<V>>,
{
    fn cast(self) -> LifelessRef<V> {
        self.downgrade().cast()
    }

    unsafe fn try_cast_back(lifeless: LifelessRef<V>) -> Option<Self> {
        Some(LifelessRef::<T>::try_cast_back(lifeless)?.upgrade())
    }
}

// Allow upgrading a LifelessRef into a LifelessRefMut if the reference is to a cell slice
// Possibly make another cast first.
// This is not valid for normal rust, e.g.:  &'a mut [u8]  =/= &'a [Cell<u8>] because although
// they both represent a variable length span of mutable bytes, the LHS cannot alias with any
// other reference in the rust type system, and the RHS can.
// For hardware, they are the same because hardware has no rules on aliasing.
impl<T, V: ?Sized> LifelessCast<LifelessRefMut<[T]>> for LifelessRef<V>
where
    LifelessRef<V>: LifelessCast<LifelessRef<[Cell<T>]>>,
{
    fn cast(self) -> LifelessRefMut<[T]> {
        // Cast first to LifelessRef<[Cell<T>]>
        let cast: LifelessRef<[Cell<T>]> = self.cast();
        // Then to LifelessRefMut<[T]>
        LifelessRefMut {
            value: NonNull::slice_from_raw_parts(cast.value.cast(), cast.value.len()),
        }
    }

    unsafe fn try_cast_back(lifeless: LifelessRefMut<[T]>) -> Option<Self> {
        let lr = LifelessRef {
            value: NonNull::slice_from_raw_parts(lifeless.value.cast(), lifeless.value.len()),
        };
        LifelessRef::<V>::try_cast_back(lr)
    }
}

// Implement cast for LifelessRef
impl<Into: ?Sized, From: LifelessCastEither<Into> + ?Sized> LifelessCast<LifelessRef<Into>>
    for LifelessRef<From>
{
    fn cast(self) -> LifelessRef<Into> {
        LifelessRef {
            value: From::cast_either(self.value),
        }
    }

    unsafe fn try_cast_back(lifeless: LifelessRef<Into>) -> Option<Self> {
        Some(LifelessRef {
            value: From::try_cast_back_either(lifeless.value)?,
        })
    }
}
// And again for mut
impl<Into: ?Sized, From: LifelessCastEither<Into> + ?Sized> LifelessCast<LifelessRefMut<Into>>
    for LifelessRefMut<From>
{
    fn cast(self) -> LifelessRefMut<Into> {
        LifelessRefMut {
            value: From::cast_either(self.value),
        }
    }

    unsafe fn try_cast_back(lifeless: LifelessRefMut<Into>) -> Option<Self> {
        Some(LifelessRefMut {
            value: From::try_cast_back_either(lifeless.value)?,
        })
    }
}

/// Implement once for use by different wrappers LifelessRef and LifelessRefMut
pub trait LifelessCastEither<Into: ?Sized> {
    fn cast_either(value: NonNull<Self>) -> NonNull<Into>;
    fn cast_back_either(value: NonNull<Into>) -> NonNull<Self>;
    fn try_cast_back_either(value: NonNull<Into>) -> Option<NonNull<Self>> {
        Some(Self::cast_back_either(value))
    }
}

// Allow identity cast
impl<T: ?Sized> LifelessCastEither<T> for T {
    fn cast_either(value: NonNull<Self>) -> NonNull<T> {
        value
    }

    fn cast_back_either(value: NonNull<T>) -> NonNull<Self> {
        value
    }
}

// Allow casting array to slice
impl<T, const N: usize> LifelessCastEither<[T]> for [T; N] {
    fn cast_either(value: NonNull<Self>) -> NonNull<[T]> {
        NonNull::slice_from_raw_parts(value.cast(), N)
    }

    fn cast_back_either(value: NonNull<[T]>) -> NonNull<Self> {
        assert_eq!(value.len(), N);
        value.cast()
    }

    fn try_cast_back_either(value: NonNull<[T]>) -> Option<NonNull<Self>> {
        if value.len() != N {
            None
        } else {
            Some(value.cast())
        }
    }
}

/// Allow discarding the `Cell` in `[Cell<T>]`. Hardware does not understand any semantics of interior
/// mutability.
impl<T> LifelessCastEither<[T]> for [Cell<T>] {
    fn cast_either(value: NonNull<Self>) -> NonNull<[T]> {
        NonNull::slice_from_raw_parts(value.cast(), value.len())
    }

    fn cast_back_either(value: NonNull<[T]>) -> NonNull<Self> {
        NonNull::slice_from_raw_parts(value.cast(), value.len())
    }
}

impl<T: ?Sized> LifelessRefMut<T> {
    /// Downgrade a `LifelessRefMut<T>` into `LifelessRef<T>`
    pub fn downgrade(self) -> LifelessRef<T> {
        LifelessRef { value: self.value }
    }
}

impl<T: ?Sized> LifelessRef<T> {
    /// Upgrading is unsafe if not called on a value that was originally a LifelessRefMut
    pub unsafe fn upgrade(self) -> LifelessRefMut<T> {
        LifelessRefMut { value: self.value }
    }
}

/// Implement divorcing lifeless refs from normal references

impl<T: ?Sized> DivorceableIntoFrom<NonNull<T>> for &T {
    fn into_divorced(self) -> NonNull<T> {
        self.into()
    }
    fn from_divorced(d: NonNull<T>) -> Self {
        // Will not be NULL as it was constructed from as_ptr
        // into_divorced also consumed the reference, so the borrow checker
        // will not allow there to be any mutable references
        unsafe { d.as_ref() }
    }
}

impl<T: ?Sized> Divorceable<LifelessRef<T>> for &T {
    type Remainder = NonNull<T>;
    type DivorceT = Divorced<Self, LifelessRef<T>>;

    fn divorceable_subset(&self) -> LifelessRef<T> {
        LifelessRef {
            value: (*self).into(),
        }
    }
    fn matches(divorced: &Divorced<Self, LifelessRef<T>>, subset: &LifelessRef<T>) -> bool {
        core::ptr::eq(subset.value.as_ptr(), divorced.value.as_ptr())
    }
}

/// A helper trait for anything that is `Divorceable<T>`,
/// where `T` is a `LifelessRef` or `LifelessRefMut`
pub trait DivorceLifeless: Divorceable<Self::Lifeless> {
    type InnerT: ?Sized;
    type Lifeless: LifelessRefTraits<Self::InnerT>;
}

impl<T: ?Sized> DivorceLifeless for &T {
    type InnerT = T;
    type Lifeless = LifelessRef<T>;
}

impl<T: ?Sized> DivorceableIntoFrom<NonNull<T>> for &mut T {
    fn into_divorced(self) -> NonNull<T> {
        self.into()
    }
    fn from_divorced(mut d: NonNull<T>) -> Self {
        // Will not be NULL as it was constructed from as_ptr
        // into_divorced also consumed the reference, so the borrow checker
        // will not allow there to be any mutable references
        unsafe { d.as_mut() }
    }
}

impl<T: ?Sized> Divorceable<LifelessRefMut<T>> for &mut T {
    type Remainder = NonNull<T>;
    type DivorceT = Divorced<Self, LifelessRefMut<T>>;

    fn divorceable_subset(&self) -> LifelessRefMut<T> {
        LifelessRefMut {
            value: (*self as &T).into(),
        }
    }
    fn matches(divorced: &Divorced<Self, LifelessRefMut<T>>, subset: &LifelessRefMut<T>) -> bool {
        core::ptr::eq(subset.value.as_ptr(), divorced.value.as_ptr())
    }
}

impl<T: ?Sized> DivorceLifeless for &mut T {
    type InnerT = T;
    type Lifeless = LifelessRefMut<T>;
}

/// Implement divorcing lifeless refs from Ref<>

impl<'a, T: 'a + ?Sized> Divorceable<LifelessRef<T>> for Ref<'a, T> {
    type Remainder = Ref<'a, T>;
    type DivorceT = Divorced<Self, LifelessRef<T>>;

    fn divorceable_subset(&self) -> LifelessRef<T> {
        LifelessRef {
            value: (&**self).into(),
        }
    }
    fn matches(divorced: &Divorced<Self, LifelessRef<T>>, subset: &LifelessRef<T>) -> bool {
        core::ptr::eq(
            subset.value.as_ptr(),
            divorced.value.divorceable_subset().value.as_ptr(),
        )
    }
}

impl<'a, T: 'a + ?Sized> DivorceLifeless for Ref<'a, T> {
    type InnerT = T;
    type Lifeless = LifelessRef<T>;
}

impl<'a, T: 'a + ?Sized> Divorceable<LifelessRefMut<T>> for RefMut<'a, T> {
    type Remainder = RefMut<'a, T>;
    type DivorceT = Divorced<Self, LifelessRefMut<T>>;

    fn divorceable_subset(&self) -> LifelessRefMut<T> {
        LifelessRefMut {
            value: (&**self).into(),
        }
    }
    fn matches(divorced: &Divorced<Self, LifelessRefMut<T>>, subset: &LifelessRefMut<T>) -> bool {
        core::ptr::eq(
            subset.value.as_ptr(),
            divorced.value.divorceable_subset().value.as_ptr(),
        )
    }
}

impl<'a, T: 'a + ?Sized> DivorceLifeless for RefMut<'a, T> {
    type InnerT = T;
    type Lifeless = LifelessRefMut<T>;
}

#[cfg(test)]
mod tests {
    use crate::divorce::{Divorceable, LifelessRef, Reunitable};
    use core::cell::RefCell;

    fn test_ptr(l: LifelessRef<i32>, compare: i32) -> LifelessRef<i32> {
        let as_ref = unsafe { l.value.as_ref() };
        assert_eq!(*as_ref, compare);
        l
    }

    #[test]
    fn test_normal_ref() {
        let val: i32 = 77;
        let r = &val;
        let (remain, lifeless) = r.divorce();
        let lifeless = test_ptr(lifeless, 77);
        remain.reunite(lifeless);
    }

    #[test]
    #[should_panic]
    fn test_normal_forget_reunite() {
        let val: i32 = 77;
        let r = &val;
        let (_remain, _lifeless) = r.divorce();
    }

    #[test]
    fn test_refcell() {
        let val_cell = RefCell::new(77);
        let r = val_cell.borrow();
        let (remain, lifeless) = r.divorce();
        let lifeless = test_ptr(lifeless, 77);
        remain.reunite(lifeless);
    }
}
