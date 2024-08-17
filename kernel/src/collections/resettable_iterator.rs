//! Provides traits (and implementations for some collections) for two new iterator-like interfaces
//! Resettable iterators support a reset method to re-obtain the collection from the iterator.
//! This is useful for when a borrow would not suffice because there is no sensible scope in which
//! the borrow could occur.
//! It also adds chasing iterators, which are two iterators through the same collection where one
//! chases the other. The chasing iterator returns none when it has returned every item the first
//! iterator has. If more items are taken from the first iterator, the chasing iterator will have
//! new items.

use crate::collections::resettable_iterator::private::IntoRawHelper;
use crate::grant::{PRefBase, Track};
use core::cell::{Ref, RefMut};
use core::marker::PhantomData;

mod private {
    use core::cell::{Ref, RefMut};
    use core::ptr::NonNull;

    /// Has a raw representation
    pub trait IntoRawHelper<'a, T: ?Sized> {
        type Output;
        type RefT;
        /// SAFETY: Convert self into a raw form, and also return a reference. It is up to the caller to ensure
        /// that when from_raw_mut is called, nothing derived from the reference exists.
        /// It is also up to the caller to ensure that the &'a T does not outlive the Output.
        unsafe fn into_raw(self) -> (Self::Output, Self::RefT);
        /// SAFETY: See into_raw_mut
        unsafe fn from_raw(raw: Self::Output) -> Self;
    }

    impl<'a, T: ?Sized> IntoRawHelper<'a, T> for &'a mut T {
        type Output = NonNull<T>;
        type RefT = &'a mut T;
        unsafe fn into_raw(self) -> (Self::Output, &'a mut T) {
            (self.into(), self)
        }
        unsafe fn from_raw(mut raw: Self::Output) -> Self {
            raw.as_mut()
        }
    }

    impl<'a, T: ?Sized> IntoRawHelper<'a, T> for RefMut<'a, T> {
        type Output = Self;
        type RefT = &'a mut T;

        unsafe fn into_raw(self) -> (Self::Output, Self::RefT) {
            let mut ptr: Option<NonNull<T>> = None;
            // Take the reference out the smart pointer.
            // Soundness: this is a little dodgy. Internally, Ref and RefMut use raw pointers,
            // so it is sound to make an actual rust reference, as long as we don't make another,
            // which we won't. However, it is worth noting that if the internals of Ref change,
            // then this suddenly becomes unsound
            let unchanged = RefMut::map(self, |as_ref| {
                ptr = Some(as_ref.into());
                as_ref
            });
            let mut ptr = ptr.unwrap_unchecked();
            (unchanged, ptr.as_mut())
        }

        unsafe fn from_raw(raw: Self::Output) -> Self {
            raw
        }
    }

    impl<'a, T: ?Sized> IntoRawHelper<'a, T> for Ref<'a, T> {
        type Output = Self;
        type RefT = &'a T;
        unsafe fn into_raw(self) -> (Self::Output, Self::RefT) {
            let mut ptr: Option<NonNull<T>> = None;
            // Take the reference out the smart pointer.
            // Soundness: see into_raw_mut
            let unchanged = Ref::map(self, |as_ref| {
                ptr = Some(as_ref.into());
                as_ref
            });
            let ptr = ptr.unwrap_unchecked();
            (unchanged, ptr.as_ref())
        }

        unsafe fn from_raw(raw: Self::Output) -> Self {
            raw
        }
    }
}

/// Boilerplate to declare a useful alias for a resettable iterator where the item obeys some bounds
/// Usage:
///     declare_chasing_resettable_x_iterator!(
///         NewIterator   <--- A new trait that is a ResettableIterator plus some bounds on its items
///         SomeUniqueName <--- any type name you have not used before
///         NewIteratorInto <--- A new trait that is a IntoResettableIterator plus some bounds on its items
///         Bounds <--- the bounds (on items) implied by using the new NewIterator and NewIteratorInto traits
///     );
/// e.g.:
/// declare_chasing_resettable_x_iterator!(
///         FooIterator,
///         BlahBlah,
///         IntoFooIterator,
///         Foo);
///
/// will create two new traits: FooIterator and IntoFooIterator. These will have supertraits of
/// ResettableIterator and IntoResettableIterator (respectively), with the included bounds on items
/// of Foo.
#[macro_export]
macro_rules! declare_resettable_x_iterator {
    ($name : ident, $nameType : ident, $nameInto : ident, $($bounds : tt)*) => {
        pub trait $nameType<'a, ImplicitBound = &'a Self> : $crate::collections::resettable_iterator::ResettableIteratorTypes<'a, ImplicitBound, ItemType = Self::ItemTypeBounded> {
            type ItemTypeBounded : $($bounds)*;
        }
        impl<'a, T : $crate::collections::resettable_iterator::ResettableIteratorTypes<'a>> $nameType<'a> for T where <Self as $crate::collections::resettable_iterator::ResettableIteratorTypes<'a>>::ItemType : $($bounds)* {
            type ItemTypeBounded = <Self as $crate::collections::resettable_iterator::ResettableIteratorTypes<'a>>::ItemType;
        }
        pub trait $name : $crate::collections::resettable_iterator::ResettableIterator + for<'a> $nameType<'a> {}
        impl< T : $crate::collections::resettable_iterator::ResettableIterator + for<'a> $nameType<'a>> $name for T {}
        pub trait $nameInto : $crate::collections::resettable_iterator::IntoResettableIterator<ResetIterType = Self::ResetIterTypeBounded> {
            type ResetIterTypeBounded : $name<CollectionType = Self>;
        }
        impl< T : $crate::collections::resettable_iterator::IntoResettableIterator> $nameInto for T where <Self as $crate::collections::resettable_iterator::IntoResettableIterator>::ResetIterType : $name {
            type ResetIterTypeBounded = <Self as $crate::collections::resettable_iterator::IntoResettableIterator>::ResetIterType;
        }
    };
}

/// Boilerplate to declare a useful alias for a chasing resettable iterator where the item obeys some bounds
/// See comment on declare_resettable_x_iterator
#[macro_export]
macro_rules! declare_chasing_resettable_x_iterator {
    ($name : ident, $nameType : ident, $nameInto : ident, $($bounds : tt)*) => {
        pub trait $nameType<'a, ImplicitBound = &'a Self> : $crate::collections::resettable_iterator::ResettableIteratorTypes<'a, ImplicitBound, ItemType = Self::ItemTypeBounded> {
            type ItemTypeBounded : $($bounds)*;
        }
        impl<'a, T : $crate::collections::resettable_iterator::ResettableIteratorTypes<'a>> $nameType<'a> for T where <Self as $crate::collections::resettable_iterator::ResettableIteratorTypes<'a>>::ItemType : $($bounds)* {
            type ItemTypeBounded = <Self as $crate::collections::resettable_iterator::ResettableIteratorTypes<'a>>::ItemType;
        }
        pub trait $name : $crate::collections::resettable_iterator::ResettableIterator + $crate::collections::resettable_iterator::ChasingResettableIterator + for<'a> $nameType<'a> {}
        impl< T : $crate::collections::resettable_iterator::ResettableIterator + $crate::collections::resettable_iterator::ChasingResettableIterator + for<'a> $nameType<'a>> $name for T {}
        pub trait $nameInto : $crate::collections::resettable_iterator::IntoChasingResettableIterator<ChasingResetIterType = Self::ChasingResetIterTypeBounded> {
            type ChasingResetIterTypeBounded : $name<CollectionType = Self>;
        }
        impl< T : $crate::collections::resettable_iterator::IntoChasingResettableIterator> $nameInto for T where <Self as $crate::collections::resettable_iterator::IntoChasingResettableIterator>::ChasingResetIterType : $name {
            type ChasingResetIterTypeBounded = <Self as $crate::collections::resettable_iterator::IntoChasingResettableIterator>::ChasingResetIterType;
        }
    };
}

/// Can be converted into a resettable iterator
pub trait IntoResettableIterator {
    /// The type of the Resettable iterator
    type ResetIterType: ResettableIterator<CollectionType = Self>;
    fn into_resettable_iterator(self) -> Self::ResetIterType;
}

/// Can be converted into a resettable iterator that has two streams.
/// The chasing iterator returns items only after they have been returned by the first.
pub trait IntoChasingResettableIterator {
    /// The type of the Resettable iterator
    type ChasingResetIterType: ChasingResettableIterator<CollectionType = Self>;
    fn into_chasing_resettable_iterator(self) -> Self::ChasingResetIterType;
}

/// The types of the iterator and item for a &'a mut ResettableIterator.
/// The implicit bound obviates the need for a Self : 'a, which causes problems with GATS, which
/// cannot in general have associated lifetimes.
pub trait ResettableIteratorTypes<'a, ImplicitBound = &'a Self> {
    type ItemType;
    type IterType: Iterator<Item = Self::ItemType>;
}

/// An iterator that can be consumed to return the collection that formed it.
/// More specifically, any borrow of this is an iterator, even if possibly a ResettableIterator
/// is also an iterator.
/// The extra layer of indirection is offered in case the items need a shorter lifetime ('a).
pub trait ResettableIterator: for<'a> ResettableIteratorTypes<'a> {
    type CollectionType;
    fn reset(self) -> Self::CollectionType;
    fn iter(&mut self) -> <Self as ResettableIteratorTypes<'_>>::IterType;
}

pub trait ChasingResettableIteratorTypes<'a, ImplicitBound = &'a Self>:
    ResettableIteratorTypes<'a, ImplicitBound>
{
    type ChasingIterType: Iterator<Item = Self::ItemType>;
}

pub trait ChasingResettableIterator:
    ResettableIterator + for<'a> ChasingResettableIteratorTypes<'a>
{
    /// Get an iterator that chases the first iterator.
    /// Will only returns items that have previously been returned (and then gone out of lifetime)
    /// from the lead iterator.
    fn chasing_iter(&mut self) -> <Self as ChasingResettableIteratorTypes<'_>>::ChasingIterType;
    /// Peek the next item from the chasing iterator
    fn chasing_peek(&mut self) -> Option<<Self as ResettableIteratorTypes<'_>>::ItemType>;
    /// Peek the next item from the lead iterator
    fn lead_peek(&mut self) -> Option<<Self as ResettableIteratorTypes<'_>>::ItemType>;
}

pub struct ResettableOnce<T> {
    used: bool,
    value: T,
}

impl<T> ResettableOnce<T> {
    pub fn new(value: T) -> Self {
        Self { used: false, value }
    }
}

impl<'a, T> Iterator for &'a mut ResettableOnce<T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.used {
            None
        } else {
            self.used = true;
            // Safety: this transmutes the lifetime of the reference of self.value from that of the
            // &mut self to that of 'a. Even though self can borrowed several times for different
            // lifetimes shorter than 'a, because this iterator only returns the item once, it is
            // always fine to do for this longer lifetime.
            let item: &mut T = &mut self.value;
            unsafe { Some(core::mem::transmute(item)) }
        }
    }
}

impl<'a, T> ResettableIteratorTypes<'a> for ResettableOnce<T> {
    type ItemType = <&'a mut Self as Iterator>::Item;
    type IterType = &'a mut Self;
}

impl<T> ResettableIterator for ResettableOnce<T> {
    type CollectionType = T;

    fn reset(self) -> Self::CollectionType {
        self.value
    }

    fn iter(&mut self) -> <Self as ResettableIteratorTypes<'_>>::IterType {
        self
    }
}

enum ChasingResettableOnceState {
    /// Neither iterator has returned the item
    None,
    /// The first iterator has returned the item
    First,
    /// The second iterator has returned the item
    Second,
}

pub struct ChasingResettableOnce<T> {
    state: ChasingResettableOnceState,
    value: T,
}

impl<T> ChasingResettableOnce<T> {
    pub fn new(value: T) -> Self {
        Self {
            state: ChasingResettableOnceState::None,
            value,
        }
    }
}

pub struct ChasingResettableOnceChaser<'a, T> {
    r: &'a mut ChasingResettableOnce<T>,
}

impl<'a, T> ChasingResettableOnceChaser<'a, T> {
    fn next_helper(&mut self, advance: bool) -> Option<&'a mut T> {
        match self.r.state {
            ChasingResettableOnceState::First => {
                if advance {
                    self.r.state = ChasingResettableOnceState::Second;
                }
                let item: &mut T = &mut self.r.value;
                // Safety : similar to getting it the first time. Constructing this chaser requires
                // the other iter to have been dropped, and so the item from it is also out of
                // scope.
                unsafe { Some(core::mem::transmute(item)) }
            }
            _ => None,
        }
    }
}

impl<'a, T> Iterator for ChasingResettableOnceChaser<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_helper(true)
    }
}

impl<'a, T> Iterator for &'a mut ChasingResettableOnce<T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.state {
            ChasingResettableOnceState::None => {
                self.state = ChasingResettableOnceState::First;
                // Safety: this transmutes the lifetime of the reference of self.value from that of the
                // &mut self to that of 'a. Even though self can borrowed several times for different
                // lifetimes shorter than 'a, because this iterator only returns the item once, it is
                // always fine to do for this longer lifetime.
                // It will be returned by the other iterator, but that cannot exist at the same time
                // as this time because constructing it requires borrowing the ChasingResettableOnce
                // mutably.
                let item: &mut T = &mut self.value;
                unsafe { Some(core::mem::transmute(item)) }
            }
            _ => None,
        }
    }
}

impl<'a, T> ResettableIteratorTypes<'a> for ChasingResettableOnce<T> {
    type ItemType = <&'a mut Self as Iterator>::Item;
    type IterType = &'a mut Self;
}

impl<'a, T> ChasingResettableIteratorTypes<'a> for ChasingResettableOnce<T> {
    type ChasingIterType = ChasingResettableOnceChaser<'a, T>;
}

impl<T> ResettableIterator for ChasingResettableOnce<T> {
    type CollectionType = T;

    fn reset(self) -> Self::CollectionType {
        self.value
    }

    fn iter(&mut self) -> <Self as ResettableIteratorTypes<'_>>::IterType {
        self
    }
}

impl<T> ChasingResettableIterator for ChasingResettableOnce<T> {
    fn chasing_iter<'a>(
        &'a mut self,
    ) -> <Self as ChasingResettableIteratorTypes<'a>>::ChasingIterType {
        ChasingResettableOnceChaser::<'a, T> { r: self }
    }

    fn chasing_peek<'a>(&'a mut self) -> Option<<Self as ResettableIteratorTypes<'a>>::ItemType> {
        ChasingResettableOnceChaser::<'a, T> { r: self }.next_helper(false)
    }

    fn lead_peek(&mut self) -> Option<<Self as ResettableIteratorTypes<'_>>::ItemType> {
        match self.state {
            ChasingResettableOnceState::None => Some(&mut self.value),
            _ => None,
        }
    }
}

/// Simple case where the original reference and an iterator can be be stored as a pair,
/// to be used when the RefT can be copied.
pub struct IterReset<RefT, IterT: Iterator> {
    orig_ref: RefT,
    the_iter: IterT,
}

// Sadly I have to copy this implementation for lots of T because negative impls/bounds
// specialisation do not work yet and a different implementation is needed for non-copy types.
macro_rules! define_into_resettable_iterator {
    ($T : ty, $($tok:tt)*) => {
        // Where we can cheaply copy a IntoIterator T we can just stash that copy
        impl<$($tok)*> IntoResettableIterator for $T
            where $T : Copy + IntoIterator
        {
            type ResetIterType = IterReset<$T, <$T as IntoIterator>::IntoIter>;

            fn into_resettable_iterator(self) ->  Self::ResetIterType {
                Self::ResetIterType {orig_ref: self, the_iter: self.into_iter()}
            }
        }
    }
}

define_into_resettable_iterator!(&'a T, 'a, T: ? Sized + 'a);

/// IterReset is an iterator itself, so will also automatically support &mut Self : IntoIterator
impl<RefT, IterT: Iterator> Iterator for IterReset<RefT, IterT> {
    type Item = IterT::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.the_iter.next()
    }
}

impl<'a, RefT, IterT: Iterator> ResettableIteratorTypes<'a> for IterReset<RefT, IterT>
where
    RefT: IntoResettableIterator<ResetIterType = Self>,
{
    type ItemType = <&'a mut Self as Iterator>::Item;
    type IterType = &'a mut Self;
}

/// Unwrap copy discarding the iterator
impl<RefT, IterT: Iterator> ResettableIterator for IterReset<RefT, IterT>
where
    RefT: IntoResettableIterator<ResetIterType = Self>,
{
    type CollectionType = RefT;
    fn reset(self) -> Self::CollectionType {
        self.orig_ref
    }

    fn iter(&mut self) -> <Self as ResettableIteratorTypes<'_>>::IterType {
        self
    }
}

pub struct IterChaseReset<RefT, IterT: Iterator>
where
    IterT::Item: Clone,
{
    orig_ref: RefT,
    the_iter: IterT,
    the_chaser: IterT,
    chase_peeked: Option<IterT::Item>,
    lead_peeked: Option<IterT::Item>,
    count: usize,
}

pub struct IterChaseResetRef<'a, RefT, IterT: Iterator>
where
    IterT::Item: Clone,
{
    the_ref: &'a mut IterChaseReset<RefT, IterT>,
}

impl<T> IntoChasingResettableIterator for T
where
    T: Clone + IntoIterator,
    T::Item: Clone,
{
    type ChasingResetIterType = IterChaseReset<T, <T as IntoIterator>::IntoIter>;

    fn into_chasing_resettable_iterator(self) -> Self::ChasingResetIterType {
        Self::ChasingResetIterType {
            orig_ref: self.clone(),
            the_iter: self.clone().into_iter(),
            the_chaser: self.into_iter(),
            chase_peeked: None,
            lead_peeked: None,
            count: 0,
        }
    }
}

impl<RefT, IterT: Iterator> Iterator for IterChaseReset<RefT, IterT>
where
    IterT::Item: Clone,
{
    type Item = IterT::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.lead_peeked.is_some() {
            return self.lead_peeked.take();
        }
        self.count += 1;
        self.the_iter.next()
    }
}

impl<'a, RefT, IterT: Iterator> Iterator for IterChaseResetRef<'a, RefT, IterT>
where
    IterT::Item: Clone,
{
    type Item = IterT::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.the_ref.chase_peeked.is_some() {
            return self.the_ref.chase_peeked.take();
        }
        if self.the_ref.count == 0 {
            None
        } else {
            self.the_ref.count -= 1;
            self.the_ref.the_chaser.next()
        }
    }
}

impl<'a, RefT, IterT: Iterator> ResettableIteratorTypes<'a> for IterChaseReset<RefT, IterT>
where
    RefT: IntoChasingResettableIterator<ChasingResetIterType = Self>,
    IterT::Item: Clone,
{
    type ItemType = <&'a mut Self as Iterator>::Item;
    type IterType = &'a mut Self;
}
impl<'a, RefT, IterT: Iterator> ChasingResettableIteratorTypes<'a> for IterChaseReset<RefT, IterT>
where
    RefT: IntoChasingResettableIterator<ChasingResetIterType = Self>,
    IterT::Item: Clone,
{
    type ChasingIterType = IterChaseResetRef<'a, RefT, IterT>;
}
impl<RefT, IterT: Iterator> ResettableIterator for IterChaseReset<RefT, IterT>
where
    RefT: IntoChasingResettableIterator<ChasingResetIterType = Self>,
    IterT::Item: Clone,
{
    type CollectionType = RefT;
    fn reset(self) -> Self::CollectionType {
        self.orig_ref
    }

    fn iter(&mut self) -> <Self as ResettableIteratorTypes<'_>>::IterType {
        self
    }
}
impl<RefT, IterT: Iterator> ChasingResettableIterator for IterChaseReset<RefT, IterT>
where
    RefT: IntoChasingResettableIterator<ChasingResetIterType = Self>,
    IterT::Item: Clone,
{
    fn chasing_iter<'a>(
        &'a mut self,
    ) -> <Self as ChasingResettableIteratorTypes<'_>>::ChasingIterType {
        IterChaseResetRef::<'a, RefT, IterT> { the_ref: self }
    }

    fn chasing_peek(&mut self) -> Option<<Self as ResettableIteratorTypes<'_>>::ItemType> {
        if !self.chase_peeked.is_some() && self.count != 0 {
            self.count -= 1;
            self.chase_peeked = self.the_chaser.next();
        }
        self.chase_peeked.clone()
    }

    fn lead_peek(&mut self) -> Option<<Self as ResettableIteratorTypes<'_>>::ItemType> {
        if !self.lead_peeked.is_some() {
            self.count += 1;
            self.lead_peeked = self.the_iter.next();
        }
        self.lead_peeked.clone()
    }
}

/// A more complicated wrapper for mutable iterators
pub struct MutIterReset<RefTWrapped, Phantom, IterT> {
    /// The iterator. It may return items with overly permissive lifetimes ('i).
    the_iter: IterT,
    /// A sound type to store the original collection (likely as a raw pointer)
    /// Even if we don't use it we are not allowed to have any aliased mutable references.
    orig: RefTWrapped,
    /// In case orig loses any important lifetime information
    _phantom: Phantom,
}

macro_rules! declare_resettable_iter_mut {
    ($a: lifetime, $i : lifetime, $c : lifetime, $T : ident, $X : ty, $IT : ty, $SIT : ty) => {
        /// Implement for any mutable reference where that mutable reference can be an iterator
        impl<$i, $c: $i, $T : ?Sized, ItemT: $i, IterT : Iterator<Item = $IT>> IntoResettableIterator for $X
            where <Self as IntoRawHelper<$c, $T>>::RefT : IntoIterator<IntoIter = IterT> {
            type ResetIterType = MutIterReset<<Self as IntoRawHelper<$c, $T>>::Output, PhantomData<($X, &$c $T, &$i ItemT)>, IterT>;

            fn into_resettable_iterator(self) -> Self::ResetIterType {
                // Safety: the_iter will be dropped first if this type is dropped
                // references can only leak via next, which shortens the lifetime of references.
                let (orig, reff) = unsafe { self.into_raw() };
                Self::ResetIterType {orig, _phantom : PhantomData, the_iter : reff.into_iter()}
            }
        }
        /// Implement iterator for mutable reference, must shorten the lifetime of items to that of
        /// the iterator reference.
        impl<$a, $c, $i, $T: ?Sized, ItemT: $i, IterT : Iterator<Item = $IT>, OrigT> Iterator for
                &$a mut MutIterReset<OrigT, PhantomData<($X, &$c $T, &$i ItemT)>, IterT> {
            type Item = $SIT;

            fn next(&mut self) -> Option<Self::Item> {
                // This is a reference with lifetime 'i.
                self.the_iter.next()
                // Which will shorten to 'a, the lifetime of the borrow of MutIterReset
                // this ensure that if we consume MutIterReset, no references will exist.
            }
        }
    };
}

declare_resettable_iter_mut!('a, 'i, 'c, T, &'c mut T, &'i mut ItemT, &'a mut ItemT);
declare_resettable_iter_mut!('a, 'i, 'c, T, RefMut<'c, T>, &'i mut ItemT, &'a mut ItemT);
declare_resettable_iter_mut!('a, 'i, 'c, T, Ref<'c, T>, &'i ItemT, &'a ItemT);

impl<'a, 'c, 'i, T: ?Sized, ItemT: 'i, IterT, X: IntoRawHelper<'c, T>> ResettableIteratorTypes<'a>
    for MutIterReset<X::Output, PhantomData<(X, &'c T, &'i ItemT)>, IterT>
where
    &'a mut Self: Iterator,
{
    type ItemType = <&'a mut Self as Iterator>::Item;
    type IterType = &'a mut Self;
}

impl<'c, 'i, T: ?Sized, ItemT: 'i, IterT: Iterator, X: IntoRawHelper<'c, T>> ResettableIterator
    for MutIterReset<X::Output, PhantomData<(X, &'c T, &'i ItemT)>, IterT>
where
    for<'a> &'a mut Self: Iterator,
{
    type CollectionType = X;

    fn reset(self) -> Self::CollectionType {
        // Just in case dropping the iterator references itself
        drop(self.the_iter);
        // SAFETY: any items provided via next are bounded by a lifetime from a borrow of self
        // because this method consumes self, those will all have gone out of scope by now
        // Orig was also cast from a valid reference, and the phantom data ensures that the
        // lifetime is still valid.
        unsafe { X::from_raw(self.orig) }
    }

    fn iter(&mut self) -> <Self as ResettableIteratorTypes<'_>>::IterType {
        self
    }
}

/// Resettable Iterator for PRef type. Starts returning none if memory is unmapped
/// Clone is whether the original PRef could be cloned or not and will impact the returned PRef
/// when reset() is called.
pub struct PRefResetIter<T: ?Sized, IterT, Trk: Track, const CLONE: bool> {
    /// Original pref.
    pref: PRefBase<T, Trk, CLONE>,
    /// Iterator, not guarded by the pref
    iter: IterT,
}

/// A reference to an iterator over something from a PRef that has been checked for liveness
pub struct CheckedPrefResetIter<'a, IterT: Iterator> {
    checked_ref: Option<&'a mut IterT>,
}

impl<T: ?Sized + 'static, Trk: Track, const CLONE: bool> IntoResettableIterator
    for PRefBase<T, Trk, CLONE>
where
    &'static T: IntoIterator,
    PRefResetIter<T, <&'static T as IntoIterator>::IntoIter, Trk, CLONE>:
        ResettableIterator<CollectionType = PRefBase<T, Trk, CLONE>>,
{
    type ResetIterType = PRefResetIter<T, <&'static T as IntoIterator>::IntoIter, Trk, CLONE>;

    fn into_resettable_iterator(self) -> Self::ResetIterType {
        // Safety: PRefResetIter will check the pref before returning any items, and will bound
        // their lifetime to a more appropriate lifetime than static during which the process
        // will not be unmapped.
        let raw_ptr = unsafe { self.get_ptr().as_ref() };
        Self::ResetIterType {
            pref: self,
            iter: raw_ptr.into_iter(),
        }
    }
}

impl<'a, 'i: 'a, ItemT: 'i + 'a, IterT: Iterator<Item = &'i ItemT>> Iterator
    for CheckedPrefResetIter<'a, IterT>
{
    type Item = &'a ItemT;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.checked_ref {
            // None if reference was no longer valid
            None => None,
            // Otherwise the reference is valid for the duration of the borrow 'a, so as long as we
            // rebound the lifetime to 'a it is safe to return.
            Some(iter_ref) => iter_ref.next(),
        }
    }
}

impl<
        'a,
        'i: 'a,
        ItemT: 'i + 'a,
        IterT: Iterator<Item = &'i ItemT>,
        T: ?Sized,
        Trk: Track,
        const CLONE: bool,
    > ResettableIteratorTypes<'a> for PRefResetIter<T, IterT, Trk, CLONE>
{
    type ItemType = <CheckedPrefResetIter<'a, IterT> as Iterator>::Item;
    type IterType = CheckedPrefResetIter<'a, IterT>;
}

impl<
        'i,
        ItemT: 'i,
        IterT: Iterator<Item = &'i ItemT>,
        T: ?Sized,
        Trk: Track,
        const CLONE: bool,
    > ResettableIterator for PRefResetIter<T, IterT, Trk, CLONE>
where
    for<'a> PRefResetIter<T, IterT, Trk, CLONE>:
        ResettableIteratorTypes<'a, IterType = CheckedPrefResetIter<'a, IterT>>,
{
    type CollectionType = PRefBase<T, Trk, CLONE>;

    fn reset(self) -> Self::CollectionType {
        self.pref
    }

    fn iter(&mut self) -> <Self as ResettableIteratorTypes<'_>>::IterType {
        CheckedPrefResetIter {
            checked_ref: if self.pref.is_still_alive() {
                Some(&mut self.iter)
            } else {
                None
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::collections::resettable_iterator::{
        ChasingResettableIterator, IntoChasingResettableIterator, IntoResettableIterator,
        ResettableIterator,
    };

    #[test]
    fn mut_example() {
        let mut some_collection = [1, 2, 3, 4];
        let ref_to_collection = &mut some_collection;

        let mut reset_iter = ref_to_collection.into_resettable_iterator();

        let mut i = 1;
        let mut foo: Option<&mut i32> = None;
        for item in reset_iter.iter() {
            assert_eq!(i, *item);
            i += 1;
            foo = Some(item);
        }

        let _ = *foo.unwrap();
        let _ref_to_collection2 = reset_iter.reset();
        //*foo.unwrap(); // <-- illegal, foo has lifetime that cannot go across reset
    }

    #[test]
    fn non_mut_example() {
        let some_collection = [1, 2, 3, 4];
        let ref_to_collection = &some_collection;

        let mut reset_iter = ref_to_collection.into_resettable_iterator();

        let mut i = 1;
        let mut foo: Option<&i32> = None;
        for item in reset_iter.iter() {
            assert_eq!(i, *item);
            i += 1;
            foo = Some(item);
        }

        let _ = *foo.unwrap();
        let _ref_to_collection2 = reset_iter.reset();

        let _ = *foo.unwrap(); // <-- illegal
    }

    #[test]
    fn chasing_test() {
        let some_collection = [1, 2, 3, 4];
        let ref_to_collection = &some_collection;

        let mut chasing = ref_to_collection.into_chasing_resettable_iterator();

        // iter() gives a pass over each item
        assert_eq!(*chasing.iter().next().unwrap(), 1);
        assert_eq!(*chasing.iter().next().unwrap(), 2);
        // chasing_iter() only gives the items already returned by iter();
        assert_eq!(*chasing.chasing_iter().next().unwrap(), 1);
        assert_eq!(*chasing.chasing_iter().next().unwrap(), 2);
        assert!(chasing.chasing_iter().next().is_none());
        // can go back to the first iterator
        assert_eq!(*chasing.iter().next().unwrap(), 3);
        assert_eq!(*chasing.iter().next().unwrap(), 4);
        assert!(chasing.iter().next().is_none());
        // and then more items will appear in the chasing iterator
        assert_eq!(*chasing.chasing_iter().next().unwrap(), 3);
        assert_eq!(*chasing.chasing_iter().next().unwrap(), 4);
        assert!(chasing.chasing_iter().next().is_none());
    }
}
