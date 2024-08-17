use crate::collections::resettable_iterator::{
    ChasingResettableOnce, IntoChasingResettableIterator,
};
use crate::processbuffer::{ReadableProcessByte, ReadableProcessU32, WriteableProcessU32};
use crate::{declare_chasing_resettable_x_iterator, declare_resettable_x_iterator};
use core::cell::{Cell, Ref};
use core::mem;
use core::ops::{Deref, Index, IndexMut, Range, RangeFrom, RangeTo};
use core::ptr::NonNull;
use misc::divorce::{
    DivorceLifeless, Divorceable, Divorced, LifelessCast, LifelessRef, LifelessRefMut,
    LifelessRefTraits, Reunitable,
};
use misc::trait_alias;

/// A single interface for the purpose of (possibly DMA-enabled) IO to (a possible chain of) buffers
/// This interface is meant to bring in line different types that might be used for this purpose
/// Buffers need to be able to contain:
///     Buffers allowed by userspace with allow_ro / allow_rw
///     Buffers allocated in (custom) grants
///     Statically allocated buffers
///     Stack allocated buffers
/// The exact types are likely going to be a blend of
///     `[u8;N]`
///     `[u8]`
///     `[Cell<u8>]`
///     `[ReadableProcessByte]`
///     `Ref<T>` of the above to make DMA more feasible
/// It is preferable to be polymorphic in the type over just borrowing to get `& mut [Cell<u8>]`,
/// because the lifetime of such a reference will not play nicely with async code where the callee
/// needs to store the reference for the duration of an operation, possibly a DMA operation.
///
/// Also, even though `& mut [Cell<u8>]` is likely the intersection of all requirements, it may not
/// optimise as well as, say, `[u8;N]` where bounds checking can be done statically.
///
/// Currently, there is also wasted effort tracking "progress" through a buffer with a manual index.
/// These are more naturally written as iterators, to avoid extra bounds checking and wasted effort.
/// ResettableIterator is offered to allow the common pattern of being passed a buffer, making an
/// iterator, looping (possibly in batches across interrupts), converting back into the buffer,
/// and then calling a callback.
/// Iterators also have the advantage of walking linked lists better than indexing
/// We will still offer the indexing option, but it should probably be avoided

/// This type describing a single contiguous buffer that corresponds to a rust type in the address
/// space of the CPU.
pub type CpuDmaRef = LifelessRef<[u8]>;
/// Mutable version of CpuDmaRef
pub type CpuDmaRefMut = LifelessRefMut<[u8]>;

pub unsafe fn cpu_dma_ref_from_address(base: usize, len: usize) -> CpuDmaRef {
    CpuDmaRef::remake(NonNull::slice_from_raw_parts(
        NonNull::new_unchecked(base as *mut u8),
        len,
    ))
}

pub unsafe fn cpu_dma_ref_mut_from_address(base: usize, len: usize) -> CpuDmaRefMut {
    CpuDmaRefMut::remake(NonNull::slice_from_raw_parts(
        NonNull::new_unchecked(base as *mut u8),
        len,
    ))
}

/// Traits for reading a byte
pub trait GetByte {
    /// Get the byte
    fn get_byte(&self) -> u8;
}
/// Trait for writing a byte
pub trait SetByte: GetByte {
    /// Set the byte
    fn set_byte(&mut self, value: u8);
}

// Just u8's, used for kernel originated buffers and grants
impl GetByte for &mut u8 {
    fn get_byte(&self) -> u8 where {
        **self
    }
}
impl SetByte for &mut u8 {
    fn set_byte(&mut self, value: u8) {
        **self = value;
    }
}
impl GetByte for &u8 {
    fn get_byte(&self) -> u8 where {
        **self
    }
}

impl GetByte for u8 {
    fn get_byte(&self) -> u8 {
        *self
    }
}

impl SetByte for u8 {
    fn set_byte(&mut self, value: u8) {
        *self = value;
    }
}

// Cell<u8> used for RW allow buffers
impl<'a> GetByte for &'a Cell<u8> {
    fn get_byte(&self) -> u8 {
        Cell::<u8>::get(*self)
    }
}
impl<'a> SetByte for &'a Cell<u8> {
    fn set_byte(&mut self, value: u8) {
        Cell::<u8>::set(*self, value);
    }
}

impl GetByte for Cell<u8> {
    fn get_byte(&self) -> u8 {
        self.get()
    }
}

impl SetByte for Cell<u8> {
    fn set_byte(&mut self, value: u8) {
        self.set(value)
    }
}

// Used for RO allow buffers
impl GetByte for ReadableProcessByte {
    fn get_byte(&self) -> u8 {
        ReadableProcessByte::get(self)
    }
}

impl<'a> GetByte for &'a ReadableProcessByte {
    fn get_byte(&self) -> u8 {
        (*self).get_byte()
    }
}

pub trait GetU32 {
    fn get_u32(&self) -> u32;
}

impl<'a> GetU32 for &'a ReadableProcessU32 {
    fn get_u32(&self) -> u32 {
        self.get()
    }
}

impl<'a> GetU32 for &'a u32 {
    fn get_u32(&self) -> u32 {
        **self
    }
}

impl<'a> GetU32 for &'a WriteableProcessU32 {
    fn get_u32(&self) -> u32 {
        self.get()
    }
}

/// A trait for a collection that has a number of elements
pub trait BufLength {
    /// How many elements are in this collection
    fn buf_len(&self) -> usize;
}

impl<T> BufLength for [T] {
    fn buf_len(&self) -> usize {
        self.len()
    }
}

impl<T, const N: usize> BufLength for [T; N] {
    fn buf_len(&self) -> usize {
        N
    }
}

impl<T> BufLength for NonNull<[T]> {
    fn buf_len(&self) -> usize {
        self.len()
    }
}

impl<T, const N: usize> BufLength for NonNull<[T; N]> {
    fn buf_len(&self) -> usize {
        N
    }
}

/// The trait used for DMA
pub trait FragmentDivorce {
    /// Divorce a lifeless ref to a slice of u8s, leaving whatever remains behind
    fn divorce_fragment(&mut self) -> CpuDmaRef;
    /// Reunite them again
    fn reunite_fragment(&mut self, lifeless: CpuDmaRef);
    /// TODO: Decide if I want a capability to invoke this interface
    /// b/271563432
    /// Reunite from a raw pointer that has been read from some CSR / Descriptor
    /// This is less safe than the other reunite. Don't stash values from consuming the lifeless ref,
    /// always try to read back from hardware to catch errors.
    fn reunite_fragment_raw(&mut self, ptr: NonNull<[u8]>);
    /// Does the fragment match the divorced type. You should already probably know if it does,
    /// this is mostly here for when the LifelessRefs were split in a way that was not tracked.
    fn raw_matches(&self, ptr: NonNull<[u8]>) -> bool;
}

/// Mutable version of FragmentDivorce where the fragments are LifelessRefMut rather than
/// LifelessRef.
pub trait FragmentDivorceMut: FragmentDivorce {
    fn divorce_fragment_mut(&mut self) -> CpuDmaRefMut;
    fn reunite_fragment_mut(&mut self, lifeless: CpuDmaRefMut);
    fn reunite_fragment_mut_raw(&mut self, ptr: NonNull<[u8]>);
}

/// More generic versions of fragment divorce to avoid a copy and paste for the mutable version
pub trait FragmentDivorceGeneric<Frag, T: ?Sized> {
    fn divorce_fragment_gen(&mut self) -> Frag;
    fn reunite_fragment_gen(&mut self, lifeless: Frag);
    fn reunite_fragment_raw_gen(&mut self, ptr: NonNull<T>);
}

// More helpful trait names for a buffer that can be converted into an iterator over bytes,
// and then back

// For Reading bytes with the CPU
declare_resettable_x_iterator!(
    ResettableByteReadIterator,
    ResettableByteReadIteratorTy,
    IntoResettableByteReadIterator,
    GetByte
);
declare_resettable_x_iterator!(
    ResettableU32ReadIterator,
    ResettableU32ReadIteratorTy,
    IntoResettableU32ReadIterator,
    GetU32
);
// For Writing bytes with the CPU
declare_resettable_x_iterator!(
    ResettableByteWriteIterator,
    ResettableByteWriteIteratorTy,
    IntoResettableByteWriteIterator,
    SetByte
);
// For read-only DMA access
declare_chasing_resettable_x_iterator!(
    ResettableDivorceIterator,
    ResettableDivorceIteratorTy,
    IntoResettableDivorceIterator,
    FragmentDivorce
);
// For read/write DMA access
declare_chasing_resettable_x_iterator!(
    ResettableDivorceMutIterator,
    ResettableDivorceMutIteratorTy,
    IntoResettableDivorceMutIterator,
    FragmentDivorceMut
);

trait_alias!(
    /// Can index to read bytes. Slicing will give the same type.
    pub trait ByteReadIndexSelf = Index<usize>, Index<Range<usize>, Output = Self>
        ,Index<RangeTo<usize>, Output = Self>
        ,Index<RangeFrom<usize>, Output = Self>
    as where Index<usize>:::Output as IndexOutputGet: GetByte | ?Sized
);

trait_alias!(
    /// Can index to read bytes. Can also be sub-sliced that (may) give a different type
    pub trait ByteReadIndex = Index<usize>, Index<Range<usize>>
        ,Index<RangeTo<usize>>
        ,Index<RangeFrom<usize>>
    as where Index<usize>:::Output as IndexOutputGet: GetByte | ?Sized,
           Index<Range<usize>>:::Output as IndexR: ByteReadIndexSelf | ?Sized,
           Index<RangeTo<usize>>:::Output as IndexT: ByteReadIndexSelf | ?Sized,
           Index<RangeFrom<usize>>:::Output as IndexF: ByteReadIndexSelf | ?Sized
);

trait_alias!(
    /// This trait is meant to encapsulate a (possibly chain of) read only data buffers.
    /// Try to use the iterator paradigm, but you can also deref to index.
    pub trait GenBufRead = IntoResettableByteReadIterator, Deref
    as where Deref:::Target as DerefTarget : ByteReadIndex | ?Sized
);

trait_alias!(
    pub trait ByteWriteIndexSelf = IndexMut<usize>, IndexMut<Range<usize>, Output = Self>
        ,IndexMut<RangeTo<usize>, Output = Self>
        ,IndexMut<RangeFrom<usize>, Output = Self>
    as where Index<usize>:::Output as IndexOutputSet: SetByte | ?Sized
);

trait_alias!(
    pub trait ByteWriteIndex = Index<usize>, IndexMut<Range<usize>>
        ,IndexMut<RangeTo<usize>>
        ,IndexMut<RangeFrom<usize>>
    as where Index<usize>:::Output as IndexOutputGet: SetByte | ?Sized,
           Index<Range<usize>>:::Output as IndexR: ByteWriteIndexSelf | ?Sized,
           Index<RangeTo<usize>>:::Output as IndexT: ByteWriteIndexSelf | ?Sized,
           Index<RangeFrom<usize>>:::Output as IndexF: ByteWriteIndexSelf | ?Sized
);

trait_alias!(
    pub trait GenBufWrite = IntoResettableByteWriteIterator, Deref
    as where Deref:::Target as DerefTargetWrite : ByteWriteIndex | ?Sized
);

pub trait DMAFinish {
    type From;
    fn finish_dma(self) -> Self::From;
}

// Can be used for DMA (read only)
pub trait GenBufDMARead {
    type GenBufDMA: IntoResettableDivorceIterator + DMAFinish<From = Self>;
    /// Perform any type conversion / wrapping required to store divorced types
    fn prepare_dma(self) -> Self::GenBufDMA;
}

/// A single, contiguous, DMA buffer. Only use this when hardware/software can really not handle
/// fragmentation as IOMPUs / length-matching may also fragment.
///GenBufDMARead is corresponding non-contiguous version.
pub trait GenBufSingleDMARead {
    type GenBufDMA: FragmentDivorce + DMAFinish<From = Self>;
    fn prepare_dma_single(self) -> Self::GenBufDMA;
}

trait_alias!(
    pub trait GenBufSingleDMAWrite = GenBufSingleDMARead
    as where GenBufSingleDMARead:::GenBufDMA as GenBufDMABounded : FragmentDivorceMut |
                                                                    DMAFinish<From = Self>
);

trait_alias!(
    pub trait GenBufDMAWrite = GenBufDMARead
    as where GenBufDMARead:::GenBufDMA as GenBufDMABounded : IntoResettableDivorceMutIterator |
                                                             DMAFinish<From = Self>
);

/// For types that just create a single fragment we wrap in an enum that allows the divorced type
/// to remain. We have the None state to help in-place modification.
pub enum PayloadOrDivorced<P: DivorceLifeless> {
    Payload(P),
    Divorced(Divorced<P, P::Lifeless>),
    None(),
}

// Implement default to set state to none
impl<P: DivorceLifeless> Default for PayloadOrDivorced<P> {
    fn default() -> Self {
        PayloadOrDivorced::None()
    }
}

// Prepare single buffer for DMA by allocating space for divorced type
impl<P: DivorceLifeless> GenBufDMARead for P
where
    PayloadOrDivorced<P>: IntoResettableDivorceIterator,
{
    type GenBufDMA = PayloadOrDivorced<P>;

    fn prepare_dma(self) -> Self::GenBufDMA {
        PayloadOrDivorced::Payload(self)
    }
}

// Same again for GenBufSingleDMARead but without the requirement for an iterator
impl<P: DivorceLifeless> GenBufSingleDMARead for P
where
    PayloadOrDivorced<P>: FragmentDivorce,
{
    type GenBufDMA = PayloadOrDivorced<P>;

    fn prepare_dma_single(self) -> Self::GenBufDMA {
        PayloadOrDivorced::Payload(self)
    }
}

// Finish by unwrapping
impl<P: DivorceLifeless> DMAFinish for PayloadOrDivorced<P> {
    type From = P;

    #[inline]
    fn finish_dma(self) -> Self::From {
        match self {
            PayloadOrDivorced::Payload(p) => p,
            _ => {
                panic!()
            }
        }
    }
}

// PayloadOrDivorced is a once iterator

impl<P: DivorceLifeless> IntoChasingResettableIterator for PayloadOrDivorced<P> {
    type ChasingResetIterType = ChasingResettableOnce<Self>;

    fn into_chasing_resettable_iterator(self) -> Self::ChasingResetIterType {
        ChasingResettableOnce::new(self)
    }
}

impl<P: DivorceLifeless> FragmentDivorceGeneric<P::Lifeless, P::InnerT> for PayloadOrDivorced<P> {
    fn divorce_fragment_gen(&mut self) -> P::Lifeless {
        let val = mem::take(self);
        let (d, l) = match val {
            PayloadOrDivorced::Payload(payload) => payload.divorce(),
            _ => panic!(),
        };
        *self = PayloadOrDivorced::Divorced(d);
        l
    }

    fn reunite_fragment_gen(&mut self, lifeless: P::Lifeless) {
        let val = mem::take(self);
        let payload = match val {
            PayloadOrDivorced::Divorced(d) => d.reunite(lifeless),
            _ => panic!(),
        };
        *self = PayloadOrDivorced::Payload(payload);
    }

    fn reunite_fragment_raw_gen(&mut self, ptr: NonNull<P::InnerT>) {
        unsafe {
            self.reunite_fragment_gen(P::Lifeless::remake(ptr));
        }
    }
}

// Provide the implementations of the two concrete traits from the more generic ones

impl<P: DivorceLifeless> FragmentDivorce for PayloadOrDivorced<P>
where
    P::Lifeless: LifelessCast<CpuDmaRef>,
{
    fn divorce_fragment(&mut self) -> CpuDmaRef {
        self.divorce_fragment_gen().cast()
    }

    fn reunite_fragment(&mut self, lifeless: CpuDmaRef) {
        // Safety: we are possibly casting back in an illegal way but this will checked by the
        // reunite.
        unsafe {
            self.reunite_fragment_gen(P::Lifeless::cast_back(lifeless));
        }
    }

    fn reunite_fragment_raw(&mut self, ptr: NonNull<[u8]>) {
        unsafe {
            self.reunite_fragment(LifelessRef::remake(ptr));
        }
    }

    fn raw_matches(&self, ptr: NonNull<[u8]>) -> bool {
        // Safety: we only construct the lifeless ref for the duration of the check
        if let Some(l) = unsafe { P::Lifeless::try_cast_back(LifelessRef::remake(ptr)) } {
            match &self {
                PayloadOrDivorced::Divorced(d) => Divorceable::<P::Lifeless>::matches(d, &l),
                _ => panic!(),
            }
        } else {
            false
        }
    }
}

impl<P: DivorceLifeless> FragmentDivorceMut for PayloadOrDivorced<P>
where
    Self: FragmentDivorce,
    P::Lifeless: LifelessCast<CpuDmaRefMut>,
{
    fn divorce_fragment_mut(&mut self) -> CpuDmaRefMut {
        self.divorce_fragment_gen().cast()
    }

    fn reunite_fragment_mut(&mut self, lifeless: CpuDmaRefMut) {
        // Safety: we are possibly casting back in an illegal way but this will checked by the
        // reunite.
        unsafe {
            self.reunite_fragment_gen(P::Lifeless::cast_back(lifeless));
        }
    }

    fn reunite_fragment_mut_raw(&mut self, ptr: NonNull<[u8]>) {
        unsafe {
            self.reunite_fragment_mut(LifelessRefMut::remake(ptr));
        }
    }
}

// Also provide on the references

impl<'a, T: FragmentDivorce> FragmentDivorce for &'a mut T {
    fn divorce_fragment(&mut self) -> CpuDmaRef {
        (*self).divorce_fragment()
    }

    fn reunite_fragment(&mut self, lifeless: CpuDmaRef) {
        (*self).reunite_fragment(lifeless)
    }

    fn reunite_fragment_raw(&mut self, ptr: NonNull<[u8]>) {
        (*self).reunite_fragment_raw(ptr)
    }

    fn raw_matches(&self, ptr: NonNull<[u8]>) -> bool {
        <T as FragmentDivorce>::raw_matches(self, ptr)
    }
}

impl<'a, T: FragmentDivorceMut> FragmentDivorceMut for &'a mut T {
    fn divorce_fragment_mut(&mut self) -> CpuDmaRefMut {
        (*self).divorce_fragment_mut()
    }

    fn reunite_fragment_mut(&mut self, lifeless: CpuDmaRefMut) {
        (*self).reunite_fragment_mut(lifeless)
    }

    fn reunite_fragment_mut_raw(&mut self, ptr: NonNull<[u8]>) {
        (*self).reunite_fragment_mut_raw(ptr)
    }
}

/// A type to support DMA to a linked list of buffer fragments.
/// If there is only one buffer to be used at an interface, then it should already support
/// GenBufDMARead/Write. If you need a chain of same typed buffers, use ChainBuf<'a, T> for
/// that type. If chains are being passed through multiple layers which attach different types,
/// ChainBuf<'a, GenPayload<'a>> is designed for that use case.
/// ChainBuf allows editing the chain, and so we wrap things in cells.
/// I chose this over simply a mutable reference because we might need multiple references.
pub struct ChainBuf<'a, PayloadT: 'a> {
    next: Option<ChainLink<'a, PayloadT>>,
    payload: Cell<PayloadT>,
}

impl<'a, PayloadT: 'a + FragmentDivorce + Default> GenBufDMARead for ChainLink<'a, PayloadT> {
    type GenBufDMA = Self;

    fn prepare_dma(self) -> Self::GenBufDMA {
        self
    }
}

impl<'a, PayloadT: 'a + FragmentDivorce + Default> DMAFinish for ChainLink<'a, PayloadT> {
    type From = Self;

    fn finish_dma(self) -> Self::From {
        self
    }
}

// Implement the FragmentDivorce/Mut traits for ChainBufs
impl<'a, PayloadT: 'a + FragmentDivorce + Default> FragmentDivorce for ChainLink<'a, PayloadT> {
    fn divorce_fragment(&mut self) -> CpuDmaRef {
        let mut p = self.payload.take();
        let result = p.divorce_fragment();
        self.payload.set(p);
        result
    }

    fn reunite_fragment(&mut self, lifeless: CpuDmaRef) {
        let mut p = self.payload.take();
        let result = p.reunite_fragment(lifeless);
        self.payload.set(p);
        result
    }

    fn reunite_fragment_raw(&mut self, ptr: NonNull<[u8]>) {
        let mut p = self.payload.take();
        let result = p.reunite_fragment_raw(ptr);
        self.payload.set(p);
        result
    }

    fn raw_matches(&self, ptr: NonNull<[u8]>) -> bool {
        let p = self.payload.take();
        let result = p.raw_matches(ptr);
        self.payload.set(p);
        result
    }
}

impl<'a, PayloadT: 'a + FragmentDivorceMut + Default> FragmentDivorceMut
    for ChainLink<'a, PayloadT>
{
    fn divorce_fragment_mut(&mut self) -> CpuDmaRefMut {
        let mut p = self.payload.take();
        let result = p.divorce_fragment_mut();
        self.payload.set(p);
        result
    }

    fn reunite_fragment_mut(&mut self, lifeless: CpuDmaRefMut) {
        let mut p = self.payload.take();
        let result = p.reunite_fragment_mut(lifeless);
        self.payload.set(p);
        result
    }

    fn reunite_fragment_mut_raw(&mut self, ptr: NonNull<[u8]>) {
        let mut p = self.payload.take();
        let result = p.reunite_fragment_mut_raw(ptr);
        self.payload.set(p);
        result
    }
}

impl<'a, PayloadT: 'a> ChainBuf<'a, PayloadT> {
    pub fn new_with_next(payload: PayloadT, next: Option<ChainLink<'a, PayloadT>>) -> Self {
        ChainBuf {
            next,
            payload: Cell::new(payload),
        }
    }
    pub fn new(payload: PayloadT) -> Self {
        Self::new_with_next(payload, None)
    }
    pub fn clone_next(&self) -> Option<ChainLink<'a, PayloadT>> {
        self.next.clone()
    }
    pub fn replace_next(
        &mut self,
        val: Option<ChainLink<'a, PayloadT>>,
    ) -> Option<ChainLink<'a, PayloadT>> {
        mem::replace(&mut self.next, val)
    }
    pub fn get_ref(&'a self) -> ChainLink<'a, PayloadT> {
        self.into()
    }
}

// Some convenience wrappers for putting in a payload that first needs wrapping
impl<'a, InnerP: 'a + DivorceLifeless> ChainBuf<'a, PayloadOrDivorced<InnerP>> {
    pub fn new_divorcable_with_next<NextT: Into<ChainLink<'a, PayloadOrDivorced<InnerP>>>>(
        payload: InnerP,
        next: NextT,
    ) -> Self {
        Self::new_with_next(PayloadOrDivorced::Payload(payload), Some(next.into()))
    }
    pub fn set_next<NextT: Into<ChainLink<'a, PayloadOrDivorced<InnerP>>>>(
        &mut self,
        next: NextT,
    ) -> Option<ChainLink<'a, PayloadOrDivorced<InnerP>>> {
        self.next.replace(next.into())
    }
    pub fn new_divorcable(payload: InnerP) -> Self {
        Self::new_with_next(PayloadOrDivorced::Payload(payload), None)
    }
}

/// A link for scatter gather DMA lists. Contains the two most common types of reference we expect
/// to be in use.
/// A list with just one variant would not be appendable to a list that used the other.
pub enum ChainLink<'a, PayloadT: 'a> {
    // Limited lifetime reference
    Ref(&'a ChainBuf<'a, PayloadT>),
    // Reference counted reference (might not really be static, but the Ref will always outlive the cell)
    RcRef(Ref<'a, ChainBuf<'a, PayloadT>>),
}

// Can convert between the different types of reference
impl<'a, PayloadT: 'a> From<&'a ChainBuf<'a, PayloadT>> for ChainLink<'a, PayloadT> {
    fn from(val: &'a ChainBuf<'a, PayloadT>) -> Self {
        ChainLink::Ref(val)
    }
}

impl<'a, PayloadT: 'a> From<Ref<'a, ChainBuf<'a, PayloadT>>> for ChainLink<'a, PayloadT> {
    fn from(val: Ref<'a, ChainBuf<'a, PayloadT>>) -> Self {
        ChainLink::RcRef(val)
    }
}

impl<'a, PayloadT: 'a> Clone for ChainLink<'a, PayloadT> {
    fn clone(&self) -> Self {
        match self {
            ChainLink::Ref(x) => ChainLink::Ref(x.clone()),
            // This clone is only an associated method, so we have to do this ourselves
            ChainLink::RcRef(x) => ChainLink::RcRef(Ref::<'_, ChainBuf<'_, PayloadT>>::clone(x)),
        }
    }
}

// Allow a chainlink to be used as a ChainBuf reference
impl<'a, PayloadT: 'a> Deref for ChainLink<'a, PayloadT> {
    type Target = ChainBuf<'a, PayloadT>;

    fn deref(&self) -> &Self::Target {
        match self {
            ChainLink::Ref(r) => *r,
            ChainLink::RcRef(rc) => rc.deref(),
        }
    }
}

pub struct ChainBufIter<'a, P: 'a> {
    next: Option<ChainLink<'a, P>>,
}

// Implement into iter for all of ChainLink or a raw reference
impl<'a, P: 'a> IntoIterator for ChainLink<'a, P> {
    type Item = ChainLink<'a, P>;
    type IntoIter = ChainBufIter<'a, P>;

    fn into_iter(self) -> Self::IntoIter {
        ChainBufIter { next: Some(self) }
    }
}
impl<'a, P: 'a> IntoIterator for &'a ChainBuf<'a, P> {
    type Item = ChainLink<'a, P>;
    type IntoIter = ChainBufIter<'a, P>;

    fn into_iter(self) -> Self::IntoIter {
        ChainBufIter {
            next: Some(ChainLink::Ref(self)),
        }
    }
}

impl<'a, P> Iterator for ChainBufIter<'a, P> {
    type Item = ChainLink<'a, P>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next.take() {
            Some(gn) => {
                self.next = gn.clone_next();
                Some(gn)
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::collections::resettable_iterator::IntoChasingResettableIterator;
    use crate::collections::safe_buf::{ChainBuf, GenBufDMARead};
    use crate::platform::iompu::{DMAMatchIter, DmaRef, DmaRefMut, InOrderIOMPU};

    type NoMPU = crate::platform::iompu::NoIOMPU<()>;

    #[test]
    fn match_iter_test() {
        // 60 bytes in two lots of 30
        let src1 = [77u8; 30].as_slice();
        let src2 = [77u8; 30].as_slice();

        // 60 bytes in three lots of 20
        let mut dst1 = [0u8; 20];
        let mut dst2 = [0u8; 20];
        let mut dst3 = [0u8; 20];

        // Some chains over them
        let dst_chain = ChainBuf::new_divorcable(dst3.as_mut_slice());
        let dst_chain = ChainBuf::new_divorcable_with_next(dst2.as_mut_slice(), &dst_chain);
        let dst_chain = ChainBuf::new_divorcable_with_next(dst1.as_mut_slice(), &dst_chain);

        let src_chain = ChainBuf::new_divorcable(src2);
        let src_chain = ChainBuf::new_divorcable_with_next(src1, &src_chain);

        // Into iterators
        let dst_iter = dst_chain
            .get_ref()
            .prepare_dma()
            .into_chasing_resettable_iterator();
        let src_iter = src_chain
            .get_ref()
            .prepare_dma()
            .into_chasing_resettable_iterator();

        // Create stream from an IOMPU
        let io_mpu = NoMPU::new();

        let dst_stream = io_mpu.start_dma_stream_mut(dst_iter);
        let src_stream = io_mpu.start_dma_stream(src_iter);

        // Zip equal sized parts
        let mut match_iter: DMAMatchIter<_, _> = DMAMatchIter::new(dst_stream, src_stream, &io_mpu);

        let mut total = 0;

        let mut pairs: [Option<(DmaRefMut, DmaRef)>; 10] = Default::default();
        let mut i = 0;

        // Iter over equal sized fragments. Get pairs of lifelessRefs to do DMA on
        for pair in match_iter.iter(&io_mpu) {
            let (dst_frag, src_frag) = pair.ok().unwrap();
            // They should match in size
            assert_eq!(dst_frag.len(), src_frag.len());
            total += dst_frag.len();
            pairs[i] = Some((dst_frag, src_frag));
            i += 1;
        }

        // And again to return them. Getting the order wrong / forgetting one will cause a panic
        for j in 0..i {
            if let Some((dst_frag, src_frag)) = pairs[j].take() {
                match_iter.reunite_pair((dst_frag.into(), src_frag.into()), &io_mpu)
            }
        }

        // Should have totalled correctly
        assert_eq!(total, 60);
    }

    // See gpdma.rs for more complicated tests involving the traits in the file.
}
