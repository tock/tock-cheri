// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Implementation of a ring buffer.

use crate::collections::queue;
use core::cell::Cell;
use core::mem::MaybeUninit;

pub struct RingBuffer<'a, T: 'a> {
    ring: &'a mut [T],
    head: usize,
    tail: usize,
}

/// Types for head/tail. 64K is plenty for character buffers. Factored to parameterize this later
/// if good reason presents itself.
pub type RingBufferInt = u16;

/// Statically sized ring buffer. As opposed to the other ring buffer above:
/// Power of two N will properly optimise as it is a constant, not dynamic, value
/// Data is stored inline making it easier to allocate (saves a bunch of unsafe in process standard)
/// Uses Cell so no &mut is needed for most operations getting rid of MapCells
/// Uses MaybeUninit so Default / Zeroing is also not required.
/// Has more efficient push_slice for moving slices with memcpy.
/// Uses unsafe =( / has an unsafer retain implementation.
pub struct StaticSizedRingBuffer<T, const N: usize> {
    /// Wrapping counter of how many items pushed
    tail: Cell<RingBufferInt>,
    /// Wrapping counter of how many items popped
    head: Cell<RingBufferInt>,
    /// Note: we put the cell around the array because projecting `Cell[;N] -> [Cell<>;N]` exists
    /// but the opposite does not.
    ring: Cell<[MaybeUninit<T>; N]>,
}

impl<T, const N: usize> Drop for StaticSizedRingBuffer<T, N> {
    fn drop(&mut self) {
        // Make sure to drop every item
        self.empty();
    }
}

// I was hoping to share logic here, but the &mut in Queue makes that hard.
// Also, because we don't use &mut, we have to be REALLY careful about when T::drop happens because
// the drop implementation of T might capture the buffer and try to make concurrent access.
impl<T, const N: usize> StaticSizedRingBuffer<T, N> {
    const Z: MaybeUninit<T> = MaybeUninit::zeroed();
    const U: MaybeUninit<T> = MaybeUninit::uninit();

    /// A version of new that will result in all zeros.
    /// Good for global queues that go in BSS.
    #[inline]
    pub const fn new_zeros() -> Self {
        StaticSizedRingBuffer {
            ring: Cell::new([Self::Z; N]),
            tail: Cell::new(0),
            head: Cell::new(0),
        }
    }

    /// A version of new that will result in the ring being uninitialized
    /// Good for dynamically allocating, e.g. in process headers.
    #[inline]
    pub fn new_uninit() -> Self {
        StaticSizedRingBuffer {
            ring: Cell::new([Self::U; N]),
            tail: Cell::new(0),
            head: Cell::new(0),
        }
    }

    /// How many elements are in the queue
    #[inline]
    pub fn len(&self) -> usize {
        (self.tail.get() as usize).wrapping_sub(self.head.get() as usize)
    }

    #[inline]
    pub fn is_full(&self) -> bool {
        self.len() == N
    }

    #[inline]
    pub fn has_elements(&self) -> bool {
        self.tail.get() != self.head.get()
    }

    /// How many space is available to write elements
    #[inline]
    pub fn available_len(&self) -> usize {
        (N as usize).wrapping_sub(self.len())
    }

    /// Try to push to the queue, if full returns back the argument
    #[inline]
    pub fn enqueue(&self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }

        let tl = self.tail.get();

        self.ring.as_array_of_cells()[(tl as usize % N)].set(MaybeUninit::new(value));

        self.tail.set(tl.wrapping_add(1));

        Ok(())
    }

    /// Try to push to the queue, if full pops an item from the queue
    #[inline]
    pub fn push(&self, value: T) -> Result<(), T> {
        let full = self.is_full();
        let tl = self.tail.get() as usize;
        let next_tl = tl.wrapping_add(1);
        self.tail.set(next_tl as RingBufferInt);
        let old = self.ring.as_array_of_cells()[(tl as usize) % N].replace(MaybeUninit::new(value));
        if full {
            self.head.set(next_tl.wrapping_sub(N) as RingBufferInt);
            Err(unsafe { old.assume_init() })
        } else {
            Ok(())
        }
    }

    #[inline]
    pub fn dequeue(&self) -> Result<T, ()> {
        if !self.has_elements() {
            return Err(());
        }

        let hd = self.head.get();

        let value = unsafe {
            // Safety: We only read items we have previously written with push
            self.ring.as_array_of_cells()[hd as usize % N]
                .replace(MaybeUninit::uninit())
                .assume_init()
        };

        self.head.set(hd.wrapping_add(1));

        Ok(value)
    }

    /// Dequeue multiple elements
    #[inline]
    pub fn dequeue_many(&self, n: usize) -> Result<(), ()> {
        if n > self.len() {
            return Err(());
        }

        if core::mem::needs_drop::<T>() {
            // Need to drop individual items
            for _i in 0..n {
                let _ = self.dequeue();
            }
        } else {
            // Can just increment
            self.head
                .set(self.head.get().wrapping_add(n as RingBufferInt))
        }

        Ok(())
    }

    /// Get up to as many as len elements from the queues as slices (without popping them).
    /// This needs to be &mut because otherwise we will be holding a reference to data that can
    /// be ripped out from underneath us by pop() and made un-init
    #[inline]
    pub fn as_slices_up_to(&mut self, mut len: usize) -> (&mut [T], &mut [T]) {
        if len > self.len() {
            // Cap len
            len = self.len();
        }

        // As we happen to have &mut, we can also get rid of the Cell<>
        let ring = self.ring.get_mut();

        let hd = self.head.get();
        let tl = hd.wrapping_add(len as RingBufferInt); // will be <= the actual tail

        let split_ndx = (hd as usize) % N;

        let (left, right) = ring.split_at_mut(split_ndx);

        let end_ndx = (tl as usize) % N;

        let (left, right) = if (split_ndx < end_ndx) || len == 0 {
            // Simple case where there is no wrap-around
            (&mut right[..len], &mut left[..0])
        } else {
            // Wrap around
            (right, &mut left[..end_ndx])
        };

        // Safety: in the no wrap round case (hd < tl) we have a zero length left and the items
        // between hd and tl.
        // In the wrap around case, we have all the items after head, and every item up to the
        // wrapped tail.
        unsafe {
            (
                MaybeUninit::slice_assume_init_mut(left),
                MaybeUninit::slice_assume_init_mut(right),
            )
        }
    }

    #[inline]
    pub fn as_slices(&mut self) -> (&mut [T], &mut [T]) {
        self.as_slices_up_to(self.len())
    }

    /// Get an element at a particular index.
    /// Note: ndx should be a wrapping counter. It is a counter from 0..u16::MAX,
    /// not from 0...N.
    /// If the counter is not between tail and head an error is returned
    #[inline]
    pub fn get_ndx(&mut self, ndx: RingBufferInt) -> Result<&mut T, ()> {
        let hd = self.head.get();

        // This is the n'th element in the queue
        let nth_elem = (ndx as usize).wrapping_sub(hd as usize);
        // This is how elements are in the queue
        let len = self.len();

        // If we are asking for an element too far after hd, error
        if nth_elem >= len {
            return Err(());
        }

        let elem = &mut self.ring.get_mut()[(ndx as usize) % N];

        // Safety: Elements between hd and tl are init. They cannot be made unnit with a pop
        // because the signature of this method borrows self mutably.
        unsafe { Ok(elem.assume_init_mut()) }
    }

    #[inline]
    pub fn get_head(&mut self) -> Result<&mut T, ()> {
        self.get_ndx(self.head.get())
    }

    #[inline]
    pub fn get_tail(&mut self) -> Result<&mut T, ()> {
        self.get_ndx(self.tail.get())
    }

    #[inline]
    pub fn empty(&self) {
        // Drop everything we need to

        if core::mem::needs_drop::<T>() {
            while self.has_elements() {
                let _ = self.dequeue();
                // Note: the drop of the result above may cause concurrent modification.
                // This is O.K.
            }
        } else {
            self.head.set(0);
            self.tail.set(0);
        }
    }

    /// Retain only items for which the predicate is true.
    /// Returns the last item removed.
    /// Safety: Neither T::Drop or the closure passed to retain may call methods on 'self' that
    /// modify the collection, or else T must be copy.
    #[inline]
    pub unsafe fn retain<F>(&self, mut f: F) -> Option<T>
    where
        F: FnMut(&T) -> bool,
    {
        // Index over the elements before the retain operation.
        let original_head = self.head.get();
        let mut src = original_head as usize;
        // Index over the retained elements.
        let mut dst = src;

        let end = self.tail.get() as usize;

        // Implementation note: we effectively empty the collection while this is ongoing so that
        // in the context of the callback the invariant of having valid items between head and tail
        // is kept true in case concurrent modification is attempted.
        // We also check afterwards that they have not changed, and just bail if they do.
        // The only way this can go wrong is if 2^16 elements were pushed/popped in the callback.
        // If they were, we might bring back elements that were popped. This is only a problem
        // if they are not copy, but is the reason we mark this function as unsafe.

        self.tail.set(0);
        self.head.set(0);

        let ring = self.ring.as_array_of_cells();

        let mut last = None;

        while src != end {
            let src_ndx = src % N;

            let item = ring[src_ndx].replace(MaybeUninit::uninit());

            // Safety: all items between head and tail are init
            let item = unsafe { item.assume_init() };

            let keep = f(&item); // modification of structure could happen here...

            if !keep {
                last = Some(item); // ...and here if T::drop does some modification
            } else {
                ring[dst % N].set(MaybeUninit::new(item));
                dst = dst.wrapping_add(1);
            }

            // Bail if structure was modified
            if self.tail.get() != 0 || self.head.get() != 0 {
                return last;
            }

            src = src.wrapping_add(1);
        }

        self.head.set(original_head);
        self.tail.set(dst as RingBufferInt);

        last
    }

    #[inline]
    pub unsafe fn remove_first_matching<F>(&self, mut f: F) -> Option<T>
    where
        F: FnMut(&T) -> bool,
    {
        let mut found: bool = false;
        self.retain(|elem| {
            found
                || if f(elem) {
                    found = true;
                    false
                } else {
                    true
                }
        })
    }

    /// Safe version of retain where &mut reference is held.
    pub fn retain_mut<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        // Safety: If self is &mut, there is no way for f to also call methods on self.
        unsafe {
            self.retain(f);
        }
    }

    #[inline]
    pub fn remove_first_matching_mut<F>(&mut self, f: F) -> Option<T>
    where
        F: FnMut(&T) -> bool,
    {
        // Safety: If self is &mut, there is no way for f to also call methods on self.
        unsafe { self.remove_first_matching(f) }
    }
}

impl<T: Copy, const N: usize> StaticSizedRingBuffer<T, N> {
    /// Safe version of retain where T copy.
    /// Might result in copies being made / items being leaked if 'F' tries to concurrently
    /// modify the collection.
    #[inline]
    pub fn retain_copy<F>(&self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        // Safety: retain says it is safe where T : Copy, and that is required in this impl block
        unsafe {
            self.retain(f);
        }
    }

    #[inline]
    pub fn remove_first_matching_copy<F>(&self, f: F) -> Option<T>
    where
        F: FnMut(&T) -> bool,
    {
        // Safety: retain says it is safe where T : Copy, and that is required in this impl block
        unsafe { self.remove_first_matching(f) }
    }
}

pub struct StaticSizedRingBufferIter<'a, T, const N: usize> {
    ring_buffer: &'a mut StaticSizedRingBuffer<T, N>,
    ndx: RingBufferInt,
}

impl<'a, T, const N: usize> IntoIterator for &'a mut StaticSizedRingBuffer<T, N> {
    type Item = &'a mut T;
    type IntoIter = StaticSizedRingBufferIter<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        let hd = self.head.get();
        StaticSizedRingBufferIter {
            ring_buffer: self,
            ndx: hd,
        }
    }
}

impl<'a, T, const N: usize> Iterator for StaticSizedRingBufferIter<'a, T, N> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ndx == self.ring_buffer.tail.get() {
            None
        } else {
            let elem = &mut self.ring_buffer.ring.get_mut()[(self.ndx as usize) % N];
            self.ndx = self.ndx.wrapping_add(1);
            unsafe {
                // Safety: we started iterating at head, and return none once we hit tail.
                // all elements between head and tail are init.
                // This iterator owns the collection so it cannot be modified.
                // The iterator will never return the item again, so increasing lifetime to 'a
                // also safe.
                core::mem::transmute(Some(elem.assume_init_mut()))
            }
        }
    }
}

impl<T: Copy, const N: usize> StaticSizedRingBuffer<T, N> {
    #[inline]
    pub fn enqueue_slice(&self, values: &[T]) -> Result<(), ()> {
        self.push_or_enqueue_slice(values, false)
    }

    #[inline]
    pub fn push_slice(&self, values: &[T]) -> Result<(), ()> {
        self.push_or_enqueue_slice(values, true)
    }

    /// Version of enqueue that uses memcpy to more efficiently push a larger range
    /// Only ptr::copy seems to correctly generate the memcpy so this uses that internally.
    /// If overwrite is true will drop any items overwritten.
    /// If false, will return an error if there is no space.
    #[inline]
    pub fn push_or_enqueue_slice(&self, mut values: &[T], overwrite: bool) -> Result<(), ()> {
        let mut len = values.len();

        // Short circuit this case, makes thinking about the rest of this easier
        if len == 0 {
            return Ok(());
        }

        // Clamp data to N if data is longer and we are overwriting
        if len > N {
            if overwrite {
                // If we are overwriting, we only take the last N values
                values = &values[(len - N)..];
                len = N;
            } else {
                return Err(());
            }
        }

        // Check data would fit in buffer
        if self.available_len() < len {
            // Copying will overwrite everything from [hd, hd + overlap).
            if overwrite {
                let overlap = len - self.available_len();
                if core::mem::needs_drop::<T>() {
                    for _ in 0..overlap {
                        let _ = self.dequeue();
                        // Note: drops happens here which may cause concurrent modification
                    }
                    // If the concurrent modification happens in an annoying way, just fail.
                    if self.available_len() != len {
                        return Err(());
                    }
                } else {
                    // If no dropping needed, just advance head
                    self.head
                        .set(self.head.get().wrapping_add(overlap as RingBufferInt))
                }
            } else {
                return Err(());
            }
        }

        let tl = self.tail.get();
        // Might as well advance tl now
        self.tail.set(tl.wrapping_add(len as RingBufferInt));

        // Copy [start_index,stop_index]
        let start_index = tl as usize % N;
        let stop_index = (tl as usize).wrapping_add(len) % N;

        // Cap first copy at end of array if wrap around case
        let len1 = if stop_index < start_index {
            N - start_index
        } else {
            len
        };

        let dst = self.ring.as_array_of_cells()[start_index as usize].as_ptr();
        let mut src = values.as_ptr() as *const MaybeUninit<T>;
        unsafe {
            core::ptr::copy(src, dst, len1 as usize);
        }

        // Wrap around case. Note the use of a comparison between lengths (not the stop_index < ...)
        // The first would generate a pointless copy of length-zero when stop_index was 0.
        if len1 != len {
            // Copy [0, stop_index)
            // always to the start of the ring if we wrap around
            let dst = self.ring.as_array_of_cells()[0].as_ptr();
            // we already copied len1 elements
            src = src.wrapping_add(len1 as usize);
            unsafe { core::ptr::copy(src, dst, (stop_index) as usize) }
        }

        Ok(())
    }
}

impl<'a, T: Copy> RingBuffer<'a, T> {
    pub const fn new(ring: &'a mut [T]) -> RingBuffer<'a, T> {
        RingBuffer {
            head: 0,
            tail: 0,
            ring,
        }
    }

    /// Returns the number of elements that can be enqueued until the ring buffer is full.
    pub fn available_len(&self) -> usize {
        // Applying the mod at access, rather than increment, means we can distinguish between a
        // full and empty buffer.
        self.ring.len().wrapping_sub(queue::Queue::len(self))
    }

    /// Returns up to 2 slices that together form the contents of the ring buffer.
    ///
    /// Returns:
    /// - `(None, None)` if the buffer is empty.
    /// - `(Some(slice), None)` if the head is before the tail (therefore all the contents is
    /// contiguous).
    /// - `(Some(left), Some(right))` if the head is after the tail. In that case, the logical
    /// contents of the buffer is `[left, right].concat()` (although physically the "left" slice is
    /// stored after the "right" slice).
    pub fn as_slices(&'a self) -> (Option<&'a [T]>, Option<&'a [T]>) {
        if self.head == self.tail {
            (None, None)
        } else {
            let hd = self.head % self.ring.len();
            let tl = self.tail % self.ring.len();
            if hd < tl {
                (Some(&self.ring[hd..tl]), None)
            } else {
                let (left, right) = self.ring.split_at(hd);
                (Some(right), if tl == 0 { None } else { Some(&left[..tl]) })
            }
        }
    }
}

impl<T: Copy> queue::Queue<T> for RingBuffer<'_, T> {
    fn has_elements(&self) -> bool {
        self.head != self.tail
    }

    fn is_full(&self) -> bool {
        self.len() == self.ring.len()
    }

    fn len(&self) -> usize {
        self.tail.wrapping_sub(self.head)
    }

    fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            // Incrementing tail will overwrite head
            false
        } else {
            self.ring[self.tail % self.ring.len()] = val;
            self.tail = self.tail.wrapping_add(1);
            true
        }
    }

    fn push(&mut self, val: T) -> Option<T> {
        let result = if self.is_full() {
            let val = self.ring[self.head % self.ring.len()];
            self.head = self.head.wrapping_add(1);
            Some(val)
        } else {
            None
        };

        self.ring[self.tail % self.ring.len()] = val;
        self.tail = self.tail.wrapping_add(1);
        result
    }

    fn dequeue(&mut self) -> Option<T> {
        if self.has_elements() {
            let val = self.ring[self.head % self.ring.len()];
            self.head = self.head.wrapping_add(1);
            Some(val)
        } else {
            None
        }
    }

    /// Removes the first element for which the provided closure returns `true`.
    ///
    /// This walks the ring buffer and, upon finding a matching element, removes
    /// it. It then shifts all subsequent elements forward (filling the hole
    /// created by removing the element).
    ///
    /// If an element was removed, this function returns it as `Some(elem)`.
    fn remove_first_matching<F>(&mut self, f: F) -> Option<T>
    where
        F: Fn(&T) -> bool,
    {
        let len = self.ring.len();
        let mut slot = self.head;
        while slot != self.tail {
            if f(&self.ring[slot % len]) {
                // This is the desired element, remove it and return it
                let val = self.ring[slot % len];

                let mut next_slot = slot.wrapping_add(1);
                // Move everything past this element forward in the ring
                while next_slot != self.tail {
                    self.ring[slot % len] = self.ring[next_slot % len];
                    slot = next_slot;
                    next_slot = next_slot.wrapping_add(1);
                }
                self.tail = slot;
                return Some(val);
            }
            slot = slot.wrapping_add(1);
        }
        None
    }

    fn empty(&mut self) {
        self.head = 0;
        self.tail = 0;
    }

    fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let len = self.ring.len();
        // Index over the elements before the retain operation.
        let mut src = self.head;
        // Index over the retained elements.
        let mut dst = self.head;

        while src != self.tail {
            if f(&self.ring[src % len]) {
                // When the predicate is true, move the current element to the
                // destination if needed, and increment the destination index.
                if src != dst {
                    self.ring[dst % len] = self.ring[src % len];
                }
                dst = dst.wrapping_add(1);
            }
            src = src.wrapping_add(1);
        }

        self.tail = dst;
    }
}

#[cfg(test)]
mod test {
    use super::super::queue::Queue;
    use super::RingBuffer;
    use crate::collections::ring_buffer::StaticSizedRingBuffer;

    // I didn't really want to implement the queue interface in queue.rs, but it was useful for
    // testing.

    impl<T, const N: usize> Queue<T> for StaticSizedRingBuffer<T, N> {
        fn has_elements(&self) -> bool {
            Self::has_elements(self)
        }

        fn is_full(&self) -> bool {
            Self::is_full(self)
        }

        fn len(&self) -> usize {
            Self::len(self)
        }

        fn enqueue(&mut self, val: T) -> bool {
            Self::enqueue(self, val).is_ok()
        }

        fn push(&mut self, val: T) -> Option<T> {
            Self::push(self, val).err()
        }

        fn dequeue(&mut self) -> Option<T> {
            Self::dequeue(self).ok()
        }

        fn empty(&mut self) {
            Self::empty(self)
        }

        fn retain<F>(&mut self, f: F)
        where
            F: FnMut(&T) -> bool,
        {
            Self::retain_mut(self, f)
        }
    }

    #[test]
    fn test_enqueue_dequeue() {
        const LEN: usize = 10;
        let mut ring = [0; LEN];
        let mut buf = RingBuffer::new(&mut ring);
        do_enqueue_dequeue(&mut buf, LEN);
    }

    #[test]
    fn test_enqueue_dequeue_const() {
        const LEN: usize = 10;
        let mut buf = StaticSizedRingBuffer::<usize, LEN>::new_zeros();
        do_enqueue_dequeue(&mut buf, LEN);
    }

    fn do_enqueue_dequeue<T: Queue<usize>>(buf: &mut T, len: usize) {
        // Twice length to stress going around ring at least once
        for _ in 0..2 * len {
            assert!(buf.enqueue(42));
            assert_eq!(buf.len(), 1);
            assert!(buf.has_elements());

            assert_eq!(buf.dequeue(), Some(42));
            assert_eq!(buf.len(), 0);
            assert!(!buf.has_elements());
        }
    }

    #[test]
    fn test_push() {
        const LEN: usize = 10;
        let mut ring = [0; LEN];
        let mut buf = RingBuffer::new(&mut ring);

        do_test_push(&mut buf, LEN);
    }

    #[test]
    fn test_push_const() {
        const LEN: usize = 10;
        let mut buf = StaticSizedRingBuffer::<usize, LEN>::new_zeros();
        do_test_push(&mut buf, LEN);
    }

    fn do_test_push<T: Queue<usize>>(buf: &mut T, len: usize) {
        const MAX: usize = 100;
        for i in 0..len {
            assert_eq!(buf.len(), i);
            assert!(!buf.is_full());
            assert_eq!(buf.push(i), None);
            assert!(buf.has_elements());
        }

        for i in len..MAX {
            assert!(buf.is_full());
            assert_eq!(buf.push(i), Some(i - len));
        }

        for i in 0..len {
            assert!(buf.has_elements());
            assert_eq!(buf.len(), len - i);
            assert_eq!(buf.dequeue(), Some(MAX - len + i));
            assert!(!buf.is_full());
        }

        assert!(!buf.has_elements());
    }

    // Enqueue integers 0 <= n < len, checking that it succeeds and that the
    // queue is full at the end.
    // See std::iota in C++.
    fn enqueue_iota<T: Queue<usize>>(buf: &mut T, len: usize) {
        for i in 0..len {
            assert!(!buf.is_full());
            assert!(buf.enqueue(i));
            assert!(buf.has_elements());
            assert_eq!(buf.len(), i + 1);
        }

        assert!(buf.is_full());
        assert!(!buf.enqueue(0));
        assert!(buf.has_elements());
    }

    // Dequeue all elements, expecting integers 0 <= n < len, checking that the
    // queue is empty at the end.
    // See std::iota in C++.
    fn dequeue_iota<T: Queue<usize>>(buf: &mut T, len: usize) {
        for i in 0..len {
            assert!(buf.has_elements());
            assert_eq!(buf.len(), len - i);
            assert_eq!(buf.dequeue(), Some(i));
            assert!(!buf.is_full());
        }

        assert!(!buf.has_elements());
        assert_eq!(buf.len(), 0);
    }

    // Move the head by `count` elements, by enqueueing/dequeueing `count`
    // times an element.
    // This assumes an empty queue at the beginning, and yields an empty queue.
    fn move_head<T: Queue<usize>>(buf: &mut T, count: usize) {
        assert!(!buf.has_elements());
        assert_eq!(buf.len(), 0);

        for _ in 0..count {
            assert!(buf.enqueue(0));
            assert_eq!(buf.dequeue(), Some(0));
        }

        assert!(!buf.has_elements());
        assert_eq!(buf.len(), 0);
    }

    #[test]
    fn test_fill_once() {
        const LEN: usize = 10;
        let mut ring = [0; LEN];
        let mut buf = RingBuffer::new(&mut ring);

        do_fill_once(&mut buf, LEN);
    }

    #[test]
    fn test_fill_once_const() {
        const LEN: usize = 10;
        let mut buf = StaticSizedRingBuffer::<usize, LEN>::new_zeros();
        do_fill_once(&mut buf, LEN);
    }

    fn do_fill_once<T: Queue<usize>>(buf: &mut T, len: usize) {
        assert!(!buf.has_elements());
        assert_eq!(buf.len(), 0);

        enqueue_iota(buf, len);
        dequeue_iota(buf, len);
    }

    #[test]
    fn test_refill() {
        const LEN: usize = 10;
        let mut ring = [0; LEN];
        let mut buf = RingBuffer::new(&mut ring);

        do_test_refill(&mut buf, LEN);
    }

    #[test]
    fn test_refill_const() {
        const LEN: usize = 10;
        let mut buf = StaticSizedRingBuffer::<usize, LEN>::new_zeros();
        do_test_refill(&mut buf, LEN);
    }

    fn do_test_refill<T: Queue<usize>>(buf: &mut T, len: usize) {
        for _ in 0..10 {
            enqueue_iota(buf, len);
            dequeue_iota(buf, len);
        }
    }

    #[test]
    fn test_retain() {
        const LEN: usize = 10;
        let mut ring = [0; LEN];
        let mut buf = RingBuffer::new(&mut ring);

        do_test_refill(&mut buf, LEN);
    }

    #[test]
    fn test_retain_const() {
        const LEN: usize = 10;
        let mut buf = StaticSizedRingBuffer::<usize, LEN>::new_zeros();
        do_test_refill(&mut buf, LEN);
    }

    fn do_test_retain<T: Queue<usize>>(buf: &mut T, len: usize) {
        move_head(buf, len - 2);
        enqueue_iota(buf, len);

        buf.retain(|x| x % 2 == 1);
        assert_eq!(buf.len(), len / 2);

        assert_eq!(buf.dequeue(), Some(1));
        assert_eq!(buf.dequeue(), Some(3));
        assert_eq!(buf.dequeue(), Some(5));
        assert_eq!(buf.dequeue(), Some(7));
        assert_eq!(buf.dequeue(), Some(9));
        assert_eq!(buf.dequeue(), None);
    }

    // This tests the more efficient copy
    #[test]
    fn test_copy_slice_const() {
        const LEN: usize = 100;
        let mut buf = StaticSizedRingBuffer::<usize, LEN>::new_zeros();

        let mut data: [usize; 70] = [0; 70];

        for i in 0..70 {
            data[i] = i;
        }

        move_head(&mut buf, 50);

        assert!(!buf.has_elements());

        // Push some data
        assert!(buf.push_or_enqueue_slice(&data, false).is_ok());
        assert_eq!(buf.len(), 70);
        // Push some more without clobbering existing data
        assert!(buf.push_or_enqueue_slice(&data, false).is_err());
        // Now with
        assert!(buf.push_or_enqueue_slice(&data, true).is_ok());
        assert!(buf.is_full());

        let mut data_expect: [usize; 140] = [0; 140];
        for i in 0..70 {
            data_expect[i] = i;
            data_expect[i + 70] = i;
        }
        let data_expect = &data_expect[40..140];

        for i in 0..100 {
            assert_eq!(buf.dequeue(), Ok(data_expect[i]));
        }

        assert!(!buf.has_elements());
    }

    #[test]
    fn test_dequeue_many() {
        #[derive(PartialEq, Debug)]
        struct DropInc<'a> {
            ctr: &'a std::cell::Cell<usize>,
        }
        impl Drop for DropInc<'_> {
            fn drop(&mut self) {
                self.ctr.set(self.ctr.get() + 1);
            }
        }

        let ctr = std::cell::Cell::new(0);

        let buffer = StaticSizedRingBuffer::<DropInc, 16>::new_uninit();

        for _i in 0..10 {
            assert_eq!(buffer.push(DropInc { ctr: &ctr }), Ok(()))
        }

        assert_eq!(buffer.len(), 10);

        assert_eq!(buffer.dequeue_many(6), Ok(()));

        assert_eq!(ctr.get(), 6);

        assert_eq!(buffer.dequeue_many(10), Err(()));

        assert_eq!(ctr.get(), 6);
    }

    #[test]
    fn test_as_slices_up_to() {
        let mut buf = StaticSizedRingBuffer::<usize, 10>::new_uninit();

        // Fill the buffer, with the hd in a non-trivial place.
        buf.enqueue_slice(&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
            .expect("");
        buf.dequeue_many(3).expect("");
        buf.enqueue_slice(&[10, 11, 12]).expect("");

        // Check simple case works:
        let (a, b) = buf.as_slices_up_to(4);
        assert_eq!(a, [3, 4, 5, 6]);
        assert_eq!(b, []);

        // Check the wrap around works:
        let (a, b) = buf.as_slices_up_to(10);
        assert_eq!(a, [3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(b, [10, 11, 12]);

        // And check length cap
        let (a, b) = buf.as_slices_up_to(100);
        assert_eq!(a, [3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(b, [10, 11, 12]);
    }

    fn test_iterator() {
        let mut buf = StaticSizedRingBuffer::<usize, 10>::new_uninit();

        // Fill the buffer, with the hd in a non-trivial place.
        buf.enqueue_slice(&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
            .expect("");
        buf.dequeue_many(3).expect("");
        buf.enqueue_slice(&[10, 11, 12]).expect("");
        let mut expect: usize = 3;

        for x in &mut buf {
            assert_eq!(*x, expect);
            expect += 1;
        }

        assert_eq!(expect, 13);
    }
}
