//! Allows leasing part of a buffer and then restoring the original (See LeasableBuffer as well).

use core::cell::Cell;
use core::marker::PhantomData;
use core::ops::IndexMut;
use core::ops::Range;
use core::ptr::NonNull;

/// Leasable buffer must pass a different type to the receiver but cannot fail.
/// Leased buffer passes a normal &mut reference and so does not complicate the receiver,
/// but performs a dynamic check and can therefore fail.
/// Either this needs to be handled, or the buffer will be lost in the event of error.
pub struct LeasedBuffer<'a, T> {
    original: NonNull<[T]>,
    leased: NonNull<[T]>,
    p: PhantomData<&'a mut T>,
}

/// A wrapper for leased buffer to easily set/take interface
pub struct LeasedBufferCell<'a, T> {
    inner: Cell<LeasedBuffer<'a, T>>,
}

impl<'a, T> LeasedBufferCell<'a, T> {
    pub const fn new() -> Self {
        Self {
            inner: Cell::new(LeasedBuffer::empty()),
        }
    }
    /// Return v.get(range) and put the rest in the cell
    pub fn set_lease(&self, v: &'a mut [T], range: Range<usize>) -> &'a mut [T] {
        let (lease, result) = LeasedBuffer::lease(v, range);
        self.inner.set(lease);
        result
    }
    /// Restore from the cell part of the leased buffer
    pub fn take_buf(&self, lease: &'a mut [T]) -> &'a mut [T] {
        let leased = self.inner.replace(LeasedBuffer::empty());
        leased.restore_min(lease)
    }
}

impl<'a, T> LeasedBuffer<'a, T> {
    /// Lease a sub-range of a slice.
    /// Can be restored later with restore.
    #[inline]
    pub fn lease(v: &'a mut [T], range: Range<usize>) -> (Self, &'a mut [T]) {
        let original = NonNull::from(&*v);
        let sub_range = v.index_mut(range);
        let leased = NonNull::from(&*sub_range);
        (
            Self {
                original,
                leased,
                p: PhantomData,
            },
            sub_range,
        )
    }

    #[inline]
    /// A state that would never restore with anything, saves wrapping with an Option
    pub const fn empty() -> Self {
        Self {
            original: NonNull::slice_from_raw_parts(NonNull::dangling(), 0),
            leased: NonNull::slice_from_raw_parts(NonNull::dangling(), 0),
            p: PhantomData,
        }
    }

    /// Restore leased part of buffer.
    /// If it does not match exactly, Err(()) is returned.
    #[inline]
    pub fn restore(mut self, leased: &'a mut [T]) -> Result<&'a mut [T], ()> {
        if NonNull::from(&*leased).eq(&self.leased) {
            unsafe {
                // Safety: we are giving back exactly the same reference with the same lifetime
                // this means that the we can restore the original reference
                Ok(self.original.as_mut())
            }
        } else {
            Err(())
        }
    }
    /// Restore leased part of buffer.
    /// If it does not match exactly, the leased buffer is returned
    #[inline]
    pub fn restore_min(mut self, leased: &'a mut [T]) -> &'a mut [T] {
        if NonNull::from(&*leased).eq(&self.leased) {
            unsafe {
                // Safety: same as restore
                self.original.as_mut()
            }
        } else {
            leased
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::utilities::leased_buffer::LeasedBufferCell;

    #[test]
    fn test_lease() {
        let buf = &mut [1, 2, 3, 4];

        let cell = LeasedBufferCell::new();

        let part = cell.set_lease(buf, 1..2);

        // Buf no longer usable
        // buf[1] = 2; // error

        assert_eq!(part[0], 2);

        // Get the buffer back
        let whole_buf = cell.take_buf(part);

        assert_eq!(whole_buf[0], 1);
        assert_eq!(whole_buf[3], 4);
    }

    #[test]
    fn test_wrong_buffer() {
        let buf = &mut [1, 2, 3, 4];

        let cell = LeasedBufferCell::new();

        let part = cell.set_lease(buf, 1..3);

        assert_eq!(part[0], 2);

        let other = &mut [2, 3, 4, 5, 6, 7, 8];

        // Get the buffer back
        let whole_buf = cell.take_buf(other);

        assert_eq!(whole_buf.len(), 7);
    }

    #[test]
    fn test_wrong_buffer_length() {
        let buf = &mut [1, 2, 3, 4];

        let cell = LeasedBufferCell::new();

        let part = cell.set_lease(buf, 1..3);

        assert_eq!(part[0], 2);

        let part = &mut part[0..1];

        // Get the buffer back
        let whole_buf = cell.take_buf(part);

        assert_eq!(whole_buf.len(), 1);
    }

    #[test]
    fn test_empty() {
        let buf = &mut [1, 2, 3, 4];

        let cell = LeasedBufferCell::new();

        let x = cell.take_buf(buf);

        assert!(x.eq(&[1, 2, 3, 4]));
    }
}
