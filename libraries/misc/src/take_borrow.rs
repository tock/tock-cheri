//! Take borrow helper.
//! Allows borrowing from containers that have a take interface by taking the value, borrowing the
//! moved value, then moving it back after the borrow ends.

use core::cell::Cell;
use core::mem::take;
use core::ops::{Deref, DerefMut};

/// It gets tedious to call take, mutate a value, then set on Cells. This allows a single method
/// call to quickly get a mutable reference to Cell contents that needs putting back after.
/// e.g.:
/// ```
/// use core::cell::Cell;
/// use misc::take_borrow::TakeBorrow;
/// pub fn is_some(arg : &Cell<Option<&mut i32>>) -> bool {
///     arg.take_borrow().is_some()
/// }
/// // Instead of
/// pub fn is_some_but_annoying_to_write(arg : &Cell<Option<&mut i32>>) -> bool {
///     let tmp = arg.take();
///     let result = tmp.is_some();
///     arg.set(tmp);
///     result
/// }
/// ```
/// Care should be taken not to access the cell again for the lifetime of a CellTakeBorrow.
/// Although doing so is not unsafe, the Cell will be found empty, and will be over-written
/// later. This is no different from accidentally accessing a Cell that has just has "take" called
/// on it.
pub struct CellTakeBorrow<'a, T: Default> {
    cell_ref: &'a Cell<T>,
    val: T,
}

/// The trait that offers the take_borrow method, which borrows by first taking a value and
/// borrowing that. The value is automatically put back afterwards.
pub trait TakeBorrow {
    type Output<'a>
    where
        Self: 'a;
    /// Take the value out of self, borrow that, and set it back again when that borrow ends
    fn take_borrow(&self) -> Self::Output<'_>;
}

impl<'a, T: Default> Drop for CellTakeBorrow<'a, T> {
    #[inline(always)]
    fn drop(&mut self) {
        self.cell_ref.set(take(&mut self.val));
    }
}

impl<T: Default> TakeBorrow for Cell<T> {
    type Output<'a> = CellTakeBorrow<'a, T> where Self: 'a,;

    #[inline(always)]
    fn take_borrow(&self) -> Self::Output<'_> {
        CellTakeBorrow {
            cell_ref: self,
            val: self.take(),
        }
    }
}

impl<'a, T: Default> Deref for CellTakeBorrow<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.val
    }
}

impl<'a, T: Default> DerefMut for CellTakeBorrow<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.val
    }
}

#[cfg(test)]
mod tests {
    use crate::take_borrow::TakeBorrow;
    use core::cell::Cell;

    #[derive(Copy, Clone, Default)]
    struct SimpleThing {
        val: u32,
    }

    impl SimpleThing {
        fn increment(&mut self) {
            self.val += 1;
        }
    }

    // Test the expected use of take_borrow
    #[test]
    fn simple_test() {
        let cell = Cell::<SimpleThing>::new(SimpleThing { val: 123 });
        let r1 = &cell;
        let r2 = &cell;
        r1.take_borrow().increment();
        assert_eq!(cell.get().val, 124);
        r2.take_borrow().increment();
        assert_eq!(cell.get().val, 125);
        r1.take_borrow().increment();
        assert_eq!(cell.take().val, 126);
    }

    // Test clobbering works as expected
    #[test]
    fn clobber_test() {
        let cell = Cell::<SimpleThing>::new(SimpleThing { val: 123 });

        let mut borrow = cell.take_borrow();

        // While borrowed, value should go back to its default value
        assert_eq!(cell.get().val, 0);
        cell.set(SimpleThing { val: 13 });
        assert_eq!(cell.get().val, 13);

        borrow.increment();
        assert_eq!(cell.get().val, 13);

        drop(borrow);
        assert_eq!(cell.get().val, 124);
    }
}
