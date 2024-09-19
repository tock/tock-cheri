// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Google LLC 2024.

use core::cell::Cell;
use core::cmp::PartialOrd;
use core::mem;
use core::mem::MaybeUninit;
use core::ops::{AddAssign, Not};

/// An allocator for unsigned integers from [0,MAX_V)
/// Calling free on an integer not allocated is allowed to cause all future allocations to return
/// any value.
/// Usage:
///
/// ```
/// use crate::misc::unsigned_allocators::UnsignedAllocator;
/// let mut my_allocator = misc::unsigned_allocators::ArrayUnsignedAllocator::<i8, 66>::default();
/// let int1 : u8 = my_allocator.alloc().unwrap();
/// let int2 : u8 = my_allocator.alloc().unwrap();
/// let int3 : u8 = my_allocator.alloc().unwrap();
/// // some_use(int1, int2, int3);
/// my_allocator.free(int1);
/// my_allocator.free(int2);
/// // some_use(int3);
/// my_allocator.free(int3);
/// ```
///
pub trait UnsignedAllocator<T, const MAX_V: usize> {
    fn alloc(&mut self) -> Option<T>;
    fn free(&mut self, val: T);
}

/// An allocator over unsigned integers [0,MAX_V). T AND Ts must be able to hold MAX_V
/// For example. Valid:
/// ```
/// use misc::unsigned_allocators::ArrayUnsignedAllocator;
/// type A = ArrayUnsignedAllocator<i8, 5>;
/// type B = ArrayUnsignedAllocator<i8, 127>;
/// type C = ArrayUnsignedAllocator<i16, 777>;
/// ```
/// Invalid:
/// ```should_fail
///  ArrayUnsignedAllocator<i8, 128>;
/// ```
pub struct ArrayUnsignedAllocator<Ts, const MAX_V: usize> {
    next_free: Ts,
    vals: [MaybeUninit<Ts>; MAX_V],
}

/// This trait is meant to provide a generic interface for the 'as' keyword for integers.
///
/// Equivalent:
/// ```
/// use misc::unsigned_allocators::As;
/// type C = u16;
/// let b : u8 = 0;
///
/// let a = b as C;
/// let a = C::from_as(b);
/// let a : C = b.into_as();
/// ```
///
/// `Into`/`From` is not provided for integer types that do not fit into each other.
/// e.g., there is no `Into<u8>` for `i8`, etc.
/// Lossy conversion is supplied via the "as" keyword, which does not work for generics as it is not
/// also a trait for a reason beyond me.
/// I am sure some of this would be in the numbers crate, but we don't pull that in.
pub trait As<Target> {
    fn into_as(self) -> Target;
    fn from_as(from: Target) -> Self;
}

// Auto generate all 100 combinations.
macro_rules! cast_to_from {
    ($to : ty, $from : ty) => {
        impl As<$to> for $from {
            fn into_as(self) -> $to {
                self as $to
            }
            fn from_as(from: $to) -> Self {
                from as Self
            }
        }
    };
}
macro_rules! cast_to_all {
    ($from: ty) => {
        cast_to_from!(u8, $from);
        cast_to_from!(i8, $from);
        cast_to_from!(u16, $from);
        cast_to_from!(i16, $from);
        cast_to_from!(u32, $from);
        cast_to_from!(i32, $from);
        cast_to_from!(u64, $from);
        cast_to_from!(i64, $from);
        cast_to_from!(usize, $from);
        cast_to_from!(isize, $from);
    };
}
cast_to_all!(u8);
cast_to_all!(i8);
cast_to_all!(u16);
cast_to_all!(i16);
cast_to_all!(u32);
cast_to_all!(i32);
cast_to_all!(u64);
cast_to_all!(i64);
cast_to_all!(usize);
cast_to_all!(isize);

/// Explanation of this implementation:
/// This allocator has two modes:
///     Mode one: a simple counter that counts from free numbers. The counter is stored as itself
///     in 'next_free'
///     Mode two: an intrusive free-chain through the array. Links are stored as _complement_ of the
///     index in order to not confuse with the counter.
impl<
        Ts: PartialOrd + Not + AddAssign + As<usize> + Copy + From<<Ts as Not>::Output>,
        T: As<Ts> + As<usize> + Copy,
        const MAX_V: usize,
    > UnsignedAllocator<T, MAX_V> for ArrayUnsignedAllocator<Ts, MAX_V>
{
    fn alloc(&mut self) -> Option<T> {
        // The first branch path is for when the next free item is the head of a linked list
        // through the array.
        if self.next_free < Ts::from_as(0usize) {
            // Values < 0 are complements of the index of the next free item, so complement again
            let res: T = T::from_as(Ts::from(!self.next_free));
            // Read next free item from list
            // Safety: the only time we store an index is when it was freed, which would
            // initialise this element in the array.
            unsafe {
                self.next_free = self.vals[<T as As<usize>>::into_as(res)].assume_init();
            }
            // Return result
            Some(res)
        } else {
            // Values >= 0 are a counter over free items
            if self.next_free == Ts::from_as(MAX_V) {
                // If the counter has hit the max value, we can allocate no more
                None
            } else {
                // Otherwise increment and return
                let res = T::from_as(self.next_free);
                self.next_free += Ts::from_as(1);
                Some(res)
            }
        }
    }

    fn free(&mut self, val: T) {
        let ndx: usize = <T as As<usize>>::into_as(val);
        // Add the current next free into the free list
        self.vals[ndx].write(self.next_free);
        // Store the (negative) of the value we just freed as the head of the free list
        self.next_free = <Ts as As<usize>>::from_as(!ndx);
    }
}

impl<Ts: As<u8>, const MAX_V: usize> Default for ArrayUnsignedAllocator<Ts, MAX_V> {
    fn default() -> Self {
        ArrayUnsignedAllocator {
            next_free: Ts::from_as(0u8),
            // Vals are MaybeUninit which do not require initialization
            vals: unsafe { mem::MaybeUninit::uninit().assume_init() },
        }
    }
}

/// Stores state as a bitfield
pub struct BitfieldAllocator<const N: usize> {
    // 0 means used, 1 means free.
    val: Cell<usize>,
}

impl<const N: usize> BitfieldAllocator<N> {
    #[inline]
    pub const fn new() -> Self {
        let bits = mem::size_of::<usize>() * 8;
        assert!(N <= bits);
        Self {
            // N set ones in the low bits
            val: Cell::new(
                // Handle shift by bits of usize as special case
                if N == bits { !0 } else { (1 << N) - 1 },
            ),
        }
    }

    pub fn alloc(&self) -> Option<u8> {
        let v = self.val.get();

        if v == 0 {
            return None;
        }

        let result = v.trailing_zeros();

        // Clear the result bit to allocate it
        self.val.set(v ^ (1usize << result as usize));

        Some(result as u8)
    }

    pub fn free(&self, val: u8) {
        // Set the val'th bit to free it.
        self.val.set(self.val.get() | (1usize << val as usize));
    }
}

#[cfg(test)]
mod tests {
    use crate::unsigned_allocators::{
        ArrayUnsignedAllocator, BitfieldAllocator, UnsignedAllocator,
    };

    const N: usize = 7;

    fn alloc_all(alloc: &BitfieldAllocator<N>, used: &mut [bool; N]) {
        for _ in 0..N {
            let result = alloc.alloc();
            assert!(result.is_some());
            let result = result.unwrap();
            assert!(!used[result as usize]);
            used[result as usize] = true;
        }
    }

    #[test]
    fn bitfield_max() {
        let alloc = BitfieldAllocator::<N>::new();

        let mut used: [bool; N] = [false; N];

        alloc_all(&alloc, &mut used);

        // Now we allocated max items we should get none
        assert!(alloc.alloc().is_none())
    }

    #[test]
    fn bitfield_reuse() {
        const N: usize = 7;
        let alloc = BitfieldAllocator::<N>::new();

        let mut used: [bool; N] = [false; N];

        // Allocate and de-allocate a few times
        for _ in 0..2 {
            // Allocate all
            alloc_all(&alloc, &mut used);

            // Free all
            for i in 0..N {
                alloc.free(i as u8);
                used[i] = false;
            }
        }
    }

    #[test]
    fn small_test() {
        let mut my_alloc: ArrayUnsignedAllocator<i8, 100> = Default::default();

        // Try allocating all the numbers
        for i in 0u8..100u8 {
            assert_eq!(my_alloc.alloc(), Some(i))
        }

        // No more should be possible
        assert_eq!(UnsignedAllocator::<u8, 100>::alloc(&mut my_alloc), None);

        // Free some up
        my_alloc.free(1u8);
        my_alloc.free(7u8);
        my_alloc.free(16u8);

        // Allocate them again
        assert_eq!(my_alloc.alloc(), Some(16u8));
        assert_eq!(my_alloc.alloc(), Some(7u8));
        assert_eq!(my_alloc.alloc(), Some(1u8));
    }

    #[test]
    fn larger_test() {
        let mut my_alloc: ArrayUnsignedAllocator<i16, 1000> = Default::default();

        // Try allocating some the numbers
        for i in 0u16..100u16 {
            assert_eq!(my_alloc.alloc(), Some(i))
        }

        // Free the even ones
        for i in 0u16..50u16 {
            my_alloc.free(2 * i);
        }

        // Allocate them again
        for i in 0u16..50u16 {
            assert_eq!(my_alloc.alloc(), Some(98 - (2 * i)));
        }

        // Go back to allocating in order
        for i in 100u16..1000u16 {
            assert_eq!(my_alloc.alloc(), Some(i));
        }
    }
}
