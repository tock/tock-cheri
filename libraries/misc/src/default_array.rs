//! Trait for constructing default arrays. Rust can only do this up to 32 elements.

use core::mem::MaybeUninit;

/// A version of default that works better inside arrays.
/// Arrays automatically implement this if elements do.
/// Non-array types must be marked with NotArrayMarker to support this interface.
pub trait DefaultArray: Sized {
    /// Construct a default value, filling arrays with repeated calls to default.
    fn default_array() -> Self;
}

/// Implement this for your non-array types if they are to be used with DefaultArray.
pub trait NotArrayMarker {}

// Blanket definitions. Without specialisation there is no way of implementing something only
// for non-array types unless we use a marker.

impl<T: DefaultArray, const M: usize> DefaultArray for [T; M] {
    fn default_array() -> Self {
        unsafe {
            // Safety: iterating to M guarantees being in bounds. We only write each element
            // once so are not forgetting to drop anything, and are definitely initializing
            // everything.
            let mut mem = MaybeUninit::<[T; M]>::uninit();
            for i in 0..M {
                (*mem.as_mut_ptr())[i] = T::default_array();
            }
            mem.assume_init()
        }
    }
}

impl<T: Default + NotArrayMarker> DefaultArray for T {
    fn default_array() -> Self {
        T::default()
    }
}

#[cfg(test)]
mod tests {
    use crate::default_array::{DefaultArray, NotArrayMarker};

    struct MyThingDefault {
        v: i32,
    }

    impl Default for MyThingDefault {
        fn default() -> Self {
            Self { v: 6 }
        }
    }

    // Implementing NotArrayMarker allows use of DefaultArray::default_array()
    impl NotArrayMarker for MyThingDefault {}

    #[test]
    fn test_single() {
        let single: MyThingDefault = DefaultArray::default_array();
        assert_eq!(single.v, 6);
    }

    #[test]
    fn test_1d() {
        let array: [MyThingDefault; 100] = DefaultArray::default_array();
        for el in array {
            assert_eq!(el.v, 6);
        }
    }

    #[test]
    fn test_2d() {
        let twod: [[MyThingDefault; 100]; 100] = DefaultArray::default_array();
        for row in twod {
            for el in row {
                assert_eq!(el.v, 6);
            }
        }
    }

    #[test]
    fn test_3d() {
        let threed: [[[MyThingDefault; 40]; 40]; 40] = DefaultArray::default_array();
        for twod in threed {
            for row in twod {
                for el in row {
                    assert_eq!(el.v, 6);
                }
            }
        }
    }
}
