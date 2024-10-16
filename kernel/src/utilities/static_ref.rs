//! Wrapper type for safe pointers to static memory.

use core::ops::Deref;

/// A pointer to statically allocated mutable data such as memory mapped I/O
/// registers.
///
/// This is a simple wrapper around a raw pointer that encapsulates an unsafe
/// dereference in a safe manner. It serve the role of creating a `&'static T`
/// given a raw address and acts similarly to `extern` definitions, except
/// `StaticRef` is subject to module and crate boundaries, while `extern`
/// definitions can be imported anywhere.
#[derive(Debug)]
pub struct StaticRef<T> {
    ptr: *const T,
}

impl<T> StaticRef<T> {
    /// Create a new `StaticRef` from a raw pointer
    ///
    /// ## Safety
    ///
    /// Callers must pass in a reference to statically allocated memory which
    /// does not overlap with other values.
    pub const unsafe fn new(ptr: *const T) -> StaticRef<T> {
        StaticRef { ptr: ptr }
    }

    pub const fn unwrap(&self) -> *const T {
        self.ptr
    }
}

/// This macro, given a StaticRef to a struct, constructs a StaticRef to a member of said struct.
/// i.e., `StaticRefGEP(struct, field)` is meant to be the same as `&struct.field`.
/// StaticRef often refers to addresses that do not really exist within a const-expr because they
/// only represent an allocation at runtime (e.g., a memory-mapped device)
/// Reading one is almost certainly an error. It is therefore sensible that Deref cannot be applied
/// as a const-fn.
/// Sadly, the syntax for accessing a element point of a struct &(struct.field) implicitly makes
/// a deref. The compiler can spot a deref of a location that does not exist, and will create
/// an error.
/// This macro operates StaticRefGEP in such a way as not to invoke any UB or implicit dereferences
/// of locations that are not allocated.
#[macro_export]
macro_rules! StaticRefGEP {
    ($from : expr, $field : ident) => {
        unsafe {
            // An explanation of what is happening here:
            // We would like to simply write: &$from.unwrap().$field to get a ptr to the field.
            // But there are two problems with that:

            // 1) It (very briefly) constructs a reference that does not exist
            // 2) Does arithmetic on a pointer range that is out of bounds.

            // core::ptr::addr_of! normally solves (1)
            // (2) Is pretty tricky to get around. You cannot cast pointers to usize with a const
            // expr because at compile time pointers do not have integer values.
            // Also, our pointer is very much out of bounds at compile time because the device
            // does not really exist at that point.
            // Methods like offset() and add() must result in a within bounds pointer.
            // wrapping_offset is pretty useful in that it is allowed to construct an OOB
            // pointer. We first construct a stand-in maybe uninit object of the same type as the real
            // reference. We can work out the offset of the field on the stand_in.
            // We then use wrapping_offset on the "real" pointer.
            // The functions here just exist to help infer the types of the object and element
            // because type_of does not exist in rust.
            const fn cast_helper<V>(raw_ptr: *const u8, _ref: *const V) -> *const V {
                raw_ptr as *const V
            }
            const fn make_stand_in<T>(_raw_ptr: *const T) -> core::mem::MaybeUninit<T> {
                core::mem::MaybeUninit::uninit()
            }
            let raw_ptr = $from.unwrap();
            let stand_in_alloc = make_stand_in(raw_ptr);
            let stand_in = stand_in_alloc.as_ptr();
            let stand_in_field = core::ptr::addr_of!((*stand_in).$field);
            let offset = (stand_in_field as *const u8).offset_from(stand_in as *const u8);
            StaticRef::new(cast_helper(
                (raw_ptr as *const u8).wrapping_offset(offset),
                stand_in_field,
            ))
        }
    };
}

impl<T> Clone for StaticRef<T> {
    fn clone(&self) -> Self {
        StaticRef { ptr: self.ptr }
    }
}

impl<T> Copy for StaticRef<T> {}

impl<T> Deref for StaticRef<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}
