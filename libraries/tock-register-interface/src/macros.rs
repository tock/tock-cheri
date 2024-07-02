//! Macros for cleanly defining peripheral registers.

use core::mem::ManuallyDrop;
use core::ops::Deref;

/// Helper to pass through a generic parameter, whether it be a type, lifetime, or constant.
#[macro_export]
macro_rules! pass_generic {
    (const $t : ident : $x : ty) => {
        $t
    };
    ($t : ident) => {
        $t
    };
    ($life : lifetime) => {
        $life
    };
}

/// A wrapper around a T that pads it to (at least, not exactly) N bytes
pub union PaddedTo<T, const N: usize> {
    inner: ManuallyDrop<T>,
    _padding: [u8; N],
}

impl<T, const N: usize> PaddedTo<T, N> {
    pub fn new(inner: T) -> Self {
        Self {
            inner: ManuallyDrop::new(inner),
        }
    }
}

impl<T, const N: usize> Deref for PaddedTo<T, N> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safety: this is the only variant we ever construct / allow access to
        unsafe { self.inner.deref() }
    }
}

impl<T, const N: usize> core::ops::DerefMut for PaddedTo<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: this is the only variant we ever construct / allow access to
        unsafe { self.inner.deref_mut() }
    }
}

#[macro_export]
macro_rules! register_fields {
    // Macro entry point.
    (@root $(#[$attr_struct:meta])* $vis_struct:vis $name:ident $(<$($($idents : ident)* $($life : lifetime)? $(: $T: tt) ?),+>)? { $($input:tt)* } ) => {
        $crate::register_fields!(
            @munch (
                $($input)*
            ) -> {
                $vis_struct struct $(#[$attr_struct])* $name $(<$($($idents)* $($life)? $(: $T) ?),+>)?
            }
        );
    };

    // Print the struct once all fields have been munched.
    (@munch
        (
            $(#[$attr_end:meta])*
            ($offset:expr => @END),
        )
        -> {    $vis_struct:vis struct $(#[$attr_struct:meta])* $name:ident $(<$($($idents : ident)* $($life : lifetime)? $(: $T: tt) ?),+>)? $(
                $(#[$attr:meta])*
                ($vis:vis $id:ident: $ty:ty)
            )*}
    ) => {
        $(#[$attr_struct])*
        #[repr(C)]
        $vis_struct struct $name $(<$($($idents)* $($life)? $(: $T) ?),+>)?
        {
            $(
                $(#[$attr])*
                $vis $id: $ty
            ),*
        }
    };

    // Munch field.
    (@munch
        (
            $(#[$attr:meta])*
            ($offset_start:expr => $vis:vis $field:ident: $ty:ty),
            $($after:tt)*
        )
        -> {$($output:tt)*}
    ) => {
        $crate::register_fields!(
            @munch (
                $($after)*
            ) -> {
                $($output)*
                $(#[$attr])*
                ($vis $field: $ty)
            }
        );
    };

    // Munch field with dynamically calculated size.
    (@munch
        (
            $(#[$attr:meta])*
            ($offset_start:expr => pad $vis:vis $field:ident: $ty:ty),
            $(#[$attr_next:meta])*
            ($offset_end:expr => $($next:tt)*),
            $($after:tt)*
        )
        -> {$($output:tt)*}
    ) => {
        $crate::register_fields!(
            @munch (
                $(#[$attr_next])*
                ($offset_end => $($next)*),
                $($after)*
            ) -> {
                $($output)*
                $(#[$attr])*
                ($vis $field: $crate::macros::PaddedTo<$ty, {$offset_end - $offset_start}>)
            }
        );
    };

    // Munch padding.
    (@munch
        (
            $(#[$attr:meta])*
            ($offset_start:expr => $padding:ident),
            $(#[$attr_next:meta])*
            ($offset_end:expr => $($next:tt)*),
            $($after:tt)*
        )
        -> {$($output:tt)*}
    ) => {
        $crate::register_fields!(
            @munch (
                $(#[$attr_next])*
                ($offset_end => $($next)*),
                $($after)*
            ) -> {
                $($output)*
                $(#[$attr])*
                ($padding: [u8; $offset_end - $offset_start])
            }
        );
    };
}

#[macro_export]
macro_rules! test_constants {
    // Match cases where are no parameters / defaults
    (,) => ();
    ({$($anything : tt)*},) => ();
    // Match a constant
    ({{const $name : ident : $t : ty} $($rest1 : tt)* }, {{$default : tt} $($rest2 : tt)*}) =>
    (
        const $name : $t = $default;
        $crate::test_constants!({$($rest1)*}, {$($rest2)*});
    );
    // Match a lifetime (outputs nothing)
    ({{$l : lifetime} $($rest1 : tt)* }, {$($rest2 : tt)*}) =>
    (
        $crate::test_constants!({$($rest1)*}, {$($rest2)*});
    );
    // Match a type
    ({{$name : ident : $t : tt} $($rest1 : tt)* }, {{$default : tt} $($rest2 : tt)*}) =>
    (
        type $name = $default;
        $crate::test_constants!({$($rest1)*} {$($rest2)*});
    );
    // Finish
    ({}, {}) => ();
}

// TODO: All of the rustdoc tests below use a `should_fail` attribute instead of
// `should_panic` because a const panic will result in a failure to evaluate a
// constant value, and thus a compiler error. However, this means that these
// examples could break for unrelated reasons, trigger a compiler error, but not
// test the desired assertion any longer. This should be switched to a
// `should_panic`-akin attribute which works for const panics, once that is
// available.
/// Statically validate the size and offsets of the fields defined
/// within the register struct through the `register_structs!()`
/// macro.
///
/// This macro expands to an expression which contains static
/// assertions about various parameters of the individual fields in
/// the register struct definition. It will test for:
///
/// - Proper start offset of padding fields. It will fail in cases
///   such as
///
///   ```should_fail
///   # #[macro_use]
///   # extern crate tock_registers;
///   # use tock_registers::register_structs;
///   # use tock_registers::registers::ReadWrite;
///   register_structs! {
///       UartRegisters {
///           (0x04 => _reserved),
///           (0x08 => foo: ReadWrite<u32>),
///           (0x0C => @END),
///       }
///   }
///   # // This is required for rustdoc to not place this code snipped into an
///   # // fn main() {...} function.
///   # fn main() { }
///   ```
///
///   In this example, the start offset of `_reserved` should have been `0x00`
///   instead of `0x04`.
///
/// - Correct start offset and end offset (start offset of next field) in actual
///   fields. It will fail in cases such as
///
///   ```should_fail
///   # #[macro_use]
///   # extern crate tock_registers;
///   # use tock_registers::register_structs;
///   # use tock_registers::registers::ReadWrite;
///   register_structs! {
///       UartRegisters {
///           (0x00 => foo: ReadWrite<u32>),
///           (0x05 => bar: ReadWrite<u32>),
///           (0x08 => @END),
///       }
///   }
///   # // This is required for rustdoc to not place this code snipped into an
///   # // fn main() {...} function.
///   # fn main() { }
///   ```
///
///   In this example, the start offset of `bar` and thus the end offset of
///   `foo` should have been `0x04` instead of `0x05`.
///
/// - Invalid alignment of fields.
///
/// - That the end marker matches the actual generated struct size. This will
///   fail in cases such as
///
///   ```should_fail
///   # #[macro_use]
///   # extern crate tock_registers;
///   # use tock_registers::register_structs;
///   # use tock_registers::registers::ReadWrite;
///   register_structs! {
///       UartRegisters {
///           (0x00 => foo: ReadWrite<u32>),
///           (0x04 => bar: ReadWrite<u32>),
///           (0x10 => @END),
///       }
///   }
///   # // This is required for rustdoc to not place this code snipped into an
///   # // fn main() {...} function.
///   # fn main() { }
///   ```
#[macro_export]
macro_rules! test_fields {
    // This macro works by iterating over all defined fields, until it hits an
    // ($size:expr => @END) field. Each iteration generates an expression which,
    // when evaluated, yields the current byte offset in the fields. Thus, when
    // reading a field or padding, the field or padding length must be added to
    // the returned size.
    //
    // By feeding this expression recursively into the macro, deeper invocations
    // can continue validating fields through knowledge of the current offset
    // and the remaining fields.
    //
    // The nested expression returned by this macro is guaranteed to be
    // const-evaluable.

    // Macro entry point.
    (@root $struct:ident $(<$($($idents : ident)* $($life : lifetime)? $(: $T: tt) ?),+>)?  $(test_defaults<$($default : tt),*>)? { $($input:tt)* } ) => {
        // Start recursion at offset 0.
        $crate::test_constants!($({$({$($idents)* $($life)? $(: $T) ?})+})?, $({$({$default})*})?);
        $crate::test_fields!(@munch $struct $(<$($($idents)* $($life)? $(: $T) ?),+>)? ($($input)*) : (0, 0));
    };

    // Consume the ($size:expr => @END) field, which MUST be the last field in
    // the register struct.
    (@munch $struct:ident $(<$($($idents : ident)* $($life : lifetime)? $(: $T: tt) ?),+>)?
        (
            $(#[$attr_end:meta])*
            ($size:expr => @END),
        )
        : $stmts:expr
    ) => {
        const _: () = {
            // We've reached the end! Normally it is sufficient to compare the
            // struct's size to the reported end offet. However, we must
            // evaluate the previous iterations' expressions for them to have an
            // effect anyways, so we can perform an internal sanity check on
            // this value as well.
            const SUM_MAX_ALIGN: (usize, usize) = $stmts;
            const SUM: usize = SUM_MAX_ALIGN.0;
            const MAX_ALIGN: usize = SUM_MAX_ALIGN.1;

            // Internal sanity check. If we have reached this point and
            // correctly iterated over the struct's fields, the current offset
            // and the claimed end offset MUST be equal.
            assert!(SUM == $size);

            const STRUCT_SIZE: usize = core::mem::size_of::<$struct $(<$($crate::pass_generic!($($idents)* $($life)? $(: $T) ?)),+>)?>();
            const ALIGNMENT_CORRECTED_SIZE: usize = if $size % MAX_ALIGN != 0 { $size + (MAX_ALIGN - ($size % MAX_ALIGN)) } else { $size };

            assert!(
                STRUCT_SIZE == ALIGNMENT_CORRECTED_SIZE,
                "{}",
                concat!(
                    "Invalid size for struct ",
                    stringify!($struct),
                    " (expected ",
                    stringify!($size),
                    ", actual struct size differs)",
                ),
            );

        };
    };

    // Consume a proper ($offset:expr => pad $field:ident: $ty:ty) field.
    (@munch $struct:ident $(<$($($idents : ident)* $($life : lifetime)? $(: $T: tt) ?),+>)?
        (
            $(#[$attr:meta])*
            ($offset_start:expr => pad $vis:vis $field:ident: $ty:ty),
            $(#[$attr_next:meta])*
            ($offset_end:expr => $($next:tt)*),
            $($after:tt)*
        )
        : $output:expr
    ) => {
        // Just replace the type and then use the non-pad matcher
        $crate::test_fields!(@munch $struct $(<$($($idents)* $($life)? $(: $T) ?),+>)?
        (
            $(#[$attr])*
            ($offset_start => $vis $field: $crate::macros::PaddedTo<$ty, {$offset_end - $offset_start}>),
            $(#[$attr_next])*
            ($offset_end => $($next)*),
            $($after)*
        )
        : $output
        );
    };

    // Consume a proper ($offset:expr => $field:ident: $ty:ty) field.
    (@munch $struct:ident $(<$($($idents : ident)* $($life : lifetime)? $(: $T: tt) ?),+>)?
        (
            $(#[$attr:meta])*
            ($offset_start:expr => $vis:vis $field:ident: $ty:ty),
            $(#[$attr_next:meta])*
            ($offset_end:expr => $($next : tt)*),
            $($after:tt)*
        )
        : $output:expr
    ) => {
        $crate::test_fields!(
            @munch $struct $(<$($($idents)* $($life)? $(: $T) ?),+>)? (
                $(#[$attr_next])*
                ($offset_end => $($next)*),
                $($after)*
            ) : {
                // Evaluate the previous iterations' expression to determine the
                // current offset.
                const SUM_MAX_ALIGN: (usize, usize) = $output;
                const SUM: usize = SUM_MAX_ALIGN.0;
                const MAX_ALIGN: usize = SUM_MAX_ALIGN.1;

                // Validate the start offset of the current field. This check is
                // mostly relevant for when this is the first field in the
                // struct, as any subsequent start offset error will be detected
                // by an end offset error of the previous field.
                assert!(
                    SUM == $offset_start,
                    "{}",
                    concat!(
                        "Invalid start offset for field ",
                        stringify!($field),
                        " (expected ",
                        stringify!($offset_start),
                        " but actual value differs)",
                    ),
                );

                // Validate that the start offset of the current field within
                // the struct matches the type's minimum alignment constraint.
                const ALIGN: usize = core::mem::align_of::<$ty>();
                // Clippy can tell that (align - 1) is zero for some fields, so
                // we allow this lint and further encapsule the assert! as an
                // expression, such that the allow attr can apply.
                #[allow(clippy::bad_bit_mask)]
                {
                    assert!(
                        SUM & (ALIGN - 1) == 0,
                        "{}",
                        concat!(
                            "Invalid alignment for field ",
                            stringify!($field),
                            " (offset differs from expected)",
                        ),
                    );
                }

                // Add the current field's length to the offset. This is validated by the next
                // iteration (unless the wildcard _ is used).
                const NEW_SUM: usize = SUM + core::mem::size_of::<$ty>();
                assert!(
                    NEW_SUM == $offset_end,
                    "{}",
                    concat!(
                        "Invalid end offset for field ",
                        stringify!($field),
                        " (expected ",
                        stringify!($offset_end),
                        " but actual value differs)",
                    ),
                );

                // Determine the new maximum alignment. core::cmp::max(ALIGN,
                // MAX_ALIGN) does not work here, as the function is not const.
                const NEW_MAX_ALIGN: usize = if ALIGN > MAX_ALIGN { ALIGN } else { MAX_ALIGN };

                // Provide the updated offset and alignment to the next
                // iteration.
                (NEW_SUM, NEW_MAX_ALIGN)
            }
        );
    };

    // Consume a padding ($offset:expr => $padding:ident) field.
    (@munch $struct:ident $(<$($($idents : ident)* $($life : lifetime)? $(: $T: tt) ?),+>)?
        (
            $(#[$attr:meta])*
            ($offset_start:expr => $padding:ident),
            $(#[$attr_next:meta])*
            ($offset_end:expr => $($next:tt)*),
            $($after:tt)*
        )
        : $output:expr
    ) => {
        $crate::test_fields!(
            @munch $struct $(<$($($idents)* $($life)? $(: $T) ?),+>)? (
                $(#[$attr_next])*
                ($offset_end => $($next)*),
                $($after)*
            ) : {
                // Evaluate the previous iterations' expression to determine the
                // current offset.
                const SUM_MAX_ALIGN: (usize, usize) = $output;
                const SUM: usize = SUM_MAX_ALIGN.0;
                const MAX_ALIGN: usize = SUM_MAX_ALIGN.1;

                // Validate the start offset of the current padding field. This
                // check is mostly relevant for when this is the first field in
                // the struct, as any subsequent start offset error will be
                // detected by an end offset error of the previous field.
                assert!(
                    SUM == $offset_start,
                    concat!(
                        "Invalid start offset for padding ",
                        stringify!($padding),
                        " (expected ",
                        stringify!($offset_start),
                        " but actual value differs)",
                    ),
                );

                // The padding field is automatically sized. Provide the start
                // offset of the next field to the next iteration.
                ($offset_end, MAX_ALIGN)
            }
        );
    };
}

#[macro_export]
macro_rules! register_structs {
    {
        $(
            $(#[$attr:meta])*
            $vis_struct:vis $name:ident$(<$($($idents : ident)* $($life : lifetime)? $(: $T: tt) ? ),+>)?  $(test_defaults<$($default : tt),*>)? {
                $( $fields:tt )*
            }
        ),*
    } => {
        $( $crate::register_fields!(@root $(#[$attr])* $vis_struct $name $(<$($($idents)* $($life)? $(: $T) ?),+>)? { $($fields)* } ); )*

        mod static_validate_register_structs {
        $(
            #[allow(non_snake_case)]
            mod $name {
                use super::super::*;

                $crate::test_fields!(@root $name $(<$($($idents)* $($life)? $(: $T) ?),+>)?  $(test_defaults<$($default),*>)? { $($fields)* } );
            }
        )*
        }
    };
}
