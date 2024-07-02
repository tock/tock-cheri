//! A helper type to allow statically overloading traits or implement foreign traits for foregin
//! types.

/// Create an overload for base, called overloaded.
/// References to one can be treated as references to the other.
/// You cannot rely on the overload having any constraints other than those imposed by
/// the type it wraps.
/// Usage:
/// ```
/// #![feature(const_mut_refs)]
/// trait ForeignTrait{};
/// struct ForeignType;
/// // ...
/// use misc::overload_impl;
/// overload_impl!(MyWrapper);
/// impl ForeignTrait for MyWrapper<ForeignType> {
/// }
/// ```
/// The wrapped type is accessible via the public inner field.
/// Transmute to the wrapper using `MyWrapper<ForeignType>::get(&unwrapped)`
/// If you need to constrain a type with phantom data, there is second
/// parameter to every type created for that purpose:
/// e.g.: `MyWrapper<ForeignType, Key>.
#[macro_export]
macro_rules! overload_impl {
    ($overloaded : ident) => {
        #[repr(transparent)]
        pub struct $overloaded<T, P = ()> {
            pub inner: T,
            _p: core::marker::PhantomData<P>,
        }

        // Safety: repr transparent around a struct with a single field will have exactly the same
        // layout and alignment requirements as the wrapped type.
        impl<T, P> $overloaded<T, P> {
            #[inline]
            pub const fn get(inner: &T) -> &Self {
                unsafe { core::mem::transmute(inner) }
            }
            #[inline]
            pub const fn get_mut(inner: &mut T) -> &mut Self {
                unsafe { core::mem::transmute(inner) }
            }
        }

        impl<T, P> core::ops::Deref for $overloaded<T, P> {
            type Target = T;
            fn deref(&self) -> &Self::Target {
                &self.inner
            }
        }

        impl<T, P> core::ops::DerefMut for $overloaded<T, P> {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.inner
            }
        }
    };
}
