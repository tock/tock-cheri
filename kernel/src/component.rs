//! Components extend the functionality of the Tock kernel through a
//! simple factory method interface.

/// A component encapsulates peripheral-specific and capsule-specific
/// initialization for the Tock OS kernel in a factory method,
/// which reduces repeated code and simplifies the boot sequence.
///
/// The `Component` trait encapsulates all of the initialization and
/// configuration of a kernel extension inside the `finalize()` function
/// call. The `Output` type defines what type this component generates.
/// Note that instantiating a component does not necessarily
/// instantiate the underlying `Output` type; instead, it is typically
/// instantiated in the `finalize()` method. If instantiating and
/// initializing the `Output` type requires parameters, these should be
/// passed in the component's `new()` function.
pub trait Component {
    /// An optional type to specify the chip or board specific static memory
    /// that a component needs to setup the output object(s). This is the memory
    /// that `static_init!()` would normally setup, but generic components
    /// cannot setup static buffers for types which are chip-dependent, so those
    /// buffers have to be passed in manually, and the `StaticInput` type makes
    /// this possible.
    type StaticInput;

    /// The type (e.g., capsule, peripheral) that this implementation
    /// of Component produces via `finalize()`. This is typically a
    /// static reference (`&'static`).
    type Output;

    /// A factory method that returns an instance of the Output type of this
    /// Component implementation. This factory method may only be called once
    /// per Component instance. Used in the boot sequence to instantiate and
    /// initialize part of the Tock kernel. Some components need to use the
    /// `static_memory` argument to allow the board initialization code to pass
    /// in references to static memory that the component will use to setup the
    /// Output type object.
    unsafe fn finalize(self, static_memory: Self::StaticInput) -> Self::Output;
}

/// Until issue 90091 clears up, here is a split_array_mut that is both const and has both
/// outputs as arrays, not slices
/// N-M must be provided due to lack of const_generic_expr
pub const fn split_array_mut<T, const N: usize, const M: usize, const N_MINUS_M: usize>(
    input: &mut [T; N],
) -> (&mut [T; M], &mut [T; N_MINUS_M]) {
    if (N - M) != N_MINUS_M {
        panic!("Wrong constants")
    }

    let (x, y) = input.split_at_mut(M);
    // SAFETY: M is checked by split_at_mut
    unsafe {
        (
            &mut *(x.as_mut_ptr() as *mut [T; M]),
            &mut *(y.as_mut_ptr() as *mut [T; N_MINUS_M]),
        )
    }
}

// It looks feature(const_precise_live_drops) might fix the issue that made me need this.

/// Similar to Component, StaticComponent encapsulates construction and initialisation of devices
/// and capsules, but it is intended to be used in a way such that it works with const
/// initialization.
///
/// The constructor should allocate both StaticState/StaticStateMut for the component.
/// They can initialize them with the values returned from component_new.
///
/// Then, the StaticComponent can be created using references to the aforementioned state
///
/// During boot, component_finalize should be called.
///
/// See kernel::define_components for a helper macro that does all this automatically.
///
/// See kernel::simple_static_component for a macro to implement this interface for you.
/// See kernel::very_simple_component if you type just has a new() and finalize() without any
/// inheritance / dependant state.
#[const_trait]
pub trait StaticComponent {
    /// The type this factory produces
    type Output: Sized;

    /// Should be statically allocated by constructor with static storage.
    type StaticState: Sized;
    type StaticStateMut: Sized;

    /// A special case where StaticStateMut would contain large buffers of the type [u8; N]
    /// This is kept separate from the rest of StaticStateMut to ensure that the linker can
    /// place it in BSS.
    /// The intent was for this to be an associated constant, but the arithmetic on those makes
    /// the compiler sad. So instead this an associated type of [u8; N].
    /// Nothing is stopping you from setting it to something else, but try to keep it all 0.
    /// CheckedNewZero should perform enough checks such that you can't make a mistake.
    type BufferBytes: ~const CheckedNewZero + Sized;

    /// Should also be provided when calling new
    /// The lifetime parameter here is for state that needs borrowing for component_new.
    /// It should not be a lifetime of the output, which is almost certainly static.
    type NewInput<'a>;

    /// Construct initial state for this component and the state associated with it.
    /// slf is the reference to the static where eventually the result from this will get assigned.
    /// Trying to access any member of slf inside this method will almost certainly cause a cycle
    /// and break compilation.
    /// You can take a reference to them.
    fn component_new<'a>(
        slf: &'static Self::Output,
        state: &'static Self::StaticState,
        state_mut: &'static mut Self::StaticStateMut,
        buffer: &'static mut Self::BufferBytes,
        input: Self::NewInput<'a>,
    ) -> (Self::Output, Self::StaticState, Self::StaticStateMut);
}

/// Rust does not like calling const associated methods directly, here is a helper to call the
/// associated method on a StaticComponent.
pub const fn call_component_new<'a, T: ~const StaticComponent + ?Sized>(
    slf: &'static T::Output,
    state: &'static T::StaticState,
    state_mut: &'static mut T::StaticStateMut,
    buffer: &'static mut T::BufferBytes,
    input: T::NewInput<'a>,
) -> (T::Output, T::StaticState, T::StaticStateMut) {
    T::component_new(slf, state, state_mut, buffer, input)
}

/// Everything that implements StaticComponent should probably also implement this.
/// There is no actual requirement, but the helper macros will break if you don't.
/// We keep it as separate trait as it is not const.
pub trait StaticComponentFinalize: ~const StaticComponent {
    type FinaliseInput;
    fn component_finalize(
        _slf: &'static Self::Output,
        _state: &'static Self::StaticState,
        _input: Self::FinaliseInput,
    ) {
    }
}

/// A version of NewZero that will also check the result.
#[const_trait]
pub trait CheckedNewZero: ~const NewZero + Sized {
    const SZ: usize = core::mem::size_of::<Self>();

    fn new_zero_checked() -> Self {
        let result = Self::new_zero();

        let as_bytes = core::ptr::addr_of!(result) as *const u8;
        let as_bytes = unsafe { core::slice::from_raw_parts(as_bytes, Self::SZ) };

        let mut i = 0;

        while i != Self::SZ {
            if as_bytes[i] != 0 {
                panic!("Result non-zero");
            }
            i += 1;
        }

        result
    }
}
impl<T: ~const NewZero> const CheckedNewZero for T {}

pub const fn call_new_zero_checked<T: ~const CheckedNewZero>() -> T {
    T::new_zero_checked()
}

/// Constructor that returns all zeros.
/// It is not unsafe to return non-zeros, just bad for performance.
#[const_trait]
pub trait NewZero {
    fn new_zero() -> Self;
}

/// Implement NewZero for arrays of u8s:
impl<const N: usize> const NewZero for [u8; N] {
    fn new_zero() -> Self {
        [0u8; N]
    }
}

/// And for unit
impl const NewZero for () {
    fn new_zero() -> Self {
        ()
    }
}

/// And tuples (recursively), up to 8 elements. Feel free to bump the number if need be.
macro_rules! implement_new_zero {
    ($($t : ident)*) => {
        impl<$($t : ~const NewZero,)*> const NewZero for ($($t,)*) {
            fn new_zero() -> Self {
                ($($t::new_zero(),)*)
            }
        }
    };
}
macro_rules! implement_new_zero_rec {
    ($t : ident) => (implement_new_zero!($t););
    ($t : ident $($ts : ident)*) => (
        implement_new_zero!($t $($ts)*);
        implement_new_zero_rec!($($ts)*);
    )
}
implement_new_zero_rec!(A B C D E F G H);

#[macro_export]
macro_rules! define_components_no_helpers {
    (
        structs $components : ident, $non_mut: ident, $mut : ident {
            $($id : ident : $t : path,)*
        }
    ) => {
        pub struct $components {
            $(pub $id : <$t as $crate::component::StaticComponent>::Output),*
        }
        pub struct $non_mut {
            $(pub $id : <$t as $crate::component::StaticComponent>::StaticState),*
        }
        pub struct $mut {
            $(pub $id : <$t as $crate::component::StaticComponent>::StaticStateMut),*
        }
    }
}

/// A helper macro to declare, init, and finalize components for your board.
/// Will declare three structs for you, all of which should have static storage.
/// Only the last type should have mutable reference taken to it. You should take care not to
/// take more than one.
/// Calling this will define two other macros you can call in your init and finalize logic.
///
/// Usage:
/// ```ignore
/// // Define three types (in a scope your board logic can see)
/// kernel::define_components!(structs Components, CState, CStateMut {
///     component1 : Type1,
///     component2 : Type2,
/// });
///
/// // Construct an instance of each (use this within your const initializer). args will be extra
/// // arguments to construct each of the componants and depends on their type.
/// kernel::construct_components!(let componants, state, state_mut =
///                                   ref_to_components, ref_to_state, ref_to_mut_state, {
///    (args1),
///    (args2),
/// });
///
/// // And finally finalise (probably inside main)
/// kernel::finalize_components!(ref_to_components, ref_to_state {
///     (extra_args),
///     (extra_args),
/// });
/// ```
///
/// NOTE: you will likely need `const_precise_live_drops` to call this macro.
#[macro_export]
macro_rules! define_components {
    (
        structs $components : ident, $non_mut: ident, $mut : ident {
            $($id : ident : $t : path,)*
        }
    ) => {
        $crate::define_components_no_helpers!(structs $components, $non_mut, $mut {
            $($id : $t,)*
        });

        struct componant_buffers
        {
            $(pub $id : <$t as $crate::component::StaticComponent>::BufferBytes),*
        }
        use $crate::component::CheckedNewZero;
        static mut COMPONANT_BUFFER : componant_buffers = componant_buffers {
            $($id : $crate::component::call_new_zero_checked::<<$t as $crate::component::StaticComponent>::BufferBytes>()),*
        };

        /// A helper macro to init the structs described by define_components.
        /// See define_components.
        #[macro_export]
        macro_rules! construct_components {
            ($$($$t:tt)*) => (
                $crate :: construct_components_helper!(
                    {$components, $non_mut, $mut {$($id : $t,)*}},
                $$($$t)*)
            )
        }

        /// A helper macro finalize the structs described by define_components.
        /// See define_components.
        #[macro_export]
        macro_rules! finalize_components {
            ($$($$t:tt)*) => (
                $crate :: finalize_components_helper!(
                    {$components, $non_mut, $mut {$($id : $t,)*}},
                $$($$t)*)
            )
        }
    }
}

/// A version of `define_components` that also creates a single component that can be used to
/// construct this set of components.
/// Usage is the same as define_components (see that) preceded by a `component = IDENT,`
/// `IDENT` will be a new component that will define everything in this set.

#[macro_export]
macro_rules! define_components_as_component {
    (
        component = $fac : ident, structs $components : ident, $non_mut: ident, $mut : ident {
            $($id : ident : $t : path,)*
        }
    ) => {
        // First define the components
        $crate::define_components_no_helpers!(structs $components, $non_mut, $mut { $($id : $t,)* });
        // Then declare the factory
        pub struct $fac();
        // Then implement component
        impl const $crate::component::StaticComponent for $fac {
            type Output = $components;
            type StaticState = $non_mut;
            type StaticStateMut = $mut;
            type BufferBytes = ($(<$t as $crate::component::StaticComponent>::BufferBytes,)*);
            type NewInput<'a> = ($(<$t as $crate::component::StaticComponent>::NewInput<'a>,)*);

            fn component_new<'a>(slf: &'static Self::Output, state: &'static Self::StaticState, state_mut: &'static mut Self::StaticStateMut, buffer: &'static mut Self::BufferBytes, input: Self::NewInput<'a>) ->
                   (Self::Output, Self::StaticState, Self::StaticStateMut) {
                $(
                    let $id = $crate::component::call_component_new::<$t>(&slf.$id, &state.$id, &mut state_mut.$id, &mut buffer.${index()}, input.${index()});
                )*

                let components = $components {
                        $($id : $id.0,)*
                };
                let component_state = $non_mut {
                        $($id : $id.1,)*
                };
                let component_state_mut = $mut {
                        $($id : $id.2,)*
                };
                (
                    components,
                    component_state,
                    component_state_mut
                )
            }
        }
        // And finalize
        impl $crate::component::StaticComponentFinalize for $fac {
            type FinaliseInput = ($(<$t as $crate::component::StaticComponentFinalize>::FinaliseInput,)*);

            fn component_finalize(slf: &'static Self::Output, state: &'static Self::StaticState, input: Self::FinaliseInput) {
                // Just finalize every member
                $(<$t as $crate::component::StaticComponentFinalize>::component_finalize(&slf.$id, &state.$id, input.${index()});)*
            }
        }
    }
}

/// Helper for construct_components. Call that, not this.
#[macro_export]
macro_rules! construct_components_helper {
    ({$components_t : ident, $non_mut_t: ident, $mut_t : ident {$($id : ident : $t : path,)*}},
        let $components : ident, $component_state : ident, $component_state_mut : ident = $c_r : expr, $s_r : expr, $m_r : expr, {
        $($arg : expr,)*
    }) => {
        let cbuffer = unsafe {&mut COMPONANT_BUFFER};
        // First call methods one-by-one, assigning the triples to a variable with a name
        // we can use again
        $(
            let $id = $crate::component::call_component_new::<$t>(&$c_r.$id, &$s_r.$id, &mut$m_r.$id, &mut cbuffer.$id, $arg);
        )*
        // Then split out each of the threes into groups

        let $components = $components_t {
                $($id : $id.0,)*
        };
        let $component_state = $non_mut_t {
                $($id : $id.1,)*
        };
        let $component_state_mut = $mut_t {
                $($id : $id.2,)*
        };
    }
}

/// Helper for construct_components. Call that, not this,
#[macro_export]
macro_rules! finalize_components_helper {
    ({$components_t : ident, $non_mut_t: ident, $mut_t : ident {$($id : ident : $t : path,)*}},
        $c_r : expr, $s_r : expr, {
        $($arg : expr,)*
    }) => {
        {
            $(<$t as $crate::component::StaticComponentFinalize>::component_finalize(&$c_r.$id, &$s_r.$id, $arg);)*
        }
    }
}

/// const construct a number of grants.
/// Usage:
/// ```ignore
/// use kernel::construct_grants;
/// construct_grants!(kernel_ref, proto_kern, counter, mem_alloc_cap, {
///     grant1 : NUM1,
///     grant2 : NUM2,
///     ...
/// });
/// ```
#[macro_export]
macro_rules! construct_grants {
    ($kernel : expr, $proto : expr, $counter : ident, $cap : expr, {
        $($id : ident : $p : expr,)*
    }) => {
        $(let ($id, $counter) = $proto.create_grant($kernel, $p, $counter, $cap);)*
    }
}

/// A StaticComponent factory for ()
pub struct NoComponent;
impl const StaticComponent for NoComponent {
    type Output = ();
    type StaticState = ();
    type StaticStateMut = ();
    type BufferBytes = ();
    type NewInput<'a> = ();

    fn component_new<'a>(
        _slf: &'static Self::Output,
        _state: &'static Self::StaticState,
        _state_mut: &'static mut Self::StaticStateMut,
        _buffer: &'static mut Self::BufferBytes,
        _input: Self::NewInput<'a>,
    ) -> (Self::Output, Self::StaticState, Self::StaticStateMut) {
        ((), (), ())
    }
}
impl StaticComponentFinalize for NoComponent {
    type FinaliseInput = ();
}

/// The StaticComponent trait is quite verbose as it is meant to handle lots of cases.
/// This macro implements the interface.
/// Usage:
/// ```ignore
/// use kernel::simple_static_component;
/// simple_static_component!(
///     // Implement for a factory type
///     impl for MyFactory,
///     // Can inherit from another factory (by reference to the parent)
///     // call the constructor / finalize with the super{} block
///     // the static reference to this parent is accessible via the supr argument.
///     (Inherit = ...)?,
///     // Or inherit by value from other factories (by composition).
///     // These will be constructed automatically (theirs inputs will just prepended to the inputs
///     // this component specifies)
///     // Finalize will also just be called automatically, again just prepended arguments together.
///     // x, y, z etc should be the field names from within your struct.
///     // the actual contained state will be accessed as self.x(.member)?.
///     // X, Y, Z etc should be _factories_ for those fields.
///     // The constructed values will be available in the scope of your closure with the same names.
///     (Contain = (x : X, y : Y, z : Z...) (member)? )?,
///     // The type that will result
///     Output = ...,
///     // How many (mutable) u8's are owned by this output type
///     (BUFFER_BYTES = ...)?,
///     // Other inputs to constructor (runs at compile time)
///     NewInput = ...,
///     // Other inputs to finalize (runs during init)
///     FinInput = ...,
///     // The function for construction. super{...} passes arguments to the inherited type
///     // slf is a reference to where this result will eventually be placed. You can do pointer
///     // arithmetic on it, but cannot read/write via it as the object as not exist at this point.
///     // supr is the 'slf' argument for the super type.
///     // the x, y, x fields will also be available in this scope.
///     | slf, input (,buf)? (,supr)? | (super{...})? {...},
///     // The function for construction. super{...} passes arguments to the inherited type's
///     // finalize
///     | slf, input (,supr)? | (super{...})? {...}
/// )
/// ```
///
/// If NewInput lifetime argument is needed, use 'a.
#[macro_export]
macro_rules! simple_static_component {
    // If no Inherit is defined, add in NoComponent as the parent.
    (impl $(<{$($ts:tt)*}>)? for $t : ty $(where {$($wheres: tt)*})?,
        $(Contain = ($($field : ident $(.$member:ident)? : $factory : path),*),)?
        Output = $ot : ty,
        $(BUFFER_BYTES = $bb : expr,)?
        NewInput = $it : ty,
        FinInput = $ift : ty,
        |$slf : ident, $input : ident $(,$b : ident)? | {$($new:tt)*},
        |$slf2 : ident, $input2 : ident | { $($finalize:tt)* }
    ) => {
        $crate::simple_static_component!(
        impl $(<{$($ts)*}>)? for $t $(where {$($wheres)*})?,
            Inherit = $crate::component::NoComponent,
            $(Contain = ($($field $(.$member)? : $factory),*),)?
            Output = $ot,
            $(BUFFER_BYTES = $bb,)?
            NewInput = $it,
            FinInput = $ift,
            |$slf, $input $(,$b)?, _sup | super{()} {$($new)*},
            |$slf2, $input2, _sup | super{()} {$($finalize)*});
    };
    // If buffer bytes is not specified, add in 0 as the amount
    (impl $(<{$($ts:tt)*}>)? for $t : ty $(where {$($wheres :tt)*})?,
        Inherit = $inherit : ty,
        $(Contain = ($($field : ident $(.$member:ident)? : $factory : path),*),)?
        Output = $ot : ty,
        NewInput = $it : ty,
        FinInput = $ift : ty,
        |$slf : ident, $input : ident, $sup : ident | super {$($super : tt)*} {$($new:tt)*},
        |$slf2 : ident, $input2 : ident, $sup2 : ident | super {$($super2 : tt)*} {$($finalize:tt)*}
    ) => {
        $crate::simple_static_component!(
        impl $(<{$($ts)*}>)? for $t $(where {$($wheres)*})?,
            Inherit = $inherit,
            $(Contain = ($($field $(.$member)? : $factory),*),)?
            Output = $ot,
            BUFFER_BYTES = 0,
            NewInput = $it,
            FinInput = $ift,
            |$slf, $input, _buffer, $sup | super {$($super)*} {$($new)*},
            |$slf2, $input2, $sup2 | super {$($super2)*} {$($finalize)*}
        );
    };
    // Main case.
    (impl $(<{$($ts:tt)*}>)? for $t : ty $(where {$($wheres: tt)*})?,
        Inherit = $inherit : ty,
        $(Contain = ($($field : ident $(.$member:ident)? : $factory : path),*),)?
        Output = $ot : ty,
        BUFFER_BYTES = $bb : expr,
        NewInput = $it : ty,
        FinInput = $ift : ty,
        |$slf : ident, $input : ident, $b : ident, $sup : ident | super {$($super : tt)*} {$($new:tt)*},
        |$slf2 : ident, $input2 : ident, $sup2 : ident | super {$($super2 : tt)*} {$($finalize:tt)*}
    ) => {
        impl $(<$($ts)*>)? const $crate::component::StaticComponent for $t where
            //$inherit : ~const $crate::component::StaticComponent,
            //$inherit : $crate::component::StaticComponentFinalize,
            $($($factory : ~const $crate::component::StaticComponent, )*)?
            $($($factory : $crate::component::StaticComponentFinalize, )*)?
            $( $($wheres)*)?
        {
            type Output = $ot;
            type StaticState = (
                <$inherit as $crate::component::StaticComponent>::Output, // output from inherit
                <$inherit as $crate::component::StaticComponent>::StaticState, // its state recursively
                $(
                    // recursive state from contained things
                    ($(<$factory as $crate::component::StaticComponent>::StaticState,)*)
                )?
            );
            type StaticStateMut = (
                // TODO: might want a way to set this via the macro
                (),
                //
                <$inherit as $crate::component::StaticComponent>::StaticStateMut,
                // recursive state from contained things
                $(
                    ($(<$factory as $crate::component::StaticComponent>::StaticStateMut,)*)
                )?
            );
            // If we have any contained things, we just inherit their inputs
            #[allow(unused_parens)]
            type NewInput<'a> = (
                $($(<$factory as $crate::component::StaticComponent>::NewInput<'a>,)*)? // and those for things it contains
                $it // this things inputs
            );

            type BufferBytes = (
                [u8; $bb], // our bytes
                <$inherit as $crate::component::StaticComponent>::BufferBytes, // for inherited
                $(
                    ($(<$factory as $crate::component::StaticComponent>::BufferBytes,)*)
                )?
            );

            fn component_new<'a>($slf: &'static Self::Output, state: &'static Self::StaticState, state_mut: &'static mut Self::StaticStateMut, $b: &'static mut Self::BufferBytes, $input: Self::NewInput<'a>) -> (Self::Output, Self::StaticState, Self::StaticStateMut) {
                let inherit_new = <$inherit as $crate::component::StaticComponent>::component_new(&state.0, &state.1, &mut state_mut.1, &mut $b.1, $($super)*);
                let $sup = &state.0;
                // Also do a similar thing to construct everything this thing will contain
                $(
                    let sub_state_ref = &state.2;
                    let sub_mut_ref = &mut state_mut.2;
                    let sub_buf = &mut $b.2;
                    $(
                        let $field = <$factory as $crate::component::StaticComponent>::component_new(&$slf.$field$(.$member)?,
                           &sub_state_ref.${index()}, &mut sub_mut_ref.${index()}, &mut sub_buf.${index()}, $input.${index()});
                        let last_input = $input.${length()};
                    )*
                    let $input = last_input;
                    // currently, $field is a triple of (slf, state, state_mut).
                    // we need to put together the state / state_mut into one tuple
                    let sub_state = ($($field.1 ,)*);
                    let sub_mut = ($($field.2 ,)*);
                    // And then shadow field to just be slf
                    $(
                      let $field = $field.0;
                    )*
                )?
                let $b = &mut $b.0;

                (
                    {$($new)*},
                    (inherit_new.0, inherit_new.1
                        $(, sub_state ${ignore(field)})?
                    ),
                    ((), inherit_new.2 $(, sub_mut ${ignore(field)})?)
                )
            }
        }
        impl $(<$($ts)*>)? $crate::component::StaticComponentFinalize for $t where
            //$inherit : ~const $crate::component::StaticComponent,
            //$inherit : $crate::component::StaticComponentFinalize,
            $($($factory : ~const $crate::component::StaticComponent, )*)?
            $($($factory : $crate::component::StaticComponentFinalize, )*)?
            $( $($wheres)*)?
        {
            #[allow(unused_parens)]
            type FinaliseInput = (
                $($(<$factory as $crate::component::StaticComponentFinalize>::FinaliseInput,)*)? // and those for things it contains
                $ift
            );

            fn component_finalize($slf2: &'static Self::Output, state: &'static Self::StaticState, $input2: Self::FinaliseInput) {
                // First finalize parent
                <$inherit as $crate::component::StaticComponentFinalize>::component_finalize(&state.0, &state.1, $($super2)*);
                let $sup2 = &state.0;
                // Call finalize on all contained components
                $(
                    let sub_state = &state.2;
                    $(
                        <$factory as $crate::component::StaticComponentFinalize>::component_finalize(
                            &$slf2.$field$(.$member)?, &sub_state.${index()}, $input2.${index()});
                        let last_input = $input2.${length()};
                    )*
                    let $input2 = last_input;
                )?

                {
                    $($finalize)*
                }
            }
        }
    };
}

/// Another even less verbose helper for static components.
///
/// For components which just have a new(...) and (maybe) a fin(&self, ...) where all
/// input arguments just need propagation to the respective method (in order with no extras).
///
/// Usage:
/// ```ignore
/// kernel::very_simple_component!( impl(<{X,Y, Z}>)? Type, new_method(...) (, fin_method(...))?);
/// // examples
/// kernel::very_simple_component!(impl for Foo, new());
/// kernel::very_simple_component!(impl for Bar, new(), fin());
/// kernel::very_simple_component!(impl<{T, V}> for Foo<T,V>, new());
/// kernel::very_simple_component!(impl for Bax, new(u8, &'a mut usize), fin(u8,u8));
/// ```
/// If your new method needs a lifetime argument, use 'a
#[macro_export]
macro_rules! very_simple_component {
    (impl $(<{$($impl:tt)*}>)? for $t : path $(where {$($wheres: tt)*})?, $new : ident ($($new_arg : ty),*) $(, $fin : ident ($($fin_arg : ty),*))? ) => {
        $crate::simple_static_component!(impl $(<{$($impl)*}>)? for $t $(where {$($wheres)*})?,
            Output = Self,
            NewInput = ($($new_arg),*),
            FinInput = ($($($fin_arg),*)?),
            |_slf, _input| {
                $crate::very_simple_component!(@call_helper {Self::$new}, _input, $($new_arg)*)
            },
            |_slf, _input| {
                $(let _ = $crate::very_simple_component!(@call_helper {_slf.$fin}, _input, $($fin_arg)*);)?
            }
        );
    };
    // One argument is passed directly
    (@call_helper {$($f : tt)*}, $v : ident, $t : ty) => {
        $($f)*($v)
    };
    // Other numbers are broken out of a tuple
    (@call_helper {$($f : tt)*}, $v : ident, $($t : ty)*) => {
        $($f)*($(${ignore(t)} $v.${index()},)*)
    }
}
