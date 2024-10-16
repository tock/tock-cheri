//! Data structure for storing compile-time configuration options in the kernel.
//!
//! The rationale for configuration based on a `const` object is twofold.
//!
//! - In theory, Cargo features could be used for boolean-based configuration.
//!   However, these features are generally error-prone for non-trivial use
//!   cases. First, they are globally enabled as long as a dependency
//!   relationship requires a feature (even for other dependency relationships
//!   that do not want the feature). Second, code gated by a non-enabled feature
//!   isn't even type-checked by the compiler, and therefore we can end up with
//!   broken features due to refactoring code (if these features aren't tested
//!   during the refactoring), or to incompatible feature combinations.
//!
//! - Cargo features can only contain bits. On the other hand, a constant value
//!   can contain arbitrary types, which allow configuration based on integers,
//!   strings, or even more complex values.
//!
//! With a typed `const` configuration, all code paths are type-checked by the
//! compiler - even those that end up disabled - which greatly reduces the risks
//! of breaking a feature or combination of features because they are disabled
//! in tests.
//!
//! In the meantime, after type-checking, the compiler can optimize away dead
//! code by folding constants throughout the code, so for example a boolean
//! condition used in an `if` block will in principle have a zero cost on the
//! resulting binary - as if a Cargo feature was used instead. Some simple
//! experiments on generated Tock code have confirmed this zero cost in
//! practice.

/// Data structure holding compile-time configuration options.
///
/// To change the configuration, modify the relevant values in the `CONFIG`
/// constant object defined at the end of this file.
pub(crate) struct Config {
    /// Whether the kernel should trace syscalls to the debug output.
    ///
    /// If enabled, the kernel will print a message in the debug output for each
    /// system call and upcall, with details including the application ID, and
    /// system call or upcall parameters.
    pub(crate) trace_syscalls: bool,

    /// Whether the kernel should show debugging output when loading processes.
    ///
    /// If enabled, the kernel will show from which addresses processes are
    /// loaded in flash and into which SRAM addresses. This can be useful to
    /// debug whether the kernel could successfully load processes, and whether
    /// the allocated SRAM is as expected.
    pub(crate) debug_load_processes: bool,

    /// Whether the kernel should output additional debug information on panics.
    ///
    /// If enabled, the kernel will include implementations of
    /// `Process::print_full_process()` and `Process::print_memory_map()` that
    /// display the process's state in a human-readable form.
    // This config option is intended to allow for smaller kernel builds (in
    // terms of code size) where printing code is removed from the kernel
    // binary. Ideally, the compiler would automatically remove
    // printing/debugging functions if they are never called, but due to
    // limitations in Rust (as of Sep 2021) that does not happen if the
    // functions are part of a trait (see
    // https://github.com/tock/tock/issues/2594).
    //
    // Attempts to separate the printing/debugging code from the Process trait
    // have only been moderately successful (see
    // https://github.com/tock/tock/pull/2826 and
    // https://github.com/tock/tock/pull/2759). Until a more complete solution
    // is identified, using configuration constants is the most effective
    // option.
    pub(crate) debug_panics: bool,

    pub(crate) counted_grant_refs: bool,

    pub(crate) is_cheri: bool,

    pub(crate) contiguous_load_procs: bool,

    pub(crate) static_init: bool,

    /// Whether or not the MMU requires asynchronous configuration
    pub(crate) async_mpu_config: bool,
}

/// A unique instance of `Config` where compile-time configuration options are
/// defined. These options are available in the kernel crate to be used for
/// relevant configuration. Notably, this is the only location in the Tock
/// kernel where we permit `#[cfg(x)]` to be used to configure code based on
/// Cargo features.
pub(crate) const CONFIG: Config = Config {
    trace_syscalls: cfg!(feature = "trace_syscalls"),
    debug_load_processes: cfg!(feature = "debug_load_processes"),
    debug_panics: !cfg!(feature = "no_debug_panics"),
    counted_grant_refs: cfg!(feature = "counted_grant_refs"),
    is_cheri: cfg!(target_feature = "xcheri"),
    static_init: cfg!(feature = "use_static_init"),
    contiguous_load_procs: true,
    async_mpu_config: cfg!(target_feature = "xcheri"),
};

/// Trait allows selecting type based on a const param
pub trait CfgControl<const ENABLED: bool> {
    type Out: ?Sized;
}

impl<T: ?Sized, U: ?Sized> CfgControl<true> for (*const T, *const U) {
    type Out = T;
}
impl<T: ?Sized, U: ?Sized> CfgControl<false> for (*const T, *const U) {
    type Out = U;
}

/// Selects between T and U based on condition
pub type IfElseT<T, U, const CONDITION: bool> =
    <(*const T, *const U) as CfgControl<CONDITION>>::Out;

/// These types are for situations where a feature would change what type is in use. This is better
/// than conditional compilation as a single compilation run can type check all combinations of
/// features.
///
/// Using NOT_COND (not !COND) as const generics still don't like expressions.
///
/// Usage: type MyType = IfElseCfg<TrueType, FalseType, ConditionForTrueType>
///
/// If coming from C and you are used to the pattern of
///
/// struct Foo {
/// #if SOME_FLAG
///   T1 field_t1;
/// #else
///   T2 field_t2;
/// #endif
/// }
///
/// Instead write:
///
/// struct Foo {
///  field : IfElseCfg<T1, T2, SOME_FLAG>,
/// }
///
/// Then, rather than
///
/// Foo myFoo = ...;
/// #if SOME_FLAG
///     bar(&myFoo.field_t1);
/// #else
///     baz(&myFoo.field_t2);
/// #endif
///
/// Do
///
/// let myFoo : Foo = ...;
/// if SOME_FLAG {
///   bar(myFoo.get_true_ref())
/// } else {
///   baz(myFoo.get_false_ref())
/// }
///
/// Or more cleanly:
///
/// let myFoo : Foo = ...;
/// myFoo.mapRef(bar, baz);
///
pub struct IfElseCfg<T, U, const CONDITION: bool>(IfElseT<T, U, CONDITION>)
where
    (*const T, *const U): CfgControl<CONDITION>;

pub type TrueCfg<T, U> = IfElseCfg<T, U, true>;
pub type FalseCfg<T, U> = IfElseCfg<T, U, false>;

impl<T: Clone + ?Sized, U: Clone + ?Sized, const COND: bool> Clone for IfElseCfg<T, U, COND>
where
    (*const T, *const U): CfgControl<COND>,
    IfElseT<T, U, COND>: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Copy, U: Copy, const COND: bool> Copy for IfElseCfg<T, U, COND>
where
    (*const T, *const U): CfgControl<COND>,
    IfElseT<T, U, COND>: Copy,
{
}

impl<T: Default, U: Default> Default for IfElseCfg<T, U, true> {
    fn default() -> Self {
        Self::new_true(Default::default())
    }
}

impl<T: Default, U: Default> Default for IfElseCfg<T, U, false> {
    fn default() -> Self {
        Self::new_false(Default::default())
    }
}

impl<T, U> IfElseCfg<T, U, true> {
    pub const fn new_true(value: T) -> Self {
        Self(value)
    }
    pub const fn new_false(_value: U) -> Self {
        panic!()
    }
    pub fn map_ref<R, FT, FF>(&self, true_f: FT, _false_f: FF) -> R
    where
        FT: FnOnce(&T) -> R,
        FF: FnOnce(&U) -> R,
    {
        true_f(&self.0)
    }
    pub fn map_mut<R, FT, FF>(&mut self, true_f: FT, _false_f: FF) -> R
    where
        FT: FnOnce(&mut T) -> R,
        FF: FnOnce(&mut U) -> R,
    {
        true_f(&mut self.0)
    }
    pub const fn get_true_ref(&self) -> &T {
        &self.0
    }
    pub fn get_true_mut(&mut self) -> &mut T {
        &mut self.0
    }
    pub fn get_false_ref(&self) -> &U {
        panic!()
    }
    pub fn get_false_mut(&mut self) -> &mut U {
        panic!()
    }
    pub fn consume_true(self) -> T {
        self.0
    }
    pub fn consume_false(self) -> U {
        panic!()
    }
}

impl<T, U> IfElseCfg<T, U, false> {
    pub const fn new_true(_value: T) -> Self {
        panic!()
    }
    pub const fn new_false(value: U) -> Self {
        Self(value)
    }
    pub fn map_ref<R, FT, FF>(&self, _true_f: FT, false_f: FF) -> R
    where
        FT: FnOnce(&T) -> R,
        FF: FnOnce(&U) -> R,
    {
        false_f(&self.0)
    }
    pub fn map_mut<R, FT, FF>(&mut self, _true_f: FT, false_f: FF) -> R
    where
        FT: FnOnce(&mut T) -> R,
        FF: FnOnce(&mut U) -> R,
    {
        false_f(&mut self.0)
    }
    pub fn get_true_ref(&self) -> &T {
        panic!()
    }
    pub fn get_true_mut(&mut self) -> &mut T {
        panic!()
    }
    pub const fn get_false_ref(&self) -> &U {
        &self.0
    }
    pub fn get_false_mut(&mut self) -> &mut U {
        &mut self.0
    }
    pub fn consume_true(self) -> T {
        panic!()
    }
    pub fn consume_false(self) -> U {
        self.0
    }
}

/// Correctly uses the IfElseCfg type depending on one of the config options in the global CONFIG
/// struct.
/// If no false type is provided, it will be unit.
///
/// Usage: type MyType = TIfCfg!(FeatureFlag, TrueType [, FalseType]?);
///
/// e.g.:
///
/// type TracingType = TIfCfg!(trace_syscalls, TypeNeedIfTracing);
///
/// Expands to
///
/// type TracingType = IfElseCfg<TypeNeedIfTracing,
///                              (),
///                              {(CONFIG.trace_syscalls) as usize}>
///
/// Usage in conjunction with ! (or never::Never),
///
/// If you want to eliminate a enum variant in certain configurations, do:
///
/// See OnlyInCfg and NotInCfg for shorter forms
///
/// ```text
/// use kernel::TIfCfg;
/// use misc::never::Never;
/// enum E {
///   Var1,
///   Var2(TIfCfg!(debug_panics, (), Never)), // variant only exists with config debug_panics
///   Var3(TIfCfg!(debug_panics, Never, ())), // variant only exists without config debug_panics
/// }
/// ```
///
#[macro_export]
macro_rules! TIfCfg {
    ($feature : ident, $TIf : ty, $TElse : ty) =>
        ($crate::config::IfElseCfg<$TIf, $TElse, {$crate::config::CONFIG. $feature}>);
    ($feature : ident, $T : ty) =>
        ($crate::TIfCfg!($feature, $T, ()));
}

#[macro_export]
macro_rules! OnlyInCfg {
    ($feature : ident, $t : ty) => {
        $crate::TIfCfg!($feature, $t, misc::never::Never)
    };
    ($feature : ident) => {
        $crate::TIfCfg!($feature, (), misc::never::Never)
    };
}

#[macro_export]
macro_rules! NotInCfg {
    ($feature : ident, $t : ty) => {
        $crate::TIfCfg!($feature, misc::never::Never, $t)
    };
    ($feature : ident) => {
        $crate::TIfCfg!($feature, misc::never::Never, ())
    };
}

#[cfg(test)]
mod tests {
    use crate::config::IfElseCfg;
    use core::mem::size_of;
    // For use as, e.g., a counter that we don't need in some situations.
    // A more normal use would be type ConfigU32 = IfElseCfg<u32, (), NEED_COUNTER, !NEED_COUNTER>
    type ConfigU32<const T: bool> = IfElseCfg<u32, (), T>;
    type AsU32 = ConfigU32<true>;
    type AsUnit = ConfigU32<false>;

    #[test]
    fn test_true() {
        // Check size
        assert_eq!(size_of::<AsU32>(), size_of::<u32>());
        // Check use
        let mut val: AsU32 = AsU32::new_true(77);
        *val.get_true_mut() = 66;
        assert_eq!(val.consume_true(), 66);
    }

    #[test]
    fn test_false() {
        // Check size
        assert_eq!(size_of::<AsUnit>(), size_of::<()>());
        // Check use
        let val: AsUnit = AsUnit::new_false(());
        assert_eq!(val.consume_false(), ());
    }

    #[test]
    #[should_panic]
    fn test_wrong_true() {
        let val: AsU32 = AsU32::new_true(77);
        val.get_false_ref();
    }

    #[test]
    #[should_panic]
    fn test_wrong_false() {
        let val: AsUnit = AsUnit::new_false(());
        val.get_true_ref();
    }
}
