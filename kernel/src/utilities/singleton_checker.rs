//! Compile time enforcement of singleton pattern

use core::any::TypeId;

/// This type keeps track of constructors / initializers that are only intended
/// to be called once during const initialisation.
/// Its implementation is really inefficient, do not use at runtime.
/// The advantage of this checker is that it should operate at compile time,
/// allowing runtime singletons without keeping track of which have already
/// been constructed. Simply construct them with a const-expr and assign to
/// a static.
/// This type itself should also be a singleton. However, because we cannot
/// mutate statics at compile time there is no way to check this.
/// Therefore, the constructor for this is unsafe, but should allow all other
/// constructors to be safe.
pub struct SingletonCheckerBase<T: ?Sized> {
    used: T,
}

pub type SingletonChecker = SingletonCheckerBase<[Option<TypeId>]>;
pub type SingletonCheckerSized<const SLOTS: usize> = SingletonCheckerBase<[Option<TypeId>; SLOTS]>;

impl<const SLOTS: usize> SingletonCheckerSized<SLOTS> {
    pub const fn as_unsized(&mut self) -> &mut SingletonChecker {
        self
    }
}

impl SingletonChecker {
    pub const fn id_eq(id1: TypeId, id2: TypeId) -> bool {
        // Const comparison has not yet been stabilised.
        // Instead we currently peek inside the type to see what integer is in
        // use.
        // This will need updating if the type changes / the official method
        // is made const.
        unsafe {
            core::mem::transmute::<TypeId, u64>(id1) == core::mem::transmute::<TypeId, u64>(id2)
        }
    }

    /// Check an ID is not used. You should probably be using assert_single.
    pub const fn check_single<T>(&mut self, id: TypeId) {
        let len = self.used.len();
        let mut ndx = 0;
        while ndx < len {
            match self.used[ndx] {
                Some(other_id) => {
                    if Self::id_eq(id, other_id) {
                        panic!("Not a singleton");
                    }
                }
                None => {
                    self.used[ndx] = Some(id);
                    return;
                }
            }
            ndx += 1;
        }
        panic!("Too few slots. Increase SLOTS in new");
    }

    /// Construct a new checker. This should be called once, GLOBALLY. Not once
    /// per const initializer. Collect as much global state as you can into a
    /// single struct, and use this within the initializer for that.
    pub const unsafe fn new_sized<const SLOTS: usize>() -> SingletonCheckerSized<SLOTS> {
        const NONE: Option<TypeId> = None;
        SingletonCheckerSized::<SLOTS> {
            used: [NONE; SLOTS],
        }
    }
}

/// Helper to assert that this place in code is reached only once
///
/// Usage:
/// ```
/// use kernel::utilities::singleton_checker::SingletonChecker;
/// let mut checker = unsafe {
///     SingletonChecker::new_sized::<100>() // Size any number larger than uses of assert_single!
/// };
/// let checker = checker.as_unsized();
/// // ...
/// kernel::assert_single!(checker)
/// ```
///
/// Note that, if you have multiple constructors of your type, you either need to call a helper
/// that has this macro.
#[macro_export]
macro_rules! assert_single {
    ($checker : expr) => {{
        struct S();
        $checker.check_single::<S>(core::any::TypeId::of::<S>());
    }};
}
