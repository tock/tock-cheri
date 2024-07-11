//! Hardware-independent kernel interface for deferred calls
//!
//! This allows any struct in the kernel which implements
//! [DynamicDeferredCallClient](crate::dynamic_deferred_call::DynamicDeferredCallClient)
//! to set and receive deferred calls.
//!
//! These can be used to implement long-running in-kernel algorithms
//! or software devices that are supposed to work like hardware devices.
//! Essentially, this allows the chip to handle more important interrupts,
//! and lets a kernel component return the function call stack up to the scheduler,
//! automatically being called again.
//!
//! Usage
//! -----
//!
//! The `dynamic_deferred_call_clients` array size determines how many
//! [DeferredCallHandle](crate::dynamic_deferred_call::DeferredCallHandle)s
//! may be registered with the instance.
//! When no more slots are available,
//! `dynamic_deferred_call.register(some_client)` will return `None`.
//!
//! ```
//! # use core::cell::Cell;
//! # use kernel::utilities::cells::OptionalCell;
//! # use kernel::static_init;
//! use kernel::dynamic_deferred_call::{
//!     DynamicDeferredCall,
//!     DynamicDeferredCallClient,
//!     DynamicDeferredCallClientState,
//! };
//!
//! let dynamic_deferred_call_clients = unsafe { static_init!(
//!     [DynamicDeferredCallClientState; 2],
//!     Default::default()
//! ) };
//! let dynamic_deferred_call = unsafe { static_init!(
//!     DynamicDeferredCall,
//!     DynamicDeferredCall::new(dynamic_deferred_call_clients)
//! ) };
//! assert!(unsafe { DynamicDeferredCall::set_global_instance(dynamic_deferred_call) } == true);
//!
//! # struct SomeCapsule;
//! # impl SomeCapsule {
//! #     pub fn new(_ddc: &'static DynamicDeferredCall) -> Self { SomeCapsule }
//! #     pub fn set_deferred_call_handle(
//! #         &self,
//! #         _handle: kernel::dynamic_deferred_call::DeferredCallHandle,
//! #     ) { }
//! # }
//! # impl DynamicDeferredCallClient for SomeCapsule {
//! #     fn call(
//! #         &self,
//! #         _handle: kernel::dynamic_deferred_call::DeferredCallHandle,
//! #     ) { }
//! # }
//! #
//! // Here you can register custom capsules, etc.
//! // This could look like:
//! let some_capsule = unsafe { static_init!(
//!     SomeCapsule,
//!     SomeCapsule::new(dynamic_deferred_call)
//! ) };
//! some_capsule.set_deferred_call_handle(
//!     dynamic_deferred_call.register(some_capsule).unwrap() // Unwrap fail = no deferred call slot available
//! );
//! ```

use crate::simple_static_component;
use core::cell::Cell;

use crate::utilities::cells::OptionalCell;
use crate::utilities::singleton_checker::SingletonChecker;

/// Kernel-global dynamic deferred call instance
///
/// This gets called by the kernel scheduler automatically and is accessible
/// through `unsafe` static functions on the `DynamicDeferredCall` struct
static mut DYNAMIC_DEFERRED_CALL: Option<&'static DynamicDeferredCall> = None;

/// Internal per-client state tracking for the [DynamicDeferredCall]
pub struct DynamicDeferredCallClientState {
    scheduled: Cell<bool>,
    client: OptionalCell<&'static dyn DynamicDeferredCallClient>,
}

impl DynamicDeferredCallClientState {
    pub const fn new() -> Self {
        DynamicDeferredCallClientState {
            scheduled: Cell::new(false),
            client: OptionalCell::empty(),
        }
    }
}

impl Default for DynamicDeferredCallClientState {
    fn default() -> DynamicDeferredCallClientState {
        Self::new()
    }
}

/// Dynamic deferred call
///
/// This struct manages and calls dynamically (at runtime) registered
/// deferred calls from capsules and other kernel structures.
///
/// It has a fixed number of possible clients, which
/// is determined by the `clients`-array passed in with the constructor.
pub struct DynamicDeferredCall {
    client_states: &'static [DynamicDeferredCallClientState],
    handle_counter: Cell<usize>,
    call_pending: Cell<bool>,
}

pub struct ProtoDynamicDeferredCallUnsized<T: ?Sized> {
    counter: usize,
    client_states: T,
}

pub type ProtoDynamicDeferredCall =
    ProtoDynamicDeferredCallUnsized<[DynamicDeferredCallClientState]>;
pub type ProtoDynamicDeferredCallSized<const N: usize> =
    ProtoDynamicDeferredCallUnsized<[DynamicDeferredCallClientState; N]>;

impl<const N: usize> ProtoDynamicDeferredCallSized<N> {
    /// Create a prototype for a DynamicDeferredCall. You can register calls with this, and then
    /// complete it later.
    pub const fn new() -> Self {
        const DDCS: DynamicDeferredCallClientState = DynamicDeferredCallClientState::new();
        Self {
            counter: 0,
            client_states: [DDCS; N],
        }
    }

    /// Complete constructing the DynamicDeferredCall.
    /// Once this is done, the completed client_states can be copied to the global.
    pub const fn complete(
        self,
        client_states: &'static [DynamicDeferredCallClientState],
    ) -> (DynamicDeferredCall, [DynamicDeferredCallClientState; N]) {
        (
            DynamicDeferredCall::new_with_counter(client_states, self.counter),
            self.client_states,
        )
    }
}

impl ProtoDynamicDeferredCall {
    pub const fn register(
        &mut self,
        ddc_client: &'static dyn DynamicDeferredCallClient,
    ) -> Option<DeferredCallHandle> {
        let ctr = self.counter;
        if ctr < self.client_states.len() {
            self.client_states[ctr].client = OptionalCell::new(ddc_client);
            self.counter = ctr + 1;
            Some(DeferredCallHandle(ctr))
        } else {
            None
        }
    }
}

/// Dynamic deferred calls with the array inline.
pub struct DynamicCallsWithArray<const SLOTS: usize> {
    calls: DynamicDeferredCall,
    array: [DynamicDeferredCallClientState; SLOTS],
}

impl<const SLOTS: usize> DynamicCallsWithArray<SLOTS> {
    pub const fn get(&self) -> &DynamicDeferredCall {
        &self.calls
    }
}

/// Constructs (and registers) the structure to contain Dynamic Deferred Calls
/// Expects a ProtoDynamicDeferredCall to already have been constructed, and every call to have
/// been registered.
/// Usage:
/// ```ignore
/// #![feature(macro_metavar_expr)]
///  // Inside your kernel::define_components! include this component
///  kernel::define_components!(
///     // ...
///     dyn_def : kernel::dynamic_deferred_call::DynamicDeferredCallComponent::<2>,
///  );
///  // Inside your const-init construct the prototype
///  use kernel::dynamic_deferred_call::ProtoDynamicDeferredCallSized;
///  let mut deferred = ProtoDynamicDeferredCallSized::<2>::new();
///  construct_components!(
///    // (a reference to the deferred calls might be an argument to other constructors)
///    (&mut deferred), // some other component that uses deferred calls
///    // finally, in construct_components!, pass the prototype to the component
///    (deferred) // The dyn_def
///  );
/// ```
pub struct DynamicDeferredCallComponent<const SLOTS: usize> {}

simple_static_component!(impl<{const SLOTS: usize}> for DynamicDeferredCallComponent::<SLOTS>,
    Output = DynamicCallsWithArray::<SLOTS>,
    NewInput = (ProtoDynamicDeferredCallSized::<SLOTS>, &'a mut SingletonChecker),
    FinInput = (),
    | slf, input | {
        crate::assert_single!(input.1);
        let (calls, array) = input.0.complete(&slf.array);
        DynamicCallsWithArray {
            calls,
            array
        }
    },
    | slf, _input | {
        unsafe {
            // Safety: we used the singleton checker to make sure we didn't construct more than one
            DynamicDeferredCall::set_global_instance(&slf.calls);
        }
    }
);

impl DynamicDeferredCall {
    /// Construct a new dynamic deferred call implementation
    ///
    /// This needs to be registered with the `set_global_instance` function immediately
    /// afterwards, and should not be changed anymore. Only the globally registered
    /// instance will receive calls from the kernel scheduler.
    ///
    /// The `clients` array can be initialized using the implementation of [Default]
    /// for the [DynamicDeferredCallClientState].
    pub const fn new(
        client_states: &'static [DynamicDeferredCallClientState],
    ) -> DynamicDeferredCall {
        Self::new_with_counter(client_states, 0)
    }

    const fn new_with_counter(
        client_states: &'static [DynamicDeferredCallClientState],
        counter: usize,
    ) -> DynamicDeferredCall {
        DynamicDeferredCall {
            client_states,
            handle_counter: Cell::new(counter),
            call_pending: Cell::new(false),
        }
    }

    /// Sets a global [DynamicDeferredCall] instance
    ///
    /// This is required before any deferred calls can be retrieved.
    /// It may be called only once. Returns `true` if the global instance
    /// was successfully registered.
    pub unsafe fn set_global_instance(ddc: &'static DynamicDeferredCall) -> bool {
        // If the returned reference is identical to the instance argument,
        // it is set in the option. Otherwise, a different instance is
        // already registered and will not be replaced.
        (*DYNAMIC_DEFERRED_CALL.get_or_insert(ddc)) as *const _ == ddc as *const _
    }

    /// Call the globally registered instance
    ///
    /// Returns `true` if a global instance was registered and has been called.
    pub unsafe fn call_global_instance() -> bool {
        DYNAMIC_DEFERRED_CALL.map(|ddc| ddc.call()).is_some()
    }

    /// Call the globally registered instance while the supplied predicate
    /// returns `true`.
    ///
    /// Returns `true` if a global instance was registered and has been called.
    pub unsafe fn call_global_instance_while<F: Fn() -> bool>(f: F) -> bool {
        DYNAMIC_DEFERRED_CALL
            .map(move |ddc| ddc.call_while(f))
            .is_some()
    }

    /// Check if one or more dynamic deferred calls are pending in the
    /// globally registered instance
    ///
    /// Returns `None` if no global instance has been registered, or `Some(true)`
    /// if the registered instance has one or more pending deferred calls.
    pub unsafe fn global_instance_calls_pending() -> Option<bool> {
        DYNAMIC_DEFERRED_CALL.map(|ddc| ddc.has_pending())
    }

    /// Schedule a deferred call to be called
    ///
    /// The handle addresses the client that will be called.
    ///
    /// If no client for the handle is found (it was unregistered), this
    /// returns `None`. If a call is already scheduled, it returns
    /// `Some(false)`.
    pub fn set(&self, handle: DeferredCallHandle) -> Option<bool> {
        let DeferredCallHandle(client_pos) = handle;
        let client_state = &self.client_states[client_pos];

        if let (call_set, true) = (&client_state.scheduled, client_state.client.is_some()) {
            if call_set.get() {
                // Already set
                Some(false)
            } else {
                call_set.set(true);
                self.call_pending.set(true);
                Some(true)
            }
        } else {
            None
        }
    }

    /// Register a new client
    ///
    /// On success, a `Some(handle)` will be returned. This handle is later
    /// required to schedule a deferred call.
    ///
    /// A given [`DynamicDeferredCallClient`] reference (client) can be
    /// registered multiple times and will receive a different handle each
    /// time. This mechanism is useful to distinguish between deferred calls
    /// scheduled by the same client, but to be handled differently. Each issued
    /// handle will occupy one [`DynamicDeferredCallClientState`] in the
    /// [`DynamicDeferredCall`]. Clients can utilize the passed
    /// [`DeferredCallHandle`] to distinguish between scheduled deferred calls.
    pub fn register(
        &self,
        ddc_client: &'static dyn DynamicDeferredCallClient,
    ) -> Option<DeferredCallHandle> {
        let current_counter = self.handle_counter.get();

        if current_counter < self.client_states.len() {
            let client_state = &self.client_states[current_counter];
            client_state.scheduled.set(false);
            client_state.client.set(ddc_client);

            self.handle_counter.set(current_counter + 1);

            Some(DeferredCallHandle(current_counter))
        } else {
            None
        }
    }

    /// Check if one or more deferred calls are pending
    ///
    /// Returns `true` if one or more deferred calls are pending.
    pub fn has_pending(&self) -> bool {
        self.call_pending.get()
    }

    /// Call all registered and to-be-scheduled deferred calls
    ///
    /// It may be called without holding the `DynamicDeferredCall` reference through
    /// `call_global_instance`.
    pub(self) fn call(&self) {
        self.call_while(|| true)
    }

    /// Call all registered and to-be-scheduled deferred calls while the supplied
    /// predicate returns `true`.
    ///
    /// It may be called without holding the `DynamicDeferredCall` reference through
    /// `call_global_instance_while`.
    pub(self) fn call_while<F: Fn() -> bool>(&self, f: F) {
        if self.call_pending.get() {
            for (i, client_state) in self.client_states.iter().enumerate() {
                if !f() {
                    break;
                }
                if client_state.scheduled.get() {
                    client_state.client.map(|client| {
                        client_state.scheduled.set(false);
                        client.call(DeferredCallHandle(i));
                    });
                }
            }

            // Recompute call_pending here, as some deferred calls may have been skipped due to the
            // `f` predicate becoming false.
            self.call_pending.set(
                self.client_states
                    .iter()
                    .any(|client_state| client_state.scheduled.get()),
            );
        }
    }
}

/// Client for the
/// [DynamicDeferredCall](crate::dynamic_deferred_call::DynamicDeferredCall)
///
/// This trait needs to be implemented for some struct to receive
/// deferred calls from a `DynamicDeferredCall`.
pub trait DynamicDeferredCallClient {
    fn call(&self, handle: DeferredCallHandle);
}

/// Unique identifier for a deferred call registered with a
/// [DynamicDeferredCall](crate::dynamic_deferred_call::DynamicDeferredCall)
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct DeferredCallHandle(usize);
