//! Virtualize a UART bus with the new interface.
//! Can handle a (statically) variable number of ZeroTransmitClients
//! Clients will have to agree on a type they can all convert their buffer into/from.
//! The mux will take care of calling into() on both paths.
//! At worst, this will be an enum over all their buffer types.
//! The policy implements an in order queue.

use core::cell::Cell;
use kernel::collections::list::{ListLink, ListNode};

/// A node in the queue (monomorphic with respect to client)
struct PerClientStateNode<Buf: 'static> {
    /// Buffer this client has queued
    queue: Cell<Option<Buf>>,
    /// Link to next in queue (if any)
    link: ListLink<'static, PerClientStateNode<Buf>>,
    /// The value to set in_progress to when popping this from the queue
    /// Although this is known statically in most cases, having it here
    /// helps for the de-queue case where we don't care about the the
    /// type of the client.
    ndx: u8,
}

impl<Buf> ListNode<'static, PerClientStateNode<Buf>> for PerClientStateNode<Buf> {
    fn next(&self) -> &ListLink<'static, PerClientStateNode<Buf>> {
        &self.link
    }
}

// A node in the queue plus the client state (different type per client)
struct PerClientState<Client, Buf: 'static> {
    // Client state
    client: Client,
    // Node for list
    node: PerClientStateNode<Buf>,
}

macro_rules! DeclareMux {
    ($mux_name : ident, $(($name : ident, $ids : ident, $overload : ident, $n : tt)),+) => {

use core::marker::PhantomData;
use kernel::hil::uart::{ZeroTransmitClient, ZeroTransmit};
use kernel::ErrorCode;
use core::cell::Cell;
use kernel::collections::list::{Queue, ListLink};
use crate::virtualizers::virtual_uart_zero::PerClientStateNode;
use crate::virtualizers::virtual_uart_zero::PerClientState;

pub struct $mux_name<Buf : 'static, $($ids : ZeroTransmitClient + 'static),+>
{
    $($name : PerClientState<$ids, Buf>,)+
    // The in progress transmission
    in_progress : Cell<u8>,
    // A queue (through the parts of the client state that are the same)
    queue : Queue<'static, PerClientStateNode<Buf>>,
    // Ugly hack:
    // If something can think of a way around this I am open to suggestion. The problem is this:
    // In order to support modifying the intrusive list though this mux, we need a reference
    // with a lifetime that lives as long as the struct itself (in this case static).
    // The "transmit" method in the uart hil gives a possibly shorter reference.
    // I don't want to modify the transmit hil to require a lifetime that is a parameter to the
    // type as this would be ugly as well.
    // We need some way to get to a handle with a longer lifetime again. The safe way of doing this
    // is to have this weird self reference.
    static_self : &'static Self,
}

// Create a set of types that act as transmitters for each client.
macro_rules! DeclareMuxRefHelper {
    ($$one_id : ident, $$one_n : tt, $$one_name: ident, $$one_overload : ident) => {

        misc::overload_impl!($$one_overload);

        impl<Buf : 'static, $($ids : ZeroTransmitClient + 'static,)+ Transmitter : ZeroTransmit<$mux_name<Buf, $($ids),+>>> ZeroTransmit<$$one_id> for
            $$one_overload<Transmitter,(Buf, $($ids,)*)>
            where $($ids::Buf : Into<Buf>, Buf : Into<$ids::Buf>),+
        {
            #[inline]
            fn transmit(&self, buf: $$one_id::Buf) -> Result<Option<$$one_id::Buf>, ($$one_id::Buf, ErrorCode)> {
                let transmit = &self.inner;
                let all_state = transmit.get_client();
                let buf = buf.into();
                let state = &all_state.$$one_name;
                if all_state.in_progress.get() == 0 {
                    // Nothing in progress, do now
                    match transmit.transmit(buf) {
                        Ok(None) => {
                            all_state.in_progress.set($$one_n); // in progress
                            Ok(None)
                        },
                        Ok(Some(buf)) => Ok(Some(buf.into())), // short-circuit
                        Err((buf, er)) => Err((buf.into(), er)) // error
                    }
                } else {
                    // Have to queue:
                    match state.node.queue.replace(Some(buf)) {
                        None => {
                            all_state.queue.push_head(&all_state.static_self.$$one_name.node);
                            Ok(None)
                        }
                        Some(buf) => { Err((buf.into(), ErrorCode::BUSY))}
                    }
                }
            }
            #[inline]
            fn get_client(&self) -> &$$one_id {
                &self.inner.get_client().$$one_name.client
            }
        }

        /// Get a client reference given the reference to the total transmitter
        pub const fn $$one_name<Buf : 'static, $($ids : ZeroTransmitClient + 'static,)+ Transmitter : ZeroTransmit<$mux_name<Buf, $($ids),+>>>
            (t : &Transmitter) -> &$$one_overload::<Transmitter,(Buf, $($ids,)*)>
                    where $($ids::Buf : Into<Buf>, Buf : Into<$ids::Buf>),+ {
            $$one_overload::<Transmitter,(Buf, $($ids,)*)>::get(t)
        }
    }
}

$(
    DeclareMuxRefHelper!($ids, $n, $name, $overload);
)*



// The Mux is also a client
impl<Buf : 'static, $($ids : ZeroTransmitClient + 'static),+> ZeroTransmitClient for $mux_name<Buf, $($ids),+>
  where $($ids::Buf : Into<Buf>, Buf : Into<$ids::Buf>),+ {
    type Buf = Buf;

    fn transmit_finish<Transmit: ZeroTransmit<Self>>(transmitter: &Transmit,
                                                     mut buf: Self::Buf,
                                                     mut res: Result<(), ErrorCode>) {
        // transmit_finish is only called from our uart's callback path, never internally to
        // this module, so there should be no capsules on the stack.
        // We can therefore handle as many items in the queue as possible now.
        // This is in contrast to the other virtual_uart, where the corresponding function
        // was at risk at being called from the transmit path.
        // On our transmit path, we have a completely separate call to transmit.transmit() that
        // will never call this function.

        let slf = transmitter.get_client();
        let mut just_finished = slf.in_progress.take(); // take clears in progress
        loop {
            // Call client callback
            match just_finished {
                $(
                    $n => $ids::transmit_finish($name(transmitter), buf.into(), res),
                )+
                 _ => { debug_assert!(false)}
            }

            // It is possible that a capsule jumped in and took the in_progress slot. I don't
            // really mind, but if ever we get starvation this is why.
            if slf.in_progress.get() != 0 {
                return;
            }

            // Try pop something off the queue
            if let Some(next) = slf.queue.pop_head() {
                if let Some(next_buf) = next.queue.take() {
                    just_finished = next.ndx;
                    (buf, res) = match transmitter.transmit(next_buf) {
                        Ok(None) => {
                            slf.in_progress.set(just_finished);
                            return;  // in progress, just return and we will get a callback
                        },
                        Ok(Some(buf)) => {(buf, Ok(()))}, // short circuit
                        Err((buf, er)) => {(buf, Err(er))} // error
                    };
                    // Go around the loop and call the next client callback
                } else {
                    debug_assert!(false);
                    return;
                }
            } else {
                return;
            }
        }

    }
}

misc::overload_impl!(MuxDeferredCall);

// Declare a constructor for the virtual uart (only really for the component to use)
impl<Buf : 'static, $($ids : ZeroTransmitClient + 'static),+> $mux_name<Buf, $($ids),+>
  where $($ids::Buf : Into<Buf>, Buf : Into<$ids::Buf>),+ {

    pub const fn new($($name : $ids,)* static_self : &'static Self) -> Self {
        Self {
            $($name : PerClientState {
                client : $name,
                node : PerClientStateNode {
                    queue : Cell::new(None),
                    link : ListLink::empty(),
                    ndx : $n,
                },
            },)*
            in_progress : Cell::new(0),
            queue : Queue::new(),
            static_self,
        }
    }
}

/// Constructs a uart mux component. Should be parameterised by a buffer type that can be
/// converted to/from each clients buffer type, and component factories for each client.
pub struct UartMuxComponent<Buf : 'static, $($ids),+>(
    PhantomData::<(Buf, $($ids),+)>
);

kernel::simple_static_component!(impl<{Buf : 'static, $($ids),+}> for UartMuxComponent::<Buf, $($ids),+>
    where {
            $(
               $ids::Output : ZeroTransmitClient + 'static,
               <$ids::Output as ZeroTransmitClient>::Buf : Into<Buf>,
                Buf: Into<<$ids::Output as ZeroTransmitClient>::Buf>,
            )+
    },
    Contain = ($($name.client : $ids),+),
    Output = $mux_name<Buf, $($ids::Output),+>,
    NewInput = (),
    FinInput = (),
    |slf, _input | {
        $mux_name::new($($name,)+ slf)
    },
    |_slf, _input| {}
);

};}

pub mod mux2 {
    DeclareMux!(UartMux, (a, A, ARef, 1), (b, B, BRef, 2));
}
pub mod mux3 {
    DeclareMux!(UartMux, (a, A, ARef, 1), (b, B, BRef, 2), (c, C, CRef, 3));
}
pub mod mux4 {
    DeclareMux!(
        UartMux,
        (a, A, ARef, 1),
        (b, B, BRef, 2),
        (c, C, CRef, 3),
        (d, D, DRef, 4)
    );
}
