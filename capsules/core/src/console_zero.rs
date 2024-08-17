use core::cell::Cell;
use kernel::collections::list::{GenListNode, ListLinkGen, PRefListLink, PRefQueue};
use kernel::grant::{ARefNoClone, AllowRoCount, AllowRwCount, Grant, LivePRef, PRef, UpcallCount};
use kernel::hil::uart::{ZeroTransmit, ZeroTransmitClient};
use kernel::processbuffer::ReadableProcessSlice;
use kernel::syscall::{CommandReturn, SyscallDriver};
use kernel::upcall::PUpcall;
use kernel::{very_simple_component, ErrorCode, ProcessId};

/// Syscall driver number.
use crate::driver;
pub const DRIVER_NUM: usize = driver::NUM::Console as usize;

/// Ids for read-only allow buffers
mod ro_allow {
    pub const WRITE: usize = 1;
    /// The number of allow buffers the kernel stores for this grant
    pub const COUNT: u8 = 2;
}

/// Ids for read-write allow buffers
mod rw_allow {
    /// The number of allow buffers the kernel stores for this grant
    pub const COUNT: u8 = 2;
}

// Prefer NoClone as it transmutes more freely with owned buffers from other clients that
// might be muxed with this one.
pub type Buffer = ARefNoClone<ReadableProcessSlice>;

#[derive(Default)]
pub struct App {
    // Link for queue
    link: PRefListLink<App>,
    // Callback
    transmit_callback: Cell<PUpcall>,
    // Data
    transmit_data: Cell<Buffer>,
}

// TODO the intrusive linked list above needs to remove the link when dropped.
// this requires finishing the app closing mechanism, which should
// (a) call a pre-drop method on each grant to let the owner know it is being dropped
// (b) call drop on the type

impl GenListNode<App, PRef<App>> for App {
    fn next(&self) -> &ListLinkGen<App, PRef<App>> {
        &self.link
    }
}

type ConsoleGrant = Grant<
    App,
    UpcallCount<3>,
    AllowRoCount<{ ro_allow::COUNT }>,
    AllowRwCount<{ rw_allow::COUNT }>,
>;

pub struct Console {
    apps: ConsoleGrant,
    transmit_queue: PRefQueue<App>,
}

impl ZeroTransmitClient for Console {
    type Buf = Buffer;

    fn transmit_finish<Transmit: ZeroTransmit<Self>>(
        transmitter: &Transmit,
        buf: Self::Buf,
        res: Result<(), ErrorCode>,
    ) {
        Console::finish_put(transmitter, buf, res)
    }
}

impl Console {
    pub const fn new(grant: ConsoleGrant) -> Self {
        Console {
            apps: grant,
            transmit_queue: PRefQueue::<App>::new(),
        }
    }

    fn buf_len(buf: Buffer) -> usize {
        buf.with_live(|x| match x {
            None => 0,
            Some(buf) => buf.len(),
        })
    }

    fn finish_put<Transmit: ZeroTransmit<Self>>(
        transmitter: &Transmit,
        buf: Buffer,
        result: Result<(), ErrorCode>,
    ) {
        let slf = transmitter.get_client();
        // Callback on head of list
        if let Some(head) = slf.transmit_queue.pop_head() {
            if let Some(live) = head.try_into_live() {
                let result = match result {
                    Ok(_) => Self::buf_len(buf),
                    Err(_) => kernel::errorcode::into_statuscode(result),
                };
                // Should we really ignore this? What is meant to happen on this kind of
                // pushback? Kernel error?
                let _ = live.transmit_callback.get().schedule(result, 0, 0);
            }
        }
        // Peek to see if there is another
        if let Some(head) = slf.transmit_queue.peek_head() {
            if let Some(live) = head.try_into_live() {
                Self::start_print(transmitter, live)
            }
        }
    }

    fn start_print<Transmit: ZeroTransmit<Self>>(transmitter: &Transmit, app: LivePRef<App>) {
        let data = app.transmit_data.take();
        match transmitter.transmit(data) {
            Ok(Some(data)) => {
                // Call finish ourselves
                Self::finish_put(transmitter, data, Ok(()))
            }
            Ok(None) => {
                // Nothing to do, handled on callback
            }
            Err((buf, er)) => Self::finish_put(transmitter, buf, Err(er)),
        }
    }

    fn do_command<Transmit: ZeroTransmit<Self>>(
        transmitter: &Transmit,
        cmd_num: usize,
        arg1: usize,
        _: usize,
        appid: ProcessId,
    ) -> Result<CommandReturn, ErrorCode> {
        let slf = transmitter.get_client();
        let process_grant = slf.apps.get_for(appid)?;
        let grant_data = process_grant.get_grant_data();
        let kern_data = process_grant.get_kern_data();
        let app_data = grant_data.get_pref().ok_or(ErrorCode::BUSY)?;
        match cmd_num {
            0 => {}
            1 => {
                // putstr
                if app_data.link.is_some() {
                    // Already in queue
                    return Err(ErrorCode::BUSY);
                }

                let buf = kern_data.get_readonly_aref(ro_allow::WRITE)?;

                if arg1 != buf.len() {
                    return Err(ErrorCode::SIZE);
                }

                // Store previous allows
                app_data.transmit_callback.set(kern_data.get_upcall(1));
                app_data.transmit_data.set(buf.as_noclone().into());
                // Then enqueue
                let some = slf.transmit_queue.is_some();
                slf.transmit_queue.push_tail(app_data.into());
                if !some {
                    // Handle now as nothing else was in the queue
                    Self::start_print(transmitter, app_data);
                }
            }
            2 => {
                // getnstr
                return Err(ErrorCode::NOSUPPORT);
            }
            3 => {
                // Abort RX
                return Err(ErrorCode::NOSUPPORT);
            }
            _ => return Err(ErrorCode::NOSUPPORT),
        }
        Ok(CommandReturn::success())
    }

    pub const fn get_syscall_driver<Transmitter: ZeroTransmit<Self>>(
        t: &Transmitter,
    ) -> &ConsoleSyscallDriver<Transmitter> {
        ConsoleSyscallDriver::get(t)
    }
}

misc::overload_impl!(ConsoleSyscallDriver);

impl<Transmitter: ZeroTransmit<Console>> SyscallDriver for ConsoleSyscallDriver<Transmitter> {
    /// Setup shared buffers.
    ///
    /// ### `allow_num`
    ///
    /// - `1`: Writeable buffer for read buffer

    /// Setup shared buffers.
    ///
    /// ### `allow_num`
    ///
    /// - `1`: Readonly buffer for write buffer

    // Setup callbacks.
    //
    // ### `subscribe_num`
    //
    // - `1`: Write buffer completed callback
    // - `2`: Read buffer completed callback

    /// Initiate serial transfers
    ///
    /// ### `command_num`
    ///
    /// - `0`: Driver check.
    /// - `1`: Transmits a buffer passed via `allow`, up to the length
    ///        passed in `arg1`
    /// - `2`: Receives into a buffer passed via `allow`, up to the length
    ///        passed in `arg1`
    /// - `3`: Cancel any in progress receives and return (via callback)
    ///        what has been received so far.
    fn command(&self, cmd_num: usize, arg1: usize, arg2: usize, appid: ProcessId) -> CommandReturn {
        match Console::do_command(&self.inner, cmd_num, arg1, arg2, appid) {
            Ok(command) => command,
            Err(er) => CommandReturn::failure(er),
        }
    }

    fn allocate_grant(&self, processid: ProcessId) -> Result<(), kernel::process::Error> {
        self.inner.get_client().apps.enter(processid, |_, _| {})
    }
}

very_simple_component!(impl for Console,
    new(ConsoleGrant)
);
