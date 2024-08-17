// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Provides low-level debugging functionality to userspace. The system call
//! interface is documented in doc/syscalls/00008_low_level_debug.md.

mod fmt;

use core::cell::Cell;
use core::ops::Deref;

use kernel::grant::{AllowRoCount, AllowRwCount, Grant, UpcallCount};
use kernel::hil::uart::{Transmit, TransmitClient, ZeroTransmit, ZeroTransmitClient};
use kernel::process::Error;
use kernel::syscall::{CommandReturn, SyscallDriver};
use kernel::utilities::leased_buffer::LeasedBufferCell;
use kernel::{ErrorCode, ProcessId};

// LowLevelDebug requires a &mut [u8] buffer of length at least BUF_LEN.
pub use fmt::BUF_LEN;

pub type GrantType = Grant<AppData, UpcallCount<0>, AllowRoCount<0>, AllowRwCount<0>>;

pub const DRIVER_NUM: usize = crate::driver::NUM::LowLevelDebug as usize;

// Length of the debug queue for each app. Each queue entry takes 3 words (tag
// and 2 usizes to print). The queue will be allocated in an app's grant region
// when that app first uses the debug driver.
const QUEUE_SIZE: usize = 4;

// -----------------------------------------------------------------------------
// Implementation details below
// -----------------------------------------------------------------------------

#[derive(Default)]
pub struct AppData {
    queue: [Option<DebugEntry>; QUEUE_SIZE],
}

#[derive(Clone, Copy)]
pub(crate) enum DebugEntry {
    Dropped(usize),       // Some debug messages were dropped
    AlertCode(usize),     // Display a predefined alert code
    Print1(usize),        // Print a single number
    Print2(usize, usize), // Print two numbers
}

struct BaseLowLevelDebug {
    buffer: Cell<Option<&'static mut [u8]>>,
    grant: GrantType,
    // grant_failed is set to true when LowLevelDebug fails to allocate an app's
    // grant region. When it has a chance, LowLevelDebug will print a message
    // indicating a grant initialization has failed, then set this back to
    // false. Although LowLevelDebug cannot print an application ID without
    // using grant storage, it will at least output an error indicating some
    // application's message was dropped.
    grant_failed: Cell<bool>,
}

impl BaseLowLevelDebug {
    pub const fn new(buffer: &'static mut [u8], grant: GrantType) -> Self {
        Self {
            buffer: Cell::new(Some(buffer)),
            grant,
            grant_failed: Cell::new(false),
        }
    }
}

pub struct LowLevelDebug<'u, U: Transmit<'u>> {
    base: BaseLowLevelDebug,
    uart: &'u U,
}

impl<'u, U: Transmit<'u>> LowLevelDebug<'u, U> {
    pub const fn new(
        buffer: &'static mut [u8],
        uart: &'u U,
        grant: GrantType,
    ) -> LowLevelDebug<'u, U> {
        LowLevelDebug {
            base: BaseLowLevelDebug::new(buffer, grant),
            uart,
        }
    }
}

// Trait shared by both implementations that has most of the logic.

trait LLDB {
    fn transmit_str(&self, tx_buffer: &'static mut [u8], len: usize);
    fn get_base(&self) -> &BaseLowLevelDebug;
    fn do_command(
        &self,
        minor_num: usize,
        r2: usize,
        r3: usize,
        caller_id: ProcessId,
    ) -> CommandReturn {
        match minor_num {
            0 => return CommandReturn::success(),
            1 => self.push_entry(DebugEntry::AlertCode(r2), caller_id),
            2 => self.push_entry(DebugEntry::Print1(r2), caller_id),
            3 => self.push_entry(DebugEntry::Print2(r2, r3), caller_id),
            _ => return CommandReturn::failure(ErrorCode::NOSUPPORT),
        }
        CommandReturn::success()
    }

    fn transmit_finish(&self, tx_buffer: &'static mut [u8]) {
        // Identify and transmit the next queued entry. If there are no queued
        // entries remaining, store buffer.

        let base = self.get_base();

        // Prioritize printing the "grant init failed" message over per-app
        // debug entries.

        if base.grant_failed.take() {
            const MESSAGE: &[u8] = b"LowLevelDebug: grant init failed\n";
            tx_buffer[..MESSAGE.len()].copy_from_slice(MESSAGE);

            self.transmit_str(tx_buffer, MESSAGE.len());

            return;
        }

        for process_grant in base.grant.iter() {
            let processid = process_grant.processid();
            let (app_num, first_entry) = process_grant.enter(|owned_app_data, _| {
                owned_app_data.queue.rotate_left(1);
                (processid.id(), owned_app_data.queue[QUEUE_SIZE - 1].take())
            });
            let to_print = match first_entry {
                None => continue,
                Some(to_print) => to_print,
            };

            let msg_len = fmt::format_entry(app_num, to_print, tx_buffer);

            self.transmit_str(tx_buffer, msg_len);

            return;
        }

        base.buffer.set(Some(tx_buffer));
    }

    // If the UART is not busy (the buffer is available), transmits the entry.
    // Otherwise, adds it to the app's queue.
    fn push_entry(&self, entry: DebugEntry, processid: ProcessId) {
        let base = self.get_base();

        if let Some(buffer) = base.buffer.take() {
            let msg_len = fmt::format_entry(processid.id(), entry, buffer);
            self.transmit_str(buffer, msg_len);
            return;
        }

        use DebugEntry::Dropped;

        let result = base.grant.enter(processid, |borrow, _| {
            for queue_entry in &mut borrow.queue {
                if queue_entry.is_none() {
                    *queue_entry = Some(entry);
                    return;
                }
            }
            // The queue is full, so indicate some entries were dropped. If
            // there is not a drop entry, replace the last entry with a drop
            // counter. A new drop counter is initialized to two, as the
            // overwrite drops an entry plus we're dropping this entry.
            borrow.queue[QUEUE_SIZE - 1] = match borrow.queue[QUEUE_SIZE - 1] {
                Some(Dropped(count)) => Some(Dropped(count + 1)),
                _ => Some(Dropped(2)),
            };
        });

        // If we were unable to enter the grant region, schedule a diagnostic
        // message. This gives the user a chance of figuring out what happened
        // when LowLevelDebug fails.
        if result.is_err() {
            base.grant_failed.set(true);
        }
    }
}

impl<'u, U: Transmit<'u>> LLDB for LowLevelDebug<'u, U> {
    fn transmit_str(&self, tx_buffer: &'static mut [u8], len: usize) {
        let _ = self
            .uart
            .transmit_buffer(tx_buffer, len)
            .map_err(|(_, returned_buffer)| {
                self.base.buffer.set(Some(returned_buffer));
            });
    }
    fn get_base(&self) -> &BaseLowLevelDebug {
        &self.base
    }
}

impl<'u, U: Transmit<'u>> kernel::syscall::SyscallDriver for LowLevelDebug<'u, U> {
    fn command(
        &self,
        minor_num: usize,
        r2: usize,
        r3: usize,
        caller_id: ProcessId,
    ) -> CommandReturn {
        self.do_command(minor_num, r2, r3, caller_id)
    }

    fn allocate_grant(&self, processid: ProcessId) -> Result<(), kernel::process::Error> {
        self.base.grant.enter(processid, |_, _| {})
    }
}

impl<'u, U: Transmit<'u>> TransmitClient for LowLevelDebug<'u, U> {
    fn transmitted_buffer(
        &self,
        tx_buffer: &'static mut [u8],
        _tx_len: usize,
        _rval: Result<(), ErrorCode>,
    ) {
        self.transmit_finish(tx_buffer)
    }
}

// The zero-copy version
pub struct LowLevelDebugZero {
    base: BaseLowLevelDebug,
    leased: LeasedBufferCell<'static, u8>,
}

impl LowLevelDebugZero {
    // Immediately prints the provided string to the UART
    fn transmit_buf<Transmit: ZeroTransmit<Self>>(
        transmit: &Transmit,
        buffer: &'static mut [u8],
        msg_len: usize,
    ) {
        let slf = transmit.get_client();
        let lease = slf.leased.set_lease(buffer, 0..msg_len);
        match transmit.transmit(lease) {
            Ok(Some(buf)) => {
                // Short circuit
                Self::transmit_finish(transmit, buf, Ok(()))
            }
            Err((b, _)) => {
                // There is nothing we can do on error apart from restore the buffer
                slf.leased.take_buf(b);
            }
            _ => {
                // waiting for callback
            }
        }
    }

    pub const fn new(buffer: &'static mut [u8], grant: GrantType) -> Self {
        Self {
            base: BaseLowLevelDebug::new(buffer, grant),
            leased: LeasedBufferCell::new(),
        }
    }

    pub const fn get_syscall_driver<Transmitter: ZeroTransmit<Self>>(
        t: &Transmitter,
    ) -> &LLDBSyscallDriver<Transmitter> {
        LLDBSyscallDriver::get(t)
    }
}

misc::overload_impl!(LLDBSyscallDriver);

impl ZeroTransmitClient for LowLevelDebugZero {
    type Buf = &'static mut [u8];

    fn transmit_finish<Transmit: ZeroTransmit<Self>>(
        transmitter: &Transmit,
        buf: Self::Buf,
        _res: Result<(), ErrorCode>,
    ) {
        let slf = transmitter.get_client();
        LLDBSyscallDriver::<Transmit>::transmit_finish(
            LLDBSyscallDriver::<Transmit>::get(transmitter),
            slf.leased.take_buf(buf),
        );
    }
}

impl<Transmitter: ZeroTransmit<LowLevelDebugZero>> LLDB for LLDBSyscallDriver<Transmitter> {
    fn transmit_str(&self, tx_buffer: &'static mut [u8], len: usize) {
        LowLevelDebugZero::transmit_buf(self.deref(), tx_buffer, len)
    }

    fn get_base(&self) -> &BaseLowLevelDebug {
        &self.get_client().base
    }
}

impl<Transmitter: ZeroTransmit<LowLevelDebugZero>> SyscallDriver
    for LLDBSyscallDriver<Transmitter>
{
    fn command(
        &self,
        command_num: usize,
        r2: usize,
        r3: usize,
        process_id: ProcessId,
    ) -> CommandReturn {
        self.do_command(command_num, r2, r3, process_id)
    }

    fn allocate_grant(&self, process_id: ProcessId) -> Result<(), Error> {
        self.get_client().base.grant.enter(process_id, |_, _| {})
    }
}
