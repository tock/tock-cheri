//! Generic uart implementation

use core::cell::Cell;
use kernel::hil::uart::Configure;
use kernel::utilities::cells::{OptionalCell, TakeCell};
use kernel::utilities::StaticRef;
use kernel::{hil, ErrorCode};

/// A low level trait that uarts in this crate can provide
pub trait UartRegistersIF: Configure {
    /// Either how many words can be written, or 0 if unknown
    fn get_transmit_space(&self) -> usize;
    /// Transmit a byte
    fn transmit_byte(&self, val: u8);
    /// Enable all needed interrupts
    fn enable_interrupts(&self);
    /// Disable all interrupts
    fn disable_interrupts(&self);
    /// Was the interrupt an expected one
    fn interrupt_expected(&self) -> bool;
}

#[const_trait]
pub trait UartRegConstruct {
    type MemoryMapped;
    fn construct(base: StaticRef<Self::MemoryMapped>) -> Self;
}

pub struct Uart<'a, R: UartRegistersIF + UartRegConstruct> {
    regs: R,
    tx_client: OptionalCell<&'a dyn hil::uart::TransmitClient>,
    rx_client: OptionalCell<&'a dyn hil::uart::ReceiveClient>,
    buffer: TakeCell<'static, [u8]>,
    len: Cell<usize>,
    index: Cell<usize>,
}

impl<'a, R: UartRegistersIF + UartRegConstruct> Uart<'a, R> {
    pub fn new(base: StaticRef<R::MemoryMapped>) -> Self {
        Uart {
            regs: R::construct(base),
            tx_client: OptionalCell::empty(),
            rx_client: OptionalCell::empty(),
            buffer: TakeCell::empty(),
            len: Cell::new(0),
            index: Cell::new(0),
        }
    }

    fn transmit(&self, tx_data: &[u8], start: usize, end: usize, allow_block: bool) -> usize {
        // Always 0. We might be calling this shortly after a previous transmission.
        let mut space = 0;

        // Fill the TX buffer until it reports full.
        for i in start..end {
            while space == 0 {
                space = self.regs.get_transmit_space();
                if space == 0 && !allow_block {
                    return i;
                }
            }

            // Write the byte from the array to the tx register.
            self.regs.transmit_byte(tx_data[i].into());
            space -= 1;
        }
        end
    }

    fn transmit_stored(&self, allow_block: bool, allow_callback: bool) {
        // Try transmit anything left
        if self.len.get() != self.index.get() {
            self.buffer.map(|tx_data| {
                self.index.set(self.transmit(
                    tx_data,
                    self.index.get(),
                    self.len.get(),
                    allow_block,
                ))
            });
        }
        // And if we are done, call back
        if self.len.get() == self.index.get() {
            // Signal client write done only if this came from an interrupt
            // Could use a deferred call here (would allow us to disable interrupts)
            if allow_callback {
                self.tx_client.map(|client| {
                    self.buffer.take().map(|buffer| {
                        client.transmitted_buffer(buffer, self.len.get(), Ok(()));
                    });
                });
            }
        }
    }

    pub fn handle_interrupt(&self) {
        if self.regs.interrupt_expected() {
            // Now handle the interrupt
            self.transmit_stored(false, true);
        }
    }

    pub fn transmit_sync(&self, bytes: &[u8]) {
        // Fill the TX buffer and spin if it is full
        self.transmit(bytes, 0, bytes.len(), true);
    }
}

impl<R: UartRegistersIF + UartRegConstruct> hil::uart::Configure for Uart<'_, R> {
    fn configure(&self, params: hil::uart::Parameters) -> Result<(), ErrorCode> {
        self.regs.configure(params)
    }
}

impl<'a, R: UartRegistersIF + UartRegConstruct> hil::uart::Transmit<'a> for Uart<'a, R> {
    fn set_transmit_client(&self, client: &'a dyn hil::uart::TransmitClient) {
        self.tx_client.set(client);
    }

    fn transmit_buffer(
        &self,
        tx_data: &'static mut [u8],
        tx_len: usize,
    ) -> Result<(), (ErrorCode, &'static mut [u8])> {
        if tx_len == 0 {
            return Err((ErrorCode::SIZE, tx_data));
        }

        // Save the buffer so we can keep sending it.
        self.buffer.replace(tx_data);
        self.len.set(tx_len);
        self.index.set(0);

        self.transmit_stored(false, false);

        Ok(())
    }

    fn transmit_abort(&self) -> Result<(), ErrorCode> {
        Err(ErrorCode::FAIL)
    }

    fn transmit_word(&self, _word: u32) -> Result<(), ErrorCode> {
        Err(ErrorCode::FAIL)
    }
}

impl<'a, R: UartRegistersIF + UartRegConstruct> hil::uart::Receive<'a> for Uart<'a, R> {
    fn set_receive_client(&self, client: &'a dyn hil::uart::ReceiveClient) {
        self.rx_client.set(client);
    }

    fn receive_buffer(
        &self,
        rx_buffer: &'static mut [u8],
        _rx_len: usize,
    ) -> Result<(), (ErrorCode, &'static mut [u8])> {
        Err((ErrorCode::FAIL, rx_buffer))
    }

    fn receive_abort(&self) -> Result<(), ErrorCode> {
        Err(ErrorCode::FAIL)
    }

    fn receive_word(&self) -> Result<(), ErrorCode> {
        Err(ErrorCode::FAIL)
    }
}
