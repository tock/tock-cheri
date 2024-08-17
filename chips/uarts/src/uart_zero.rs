//! General zero-copy UART driver.

use core::marker::PhantomData;
use kernel::collections::resettable_iterator::{IntoResettableIterator, ResettableIterator};
use kernel::collections::safe_buf::{GetByte, IntoResettableByteReadIterator};
use kernel::component::StaticComponentFinalize;
use kernel::hil;
use kernel::hil::uart::{ZeroTransmit, ZeroTransmitClient};
use kernel::utilities::cells::OptionalCell;
use kernel::utilities::StaticRef;
use kernel::{simple_static_component, ErrorCode};

pub struct ZeroUart<R: UartRegistersIF + ~const UartRegConstruct, Client: ZeroTransmitClient>
where
    Client::Buf: IntoResettableByteReadIterator,
{
    client: Client,
    regs: R,
    // The currently transmitting data
    in_progress: OptionalCell<<Client::Buf as IntoResettableIterator>::ResetIterType>,
}

impl<R: UartRegistersIF + ~const UartRegConstruct, Client: ZeroTransmitClient> ZeroUart<R, Client>
where
    Client::Buf: IntoResettableByteReadIterator,
{
    pub const fn new(client: Client, base: StaticRef<R::MemoryMapped>) -> Self {
        Self {
            client,
            regs: R::construct(base),
            in_progress: OptionalCell::empty(),
        }
    }

    // Returns whether the operation completed
    fn transmit<Item: GetByte, Iter: Iterator<Item = Item>>(
        &self,
        iter: &mut Iter,
        allow_block: bool,
    ) -> bool {
        // We might be calling this shortly after a previous transmission.
        let mut space = 0;

        loop {
            while space == 0 {
                space = self.regs.get_transmit_space();
                if space == 0 && !allow_block {
                    return false;
                }
            }
            for b in &mut *iter {
                // Write the byte from the array to the tx register.
                let b = b.get_byte();
                self.regs.transmit_byte(b.into());
                space -= 1;
                if space == 0 {
                    break;
                }
            }
            if space != 0 {
                break;
            }
        }

        return true;
    }

    pub fn handle_interrupt(&self) {
        if self.regs.interrupt_expected() {
            // If there is a transmit in progress, continue it
            if let Some(mut iter) = self.in_progress.take() {
                if self.transmit(&mut iter.iter(), false) {
                    // If finished, pass back to callback
                    Client::transmit_finish(self, iter.reset(), Ok(()));
                } else {
                    // Otherwise save progress
                    self.in_progress.set(iter)
                }
            }
        }
    }

    pub fn transmit_sync(&self, bytes: &[u8]) {
        // Fill the TX buffer and spin if it is full
        self.transmit(&mut bytes.into_iter(), true);
    }
}

impl<R: UartRegistersIF + ~const UartRegConstruct, Client: ZeroTransmitClient> hil::uart::Configure
    for ZeroUart<R, Client>
where
    Client::Buf: IntoResettableByteReadIterator,
{
    fn configure(&self, params: hil::uart::Parameters) -> Result<(), ErrorCode> {
        self.regs.configure(params)
    }
}

impl<R: UartRegistersIF + ~const UartRegConstruct, Client: ZeroTransmitClient> ZeroTransmit<Client>
    for ZeroUart<R, Client>
where
    Client::Buf: IntoResettableByteReadIterator,
{
    fn transmit(&self, buf: Client::Buf) -> Result<Option<Client::Buf>, (Client::Buf, ErrorCode)> {
        if self.in_progress.is_some() {
            return Err((buf, ErrorCode::BUSY));
        }

        let mut iter = buf.into_resettable_iterator();

        if self.transmit(&mut iter.iter(), false) {
            Ok(Some(iter.reset()))
        } else {
            self.in_progress.set(iter);
            Ok(None)
        }
    }

    fn get_client(&self) -> &Client {
        &self.client
    }
}

pub struct ZeroUartComponent<
    R: UartRegistersIF + ~const UartRegConstruct,
    ClientFactory: StaticComponentFinalize,
> where
    ClientFactory::Output: ZeroTransmitClient,
    <ClientFactory::Output as ZeroTransmitClient>::Buf: IntoResettableByteReadIterator,
{
    _phantom: PhantomData<(R, ClientFactory)>,
}

use crate::uart::{UartRegConstruct, UartRegistersIF};
use kernel::hil::uart::Configure;

simple_static_component!(impl<{R : UartRegistersIF + ~const UartRegConstruct, ClientFactory : StaticComponentFinalize}> for
    ZeroUartComponent::<R, ClientFactory> where
        {ClientFactory::Output : ZeroTransmitClient,
        <ClientFactory::Output as ZeroTransmitClient>::Buf : IntoResettableByteReadIterator},
    Contain = (client : ClientFactory),
    Output = ZeroUart<R, ClientFactory::Output>,
    NewInput = StaticRef<R::MemoryMapped>,
    FinInput = hil::uart::Parameters,
    |slf, input| {
        ZeroUart::new(client, input)
    },
    |slf, input | {
        let _ = slf.configure(input);
    }
);
