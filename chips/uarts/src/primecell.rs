//! ARM PrimeCell compatible uart
//! This is mostly incomplete as it was intended to test QEMU, which never
//! blocks.

use crate::uart::{UartRegConstruct, UartRegistersIF};
use kernel::hil::time::Frequency;
use kernel::hil::uart::Parameters;
use kernel::utilities::registers::ReadWrite;
use kernel::utilities::StaticRef;
use kernel::{hil, ErrorCode};
use tock_registers::interfaces::Writeable;
use tock_registers::register_structs;

const FIFO_DEPTH: usize = 8;

register_structs! {
    pub UartRegisters {
        ( 0x00 => pub(crate) dr: ReadWrite<u32>),
        ( 0x04 => pub(crate) rsr_ecr: ReadWrite<u32>),
        ( 0x08 => pub(crate) lcr_h : ReadWrite<u32>),
        ( 0x0C => pub(crate) lcr_m : ReadWrite<u32>),
        ( 0x10 => pub(crate) lcr_l : ReadWrite<u32>),
        ( 0x14 => pub(crate) cr : ReadWrite<u32>),
        ( 0x18 => pub(crate) fr : ReadWrite<u32>),
        ( 0x1c => pub(crate) iir_icr : ReadWrite<u32>),
        ( 0x20 => pub(crate) lpr : ReadWrite<u32>),
        ( 0x24 => @END),
    }

}

pub struct UartRegs<F: Frequency> {
    pub registers: StaticRef<UartRegisters>,
    pub(crate) phantom_f: core::marker::PhantomData<F>,
}

impl<F: Frequency> UartRegistersIF for UartRegs<F> {
    fn get_transmit_space(&self) -> usize {
        FIFO_DEPTH
    }

    fn transmit_byte(&self, val: u8) {
        self.registers.dr.set(val.into())
    }

    fn enable_interrupts(&self) {}

    fn disable_interrupts(&self) {}

    fn interrupt_expected(&self) -> bool {
        true
    }
}

impl<F: Frequency> hil::uart::Configure for UartRegs<F> {
    fn configure(&self, _params: Parameters) -> Result<(), ErrorCode> {
        // Note: this was just for a qemu test, so I have not bothered.
        Ok(())
    }
}

impl<F: Frequency> const UartRegConstruct for UartRegs<F> {
    type MemoryMapped = UartRegisters;

    fn construct(base: StaticRef<Self::MemoryMapped>) -> Self {
        UartRegs {
            registers: base,
            phantom_f: core::marker::PhantomData,
        }
    }
}

pub type Uart<'a, F> = crate::uart::Uart<'a, UartRegs<F>>;
pub type UartZero<F, Client> = crate::uart_zero::ZeroUart<UartRegs<F>, Client>;
pub type ZeroUartComponent<F, ClientFactory> =
    crate::uart_zero::ZeroUartComponent<UartRegs<F>, ClientFactory>;
