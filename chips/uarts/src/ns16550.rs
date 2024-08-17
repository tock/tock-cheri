//! ns16550 compatible UART driver.

use core::cell::Cell;
use core::marker::PhantomData;
use kernel::hil::time::Frequency;
use kernel::hil::uart::{Parameters, Parity, StopBits, Width};
use kernel::utilities::registers::interfaces::{Readable, Writeable};
use kernel::utilities::registers::{register_bitfields, register_structs, Aliased, ReadWrite};
use kernel::utilities::StaticRef;
use kernel::ErrorCode;
use kernel::{debug, hil};

use crate::uart::{UartRegConstruct, UartRegistersIF};

// All ns165550 registers are really 8bit, but an ns16550 has a "register shift" that defines how far
// apart they are. We default to 32-bit registers here, with an option for 8-bit.

// The register_* macros cannot handle a type alias, so factoring out the type is hard to make generic
// It is mostly the fault of repr(X) that they cannot take a type alias.
// We could define two different types, but the generics get ugly because they dont share
// a common trait. Conditional compilation to the rescue...

macro_rules! define_uart_regs {
    {$Ty : tt, $scale : tt} => {
        register_structs! {
            pub UartRegisters {
                ( 0b000 * $scale => pub(crate) brdl: ReadWrite<$Ty>),  // DLL when DLAB=1
                ( 0b001 * $scale => pub(crate) ier: ReadWrite<$Ty, IER::Register>),   // DLH when DLAB=1
                ( 0b010 * $scale => pub(crate) fcr_iir: Aliased<$Ty, IIR::Register, FCR::Register>),
                ( 0b011 * $scale => pub(crate) lcr: ReadWrite<$Ty, LCR::Register>),
                ( 0b100 * $scale => pub(crate) mcr: ReadWrite<$Ty>),
                ( 0b101 * $scale => pub(crate) lsr: ReadWrite<$Ty, LSR::Register>),
                ( 0b110 * $scale => pub(crate) msr: ReadWrite<$Ty>),
                ( 0b111 * $scale => @END),
            }
        }
        register_bitfields![$Ty,
            pub(crate) IER [
                ALL         OFFSET(0) NUMBITS(4) [],
                MODEM       OFFSET(3) NUMBITS(1) [],
                RCV_LINE    OFFSET(2) NUMBITS(1) [],
                TX_EMPTY    OFFSET(1) NUMBITS(1) [],
                RX_RDY      OFFSET(0) NUMBITS(1) [],
            ],
            pub(crate) FCR [
                FIFO_ENABLE OFFSET(0) NUMBITS(1) [],
                CLEAR_RX OFFSET(1) NUMBITS(1) [],
                CLEAR_TX OFFSET(2) NUMBITS(1) [],
                FIFO_REC_TRIG_LVL OFFSET(6) NUMBITS(2) [
                    ONE_BYTE        = 0,
                    FOUR_BYTE       = 1,
                    EIGHT_BYTE      = 2,
                    FOURTEEN_BYTE   = 3,
                ],
            ],
            pub(crate) IIR [
                STATUS OFFSET(0) NUMBITS(1) [
                    NO_INTERRUPT    = 0b1,
                    PENDING         = 0b0,
                ],
                IIR_CODE OFFSET(0) NUMBITS(4) [
                    NO_INTERRUPT    = 0b0001,
                    REC_STATUS      = 0b0110,
                    REC_READY       = 0b0100,
                    TIMEOUT         = 0b1100,
                    TRANS_EMPTY     = 0b0010,
                ],
                FIFOs_ENABLED OFFSET(6) NUMBITS(2) [
                    DISABLED        = 0b00,
                    ENABLED         = 0b11,
                ]
            ],
            pub(crate) LCR [
                WORD_LENGTH OFFSET(0) NUMBITS(2) [
                    FIVE    = 0b00,
                    SIX     = 0b01,
                    SEVEN   = 0b10,
                    EIGHT   = 0b11,
                ],
                STOP_BITS       OFFSET(2) NUMBITS(1) [
                    ONE     = 0b0,
                    TWO     = 0b1,
                ],
                PARITY_ENABLE   OFFSET(3) NUMBITS(1) [],
                EVEN_PARITY     OFFSET(4) NUMBITS(1) [],
                FORCE_PARITY    OFFSET(5) NUMBITS(1) [],
                SET_BREAK       OFFSET(6) NUMBITS(1) [],
                DLAB            OFFSET(7) NUMBITS(1) [],
            ],
            pub(crate) LSR [
                // 1 only if transmitters FIFO is _completely_ empty
                THR_EMPTY   OFFSET(5) NUMBITS(1),
                // 1 only if both transmitters FIFO AND TSR
                TRANS_EMPTY OFFSET(6) NUMBITS(1),
            ]
        ];
    }
}

const FIFO_DEPTH: usize = 16;

#[cfg(feature = "ns16550_u8")]
define_uart_regs!(u8, 1);

#[cfg(not(feature = "ns16550_u8"))]
define_uart_regs!(u32, 4);

pub struct UartRegs<F: Frequency> {
    pub registers: StaticRef<UartRegisters>,
    // If true, then BOTH fifos are operational.
    // The depth of the FIFOs are assumed to be 16 words.
    pub fifos_enabled: Cell<bool>,
    pub(crate) phantom_f: core::marker::PhantomData<F>,
}

impl<F: Frequency> UartRegistersIF for UartRegs<F> {
    fn get_transmit_space(&self) -> usize {
        let block_max = if self.fifos_enabled.get() {
            FIFO_DEPTH
        } else {
            1
        };
        if self.registers.lsr.is_set(LSR::THR_EMPTY) {
            block_max
        } else {
            0
        }
    }

    fn transmit_byte(&self, val: u8) {
        self.registers.brdl.set(val.into())
    }

    fn enable_interrupts(&self) {
        self.registers.ier.write(IER::TX_EMPTY::SET);
    }

    fn disable_interrupts(&self) {
        self.registers.ier.set(0);
    }

    fn interrupt_expected(&self) -> bool {
        // Read what interrupt we got. This also acks the interrupt if it was a THR empty.
        let iir = self.registers.fcr_iir.extract();

        if iir.matches_all(IIR::IIR_CODE::TRANS_EMPTY) {
            true
        } else {
            debug!("Unimplemented UART code {}", iir.read(IIR::IIR_CODE));
            false
        }
    }
}

impl<F: Frequency> hil::uart::Configure for UartRegs<F> {
    fn configure(&self, params: Parameters) -> Result<(), ErrorCode> {
        // This chip does not support these features.
        if params.parity != hil::uart::Parity::None {
            return Err(ErrorCode::NOSUPPORT);
        }
        if params.hw_flow_control != false {
            return Err(ErrorCode::NOSUPPORT);
        }

        // Put this in a known state so we write to the registers we expect
        self.registers.lcr.write(LCR::DLAB::CLEAR);

        // Do not get any spurious interrupts
        self.disable_interrupts();

        // Set divisor reg. This controls the BAUD rate.

        // First set DLAB in LCR. This makes brdl and ier into divisor low and high.
        self.registers.lcr.write(LCR::DLAB::SET);

        // Formula is: dl = (SYSTEM_CLK_FREQ + 8 * BAUD) / (16 * BAUD)
        // e.g.: BAUD 115200 and CLK 25MHz, gives 14: dl = (25 * 1000000 + (8 * 115200)) / (16 * 115200)
        let dl: u16 =
            ((F::frequency() + (8u32 * params.baud_rate)) / (16u32 * params.baud_rate)) as u16;

        self.registers.brdl.set(((dl & 0xFF) as u8).into()); // actually dl low byte
        self.registers.ier.set((((dl >> 8) & 0xFF) as u8).into()); // actually dl high byte

        // Configure params. I've been a bit lazy here, add as needed.
        assert!(
            params.parity == Parity::None
                && params.stop_bits == StopBits::One
                && params.width == Width::Eight
        );

        self.registers.lcr.write(
            LCR::PARITY_ENABLE::CLEAR
                + LCR::STOP_BITS::ONE
                + LCR::WORD_LENGTH::EIGHT
                + LCR::DLAB::CLEAR,
        );

        // Writing to enable also resets the fifos
        self.registers
            .fcr_iir
            .write(FCR::FIFO_REC_TRIG_LVL::EIGHT_BYTE + FCR::FIFO_ENABLE::SET);

        self.registers.mcr.set(0);

        // This might clear some pending interrupts, so why not.
        self.registers.lsr.get();
        self.registers.brdl.get();
        self.registers.fcr_iir.get();
        self.registers.msr.get();

        // Check if the UART supports FIFO operation
        self.fifos_enabled.set(
            self.registers
                .fcr_iir
                .matches_any(&[IIR::FIFOs_ENABLED::ENABLED]),
        );

        self.enable_interrupts();

        Ok(())
    }
}

impl<F: Frequency> const UartRegConstruct for UartRegs<F> {
    type MemoryMapped = UartRegisters;

    fn construct(base: StaticRef<Self::MemoryMapped>) -> Self {
        UartRegs {
            registers: base,
            fifos_enabled: Cell::new(false),
            phantom_f: PhantomData,
        }
    }
}

pub type Uart<'a, F> = crate::uart::Uart<'a, UartRegs<F>>;
pub type UartZero<F, Client> = crate::uart_zero::ZeroUart<UartRegs<F>, Client>;
pub type ZeroUartComponent<F, ClientFactory> =
    crate::uart_zero::ZeroUartComponent<UartRegs<F>, ClientFactory>;
