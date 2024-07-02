//! Component for DebugWriter, the implementation for `debug!()`.
//!
//! This provides components for attaching the kernel debug output (for panic!,
//! print!, debug!, etc.) to the output. `DebugWriterComponent` uses a UART mux,
//! and `DebugWriterNoMuxComponent` just uses a UART interface directly.
//!
//! Usage
//! -----
//! ```rust
//! DebugWriterComponent::new(uart_mux).finalize(());
//!
//! components::debug_writer::DebugWriterNoMuxComponent::new(
//!     &nrf52::uart::UARTE0,
//! )
//! .finalize(());
//! ```

// Author: Brad Campbell <bradjc@virginia.edu>
// Last modified: 11/07/2019

use capsules::virtual_uart::{MuxUart, UartDevice};
use kernel::capabilities;
use kernel::collections::ring_buffer::RingBuffer;
use kernel::component::{Component, StaticComponent, StaticComponentFinalize};
use kernel::debug::{DebugWriter, DebugWriterWrapper};
use kernel::hil;
use kernel::hil::uart;
use kernel::hil::uart::Transmit;
use kernel::static_init;

// The sum of the output_buf and internal_buf is set to a multiple of 1024 bytes in order to avoid excessive
// padding between kernel memory and application memory (which often needs to be aligned to at
// least a 1 KiB boundary). This is not _semantically_ critical, but helps keep buffers on 1 KiB
// boundaries in some cases. Of course, these definitions are only advisory, and individual boards
// can choose to pass in their own buffers with different lengths.
pub const DEBUG_BUFFER_KBYTE: usize = 1;

// Bytes [0, DEBUG_BUFFER_SPLIT) are used for output_buf while bytes
// [DEBUG_BUFFER_SPLIT, DEBUG_BUFFER_KBYTE * 1024) are used for internal_buf.
pub const DEBUG_BUFFER_SPLIT: usize = 64;

pub struct DebugWriterComponent {
    uart_mux: &'static MuxUart<'static>,
}

impl DebugWriterComponent {
    pub fn new(uart_mux: &'static MuxUart) -> DebugWriterComponent {
        DebugWriterComponent { uart_mux: uart_mux }
    }
}

pub struct Capability;
unsafe impl capabilities::ProcessManagementCapability for Capability {}

impl Component for DebugWriterComponent {
    type StaticInput = ();
    type Output = ();

    unsafe fn finalize(self, _s: Self::StaticInput) -> Self::Output {
        let buf = static_init!(
            [u8; 1024 * DEBUG_BUFFER_KBYTE],
            [0; 1024 * DEBUG_BUFFER_KBYTE]
        );
        let (output_buf, internal_buf) = buf.split_at_mut(DEBUG_BUFFER_SPLIT);

        // Create virtual device for kernel debug.
        let debugger_uart = static_init!(UartDevice, UartDevice::new(self.uart_mux, false));
        debugger_uart.setup();
        let ring_buffer = static_init!(RingBuffer<'static, u8>, RingBuffer::new(internal_buf));
        let debugger = static_init!(
            kernel::debug::DebugWriter,
            kernel::debug::DebugWriter::new(debugger_uart, output_buf, ring_buffer)
        );
        hil::uart::Transmit::set_transmit_client(debugger_uart, debugger);

        let debug_wrapper = static_init!(
            kernel::debug::DebugWriterWrapper,
            kernel::debug::DebugWriterWrapper::new(debugger)
        );
        kernel::debug::set_debug_writer_wrapper(debug_wrapper);
    }
}

pub struct DebugWriterNoMuxComponent<U: uart::Uart<'static> + uart::Transmit<'static> + 'static> {
    uart: &'static U,
}

impl<U: uart::Uart<'static> + uart::Transmit<'static> + 'static> DebugWriterNoMuxComponent<U> {
    pub fn new(uart: &'static U) -> Self {
        Self { uart }
    }
}

impl<U: uart::Uart<'static> + uart::Transmit<'static> + 'static> Component
    for DebugWriterNoMuxComponent<U>
{
    type StaticInput = ();
    type Output = ();

    unsafe fn finalize(self, _s: Self::StaticInput) -> Self::Output {
        let buf = static_init!(
            [u8; 1024 * DEBUG_BUFFER_KBYTE],
            [0; 1024 * DEBUG_BUFFER_KBYTE]
        );
        let (output_buf, internal_buf) = buf.split_at_mut(DEBUG_BUFFER_SPLIT);

        // Create virtual device for kernel debug.
        let ring_buffer = static_init!(RingBuffer<'static, u8>, RingBuffer::new(internal_buf));
        let debugger = static_init!(
            kernel::debug::DebugWriter,
            kernel::debug::DebugWriter::new(self.uart, output_buf, ring_buffer)
        );
        hil::uart::Transmit::set_transmit_client(self.uart, debugger);

        let debug_wrapper = static_init!(
            kernel::debug::DebugWriterWrapper,
            kernel::debug::DebugWriterWrapper::new(debugger)
        );
        kernel::debug::set_debug_writer_wrapper(debug_wrapper);

        let _ = self.uart.configure(uart::Parameters {
            baud_rate: 115200,
            width: uart::Width::Eight,
            stop_bits: uart::StopBits::One,
            parity: uart::Parity::None,
            hw_flow_control: false,
        });
    }
}

impl StaticComponentFinalize for DebugWriterComponent {
    type FinaliseInput = ();

    fn component_finalize(
        slf: &'static Self::Output,
        state: &'static Self::StaticState,
        _input: Self::FinaliseInput,
    ) {
        state.setup();
        state.set_transmit_client(slf);
    }
}

impl const StaticComponent for DebugWriterComponent {
    type Output = DebugWriter;
    type StaticState = UartDevice<'static>;
    type StaticStateMut = (RingBuffer<'static, u8>, DebugWriterWrapper);

    type BufferBytes = [u8; 1024 * DEBUG_BUFFER_KBYTE];

    type NewInput<'a> = &'static MuxUart<'static>;

    fn component_new<'a>(
        slf: &'static Self::Output,
        state: &'static Self::StaticState,
        state_mut: &'static mut Self::StaticStateMut,
        buffer: &'static mut Self::BufferBytes,
        input: Self::NewInput<'a>,
    ) -> (Self::Output, Self::StaticState, Self::StaticStateMut) {
        let (output_buf, internal_buf) = buffer.split_at_mut(DEBUG_BUFFER_SPLIT);
        let debug_writer = DebugWriter::new(state, output_buf, &mut state_mut.0);
        (
            debug_writer,
            UartDevice::new(input, false),
            (RingBuffer::new(internal_buf), DebugWriterWrapper::new(slf)),
        )
    }
}

// A version of the debug writer component without a uart device mux.
pub struct LegacyDebugWriterComponent();

impl const StaticComponent for LegacyDebugWriterComponent {
    type Output = DebugWriter;
    type StaticState = DebugWriterWrapper;
    type StaticStateMut = RingBuffer<'static, u8>;
    type BufferBytes = [u8; 1024 * DEBUG_BUFFER_KBYTE];

    type NewInput<'a> = &'static dyn hil::uart::Transmit<'static>;

    fn component_new<'a>(
        slf: &'static Self::Output,
        _state: &'static Self::StaticState,
        state_mut: &'static mut Self::StaticStateMut,
        buffer: &'static mut Self::BufferBytes,
        input: Self::NewInput<'a>,
    ) -> (Self::Output, Self::StaticState, Self::StaticStateMut) {
        let (output_buf, internal_buf) = buffer.split_at_mut(DEBUG_BUFFER_SPLIT);
        let debug_writer = DebugWriter::new(input, output_buf, state_mut);
        (
            debug_writer,
            DebugWriterWrapper::new(slf),
            RingBuffer::new(internal_buf),
        )
    }
}

impl StaticComponentFinalize for LegacyDebugWriterComponent {
    type FinaliseInput = ();

    fn component_finalize(
        _slf: &'static Self::Output,
        state: &'static Self::StaticState,
        _input: Self::FinaliseInput,
    ) {
        // Safety: nothing is unsafe about set_debug_writer_wrapper afaict. If it turns out
        // calling this more than once is unsafe, we can always add a singleton check to the
        // constructor for DebugWriterWrapper.
        unsafe {
            kernel::debug::set_debug_writer_wrapper(state);
        }
    }
}
