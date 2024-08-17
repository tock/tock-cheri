// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Component for DebugWriter, the implementation for `debug!()`.
//!
//! This provides components for attaching the kernel debug output (for panic!,
//! print!, debug!, etc.) to the output. `DebugWriterComponent` uses a UART mux,
//! and `DebugWriterNoMuxComponent` just uses a UART interface directly.
//!
//! Usage
//! -----
//! ```rust
//! DebugWriterComponent::new(uart_mux).finalize(components::debug_writer_component_static!());
//!
//! components::debug_writer::DebugWriterNoMuxComponent::new(
//!     &nrf52::uart::UARTE0,
//! )
//! .finalize(());
//! ```

// Author: Brad Campbell <bradjc@virginia.edu>
// Last modified: 11/07/2019

use capsules_core::virtualizers::virtual_uart::{MuxUart, UartDevice};
use core::mem::MaybeUninit;
use kernel::capabilities;
use kernel::collections::ring_buffer::RingBuffer;
use kernel::component::{Component, StaticComponent, StaticComponentFinalize};
use kernel::debug::{DebugWriter, DebugWriterWrapper};
use kernel::hil;
use kernel::hil::uart;
use kernel::hil::uart::Transmit;

// The sum of the output_buf and internal_buf is set to a multiple of 1024 bytes in order to avoid excessive
// padding between kernel memory and application memory (which often needs to be aligned to at
// least a 1 KiB boundary). This is not _semantically_ critical, but helps keep buffers on 1 KiB
// boundaries in some cases. Of course, these definitions are only advisory, and individual boards
// can choose to pass in their own buffers with different lengths.
pub const DEFAULT_DEBUG_BUFFER_KBYTE: usize = 2;

// Bytes [0, DEBUG_BUFFER_SPLIT) are used for output_buf while bytes
// [DEBUG_BUFFER_SPLIT, DEFAULT_DEBUG_BUFFER_KBYTE * 1024) are used for internal_buf.
pub const DEBUG_BUFFER_SPLIT: usize = 64;

/// The optional argument to this macro allows boards to specify the size of the in-RAM
/// buffer used for storing debug messages. Increase this value to be able to send more debug
/// messages in quick succession.
#[macro_export]
macro_rules! debug_writer_component_static {
    ($BUF_SIZE_KB:expr) => {{
        let uart = kernel::static_buf!(capsules_core::virtualizers::virtual_uart::UartDevice);
        let ring = kernel::static_buf!(kernel::collections::ring_buffer::RingBuffer<'static, u8>);
        let buffer = kernel::static_buf!([u8; 1024 * $BUF_SIZE_KB]);
        let debug = kernel::static_buf!(kernel::debug::DebugWriter);
        let debug_wrapper = kernel::static_buf!(kernel::debug::DebugWriterWrapper);

        (uart, ring, buffer, debug, debug_wrapper)
    };};
    () => {{
        $crate::debug_writer_component_static!($crate::debug_writer::DEFAULT_DEBUG_BUFFER_KBYTE)
    };};
}

/// The optional argument to this macro allows boards to specify the size of the in-RAM
/// buffer used for storing debug messages. Increase this value to be able to send more debug
/// messages in quick succession.
#[macro_export]
macro_rules! debug_writer_no_mux_component_static {
    ($BUF_SIZE_KB:expr) => {{
        let ring = kernel::static_buf!(kernel::collections::ring_buffer::RingBuffer<'static, u8>);
        let buffer = kernel::static_buf!([u8; 1024 * $BUF_SIZE_KB]);
        let debug = kernel::static_buf!(kernel::debug::DebugWriter);
        let debug_wrapper = kernel::static_buf!(kernel::debug::DebugWriterWrapper);

        (ring, buffer, debug, debug_wrapper)
    };};
    () => {{
        use $crate::debug_writer::DEFAULT_DEBUG_BUFFER_KBYTE;
        $crate::debug_writer_no_mux_component_static!(DEFAULT_DEBUG_BUFFER_KBYTE);
    };};
}

pub struct DebugWriterComponent<const BUF_SIZE_BYTES: usize> {
    uart_mux: &'static MuxUart<'static>,
    marker: core::marker::PhantomData<[u8; BUF_SIZE_BYTES]>,
}

impl<const BUF_SIZE_BYTES: usize> DebugWriterComponent<BUF_SIZE_BYTES> {
    pub fn new(uart_mux: &'static MuxUart) -> Self {
        Self {
            uart_mux,
            marker: core::marker::PhantomData,
        }
    }
}

pub struct Capability;
unsafe impl capabilities::ProcessManagementCapability for Capability {}

impl<const BUF_SIZE_BYTES: usize> Component for DebugWriterComponent<BUF_SIZE_BYTES> {
    type StaticInput = (
        &'static mut MaybeUninit<UartDevice<'static>>,
        &'static mut MaybeUninit<RingBuffer<'static, u8>>,
        &'static mut MaybeUninit<[u8; BUF_SIZE_BYTES]>,
        &'static mut MaybeUninit<kernel::debug::DebugWriter>,
        &'static mut MaybeUninit<kernel::debug::DebugWriterWrapper>,
    );
    type Output = ();

    fn finalize(self, s: Self::StaticInput) -> Self::Output {
        let buf = s.2.write([0; BUF_SIZE_BYTES]);

        let (output_buf, internal_buf) = buf.split_at_mut(DEBUG_BUFFER_SPLIT);

        // Create virtual device for kernel debug.
        let debugger_uart = s.0.write(UartDevice::new(self.uart_mux, false));
        debugger_uart.setup();
        let ring_buffer = s.1.write(RingBuffer::new(internal_buf));
        let debugger = s.3.write(kernel::debug::DebugWriter::new(
            debugger_uart,
            output_buf,
            ring_buffer,
        ));
        hil::uart::Transmit::set_transmit_client(debugger_uart, debugger);

        let debug_wrapper = s.4.write(kernel::debug::DebugWriterWrapper::new(debugger));
        unsafe {
            kernel::debug::set_debug_writer_wrapper(debug_wrapper);
        }
    }
}

pub struct DebugWriterNoMuxComponent<
    U: uart::Uart<'static> + uart::Transmit<'static> + 'static,
    const BUF_SIZE_BYTES: usize,
> {
    uart: &'static U,
    marker: core::marker::PhantomData<[u8; BUF_SIZE_BYTES]>,
}

impl<U: uart::Uart<'static> + uart::Transmit<'static> + 'static, const BUF_SIZE_BYTES: usize>
    DebugWriterNoMuxComponent<U, BUF_SIZE_BYTES>
{
    pub fn new(uart: &'static U) -> Self {
        Self {
            uart,
            marker: core::marker::PhantomData,
        }
    }
}

impl<U: uart::Uart<'static> + uart::Transmit<'static> + 'static, const BUF_SIZE_BYTES: usize>
    Component for DebugWriterNoMuxComponent<U, BUF_SIZE_BYTES>
{
    type StaticInput = (
        &'static mut MaybeUninit<RingBuffer<'static, u8>>,
        &'static mut MaybeUninit<[u8; BUF_SIZE_BYTES]>,
        &'static mut MaybeUninit<kernel::debug::DebugWriter>,
        &'static mut MaybeUninit<kernel::debug::DebugWriterWrapper>,
    );
    type Output = ();

    fn finalize(self, s: Self::StaticInput) -> Self::Output {
        let buf = s.1.write([0; BUF_SIZE_BYTES]);
        let (output_buf, internal_buf) = buf.split_at_mut(DEBUG_BUFFER_SPLIT);

        // Create virtual device for kernel debug.
        let ring_buffer = s.0.write(RingBuffer::new(internal_buf));
        let debugger = s.2.write(kernel::debug::DebugWriter::new(
            self.uart,
            output_buf,
            ring_buffer,
        ));
        hil::uart::Transmit::set_transmit_client(self.uart, debugger);

        let debug_wrapper = s.3.write(kernel::debug::DebugWriterWrapper::new(debugger));
        unsafe {
            kernel::debug::set_debug_writer_wrapper(debug_wrapper);
        }

        let _ = self.uart.configure(uart::Parameters {
            baud_rate: 115200,
            width: uart::Width::Eight,
            stop_bits: uart::StopBits::One,
            parity: uart::Parity::None,
            hw_flow_control: false,
        });
    }
}

impl<const BUF_SIZE_BYTES: usize> StaticComponentFinalize for DebugWriterComponent<BUF_SIZE_BYTES> {
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

impl<const BUF_SIZE_BYTES: usize> const StaticComponent for DebugWriterComponent<BUF_SIZE_BYTES> {
    type Output = DebugWriter;
    type StaticState = UartDevice<'static>;
    type StaticStateMut = (RingBuffer<'static, u8>, DebugWriterWrapper);

    type BufferBytes = [u8; BUF_SIZE_BYTES];

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
    type BufferBytes = [u8; 1024 * DEFAULT_DEBUG_BUFFER_KBYTE];

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
