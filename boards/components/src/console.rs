//! Components for Console, the generic serial interface, and for multiplexed access
//! to UART.
//!
//!
//! This provides two Components, `ConsoleComponent`, which implements a buffered
//! read/write console over a serial port, and `UartMuxComponent`, which provides
//! multiplexed access to hardware UART. As an example, the serial port used for
//! console on Imix is typically USART3 (the DEBUG USB connector).
//!
//! Usage
//! -----
//! ```rust
//! let uart_mux = UartMuxComponent::new(&sam4l::usart::USART3,
//!                                      115200,
//!                                      deferred_caller).finalize(());
//! let console = ConsoleComponent::new(board_kernel, uart_mux)
//!    .finalize(console_component_helper!());
//! ```
// Author: Philip Levis <pal@cs.stanford.edu>
// Last modified: 1/08/2020

use capsules::console;
use capsules::virtual_uart::{MuxUart, UartDevice};
use kernel::component::Component;
use kernel::create_capability;
use kernel::dynamic_deferred_call::{DynamicDeferredCall, ProtoDynamicDeferredCall};
use kernel::hil;
use kernel::hil::uart;
use kernel::static_init;
use kernel::utilities::static_init::StaticUninitializedBuffer;
use kernel::{capabilities, simple_static_component};

use capsules::console::{Console, DEFAULT_BUF_SIZE};
use kernel::hil::uart::{Receive, Transmit};

pub struct UartMuxComponent {
    uart: &'static dyn uart::Uart<'static>,
    baud_rate: u32,
    deferred_caller: &'static DynamicDeferredCall,
}

impl UartMuxComponent {
    pub fn new(
        uart: &'static dyn uart::Uart<'static>,
        baud_rate: u32,
        deferred_caller: &'static DynamicDeferredCall,
    ) -> UartMuxComponent {
        UartMuxComponent {
            uart,
            baud_rate,
            deferred_caller,
        }
    }
}

impl Component for UartMuxComponent {
    type StaticInput = ();
    type Output = &'static MuxUart<'static>;

    unsafe fn finalize(self, _s: Self::StaticInput) -> Self::Output {
        let uart_mux = static_init!(
            MuxUart<'static>,
            MuxUart::new(
                self.uart,
                &mut capsules::virtual_uart::RX_BUF,
                self.baud_rate,
                self.deferred_caller,
                None,
            )
        );
        uart_mux.initialize_callback_handle(
            self.deferred_caller.register(uart_mux).unwrap(), // Unwrap fail = no deferred call slot available for uart mux
        );

        uart_mux.initialize();
        hil::uart::Transmit::set_transmit_client(self.uart, uart_mux);
        hil::uart::Receive::set_receive_client(self.uart, uart_mux);

        uart_mux
    }
}

#[macro_export]
macro_rules! console_component_helper {
    () => {{
        use capsules::console::{Console, DEFAULT_BUF_SIZE};
        use capsules::virtual_uart::UartDevice;
        use kernel::static_buf;
        let read_buf = static_buf!([u8; DEFAULT_BUF_SIZE]);
        let write_buf = static_buf!([u8; DEFAULT_BUF_SIZE]);
        // Create virtual device for console.
        let console_uart = static_buf!(UartDevice);
        let console = static_buf!(Console<'static>);
        (write_buf, read_buf, console_uart, console)
    }};
}

pub struct ConsoleComponent {
    board_kernel: &'static kernel::Kernel,
    driver_num: usize,
    uart_mux: &'static MuxUart<'static>,
}

impl ConsoleComponent {
    pub fn new(
        board_kernel: &'static kernel::Kernel,
        driver_num: usize,
        uart_mux: &'static MuxUart,
    ) -> ConsoleComponent {
        ConsoleComponent {
            board_kernel: board_kernel,
            driver_num: driver_num,
            uart_mux: uart_mux,
        }
    }
}

impl Component for ConsoleComponent {
    type StaticInput = (
        StaticUninitializedBuffer<[u8; DEFAULT_BUF_SIZE]>,
        StaticUninitializedBuffer<[u8; DEFAULT_BUF_SIZE]>,
        StaticUninitializedBuffer<UartDevice<'static>>,
        StaticUninitializedBuffer<console::Console<'static>>,
    );
    type Output = &'static console::Console<'static>;

    unsafe fn finalize(self, s: Self::StaticInput) -> Self::Output {
        let grant_cap = create_capability!(capabilities::MemoryAllocationCapability);

        let write_buffer = s.0.initialize([0; DEFAULT_BUF_SIZE]);

        let read_buffer = s.1.initialize([0; DEFAULT_BUF_SIZE]);

        let console_uart = s.2.initialize(UartDevice::new(self.uart_mux, true));
        console_uart.setup();

        let console = s.3.initialize(console::Console::new(
            console_uart,
            write_buffer,
            read_buffer,
            self.board_kernel.create_grant(self.driver_num, &grant_cap),
        ));
        hil::uart::Transmit::set_transmit_client(console_uart, console);
        hil::uart::Receive::set_receive_client(console_uart, console);

        console
    }
}

pub struct UartMuxClientComponent();

simple_static_component!(impl for UartMuxClientComponent,
    Output = UartDevice<'static>,
    NewInput = (&'static MuxUart<'static>, bool),
    FinInput = (),
    |_slf, input| {UartDevice::new(input.0, input.1)},
    |slf, _input| {slf.setup()}
);

simple_static_component!(impl for ConsoleComponent,
    Inherit = UartMuxClientComponent,
    Output = Console<'static>,
    BUFFER_BYTES = 2 * DEFAULT_BUF_SIZE,
    NewInput = (&'static MuxUart<'static>, capsules::console::ConsoleGrant),
    FinInput = (),
    |_slf, input, buf, supe | super{(input.0, true)} {
        let (b1, b2) : (&mut [u8; DEFAULT_BUF_SIZE], &mut [u8; DEFAULT_BUF_SIZE]) = kernel::component::split_array_mut::<u8, {2 * DEFAULT_BUF_SIZE}, DEFAULT_BUF_SIZE, DEFAULT_BUF_SIZE>(buf);
        Console::new(supe, b1, b2, input.1)
    },
    |slf, _input, supe | super{()} {
             supe.set_transmit_client(slf);
             supe.set_receive_client(slf);
     }
);

simple_static_component!(impl for UartMuxComponent,
    Output = MuxUart<'static>,
    BUFFER_BYTES = capsules::virtual_uart::RX_BUF_LEN,
    NewInput = (&'static dyn uart::Uart<'static>, u32, &'static DynamicDeferredCall, &'a mut ProtoDynamicDeferredCall),
    FinInput = &'static dyn uart::Uart<'static>,
    |slf, input, buf | {MuxUart::new(input.0, buf, input.1, input.2, input.3.register(slf))},
    |slf, input | {
            slf.initialize();
            input.set_transmit_client(slf);
            input.set_receive_client(slf);
    }
);
