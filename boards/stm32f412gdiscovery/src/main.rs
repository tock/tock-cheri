//! Board file for STM32F412GDiscovery Discovery kit development board
//!
//! - <https://www.st.com/en/evaluation-tools/32f412gdiscovery.html>

#![no_std]
// Disable this attribute when documenting, as a workaround for
// https://github.com/rust-lang/rust/issues/62184.
#![cfg_attr(not(doc), no_main)]
#![deny(missing_docs)]
use capsules::virtual_alarm::VirtualMuxAlarm;
use components::gpio::GpioComponent;
use components::rng::RngComponent;
use kernel::capabilities;
use kernel::component::Component;
use kernel::dynamic_deferred_call::{DynamicDeferredCall, DynamicDeferredCallClientState};
use kernel::hil::gpio;
use kernel::hil::led::LedLow;
use kernel::hil::screen::ScreenRotation;
use kernel::platform::{KernelResources, SyscallDriverLookup};
use kernel::scheduler::round_robin::RoundRobinSched;
use kernel::{create_capability, debug, static_init};
use stm32f412g::interrupt_service::Stm32f412gDefaultPeripherals;

/// Support routines for debugging I/O.
pub mod io;

// Number of concurrent processes this platform supports.
const NUM_PROCS: usize = 4;

// Actual memory for holding the active process structures.
static mut PROCESSES: kernel::ProcessArray<NUM_PROCS> = kernel::Kernel::init_process_array();

static mut CHIP: Option<&'static stm32f412g::chip::Stm32f4xx<Stm32f412gDefaultPeripherals>> = None;
static mut PROCESS_PRINTER: Option<&'static kernel::process::ProcessPrinterText> = None;

// How should the kernel respond when a process faults.
const FAULT_RESPONSE: kernel::process::PanicFaultPolicy = kernel::process::PanicFaultPolicy {};

/// Dummy buffer that causes the linker to reserve enough space for the stack.
#[no_mangle]
#[link_section = ".stack_buffer"]
pub static mut STACK_MEMORY: [u8; 0x2000] = [0; 0x2000];

/// A structure representing this platform that holds references to all
/// capsules for this platform.
struct STM32F412GDiscovery {
    console: &'static capsules::console::Console<'static>,
    ipc: kernel::ipc::IPC<{ NUM_PROCS as u8 }>,
    led: &'static capsules::led::LedDriver<
        'static,
        LedLow<'static, stm32f412g::gpio::Pin<'static>>,
        4,
    >,
    button: &'static capsules::button::Button<'static, stm32f412g::gpio::Pin<'static>>,
    alarm: &'static capsules::alarm::AlarmDriver<
        'static,
        VirtualMuxAlarm<'static, stm32f412g::tim2::Tim2<'static>>,
    >,
    gpio: &'static capsules::gpio::GPIO<'static, stm32f412g::gpio::Pin<'static>>,
    adc: &'static capsules::adc::AdcVirtualized<'static>,
    touch: &'static capsules::touch::Touch<'static>,
    screen: &'static capsules::screen::Screen<'static>,
    temperature: &'static capsules::temperature::TemperatureSensor<'static>,
    rng: &'static capsules::rng::RngDriver<'static>,

    scheduler: &'static RoundRobinSched<'static>,
    systick: cortexm4::systick::SysTick,
}

/// Mapping of integer syscalls to objects that implement syscalls.
impl SyscallDriverLookup for STM32F412GDiscovery {
    fn with_driver<F, R>(&self, driver_num: usize, f: F) -> R
    where
        F: FnOnce(Option<&dyn kernel::syscall::SyscallDriver>) -> R,
    {
        match driver_num {
            capsules::console::DRIVER_NUM => f(Some(self.console)),
            capsules::led::DRIVER_NUM => f(Some(self.led)),
            capsules::button::DRIVER_NUM => f(Some(self.button)),
            capsules::alarm::DRIVER_NUM => f(Some(self.alarm)),
            kernel::ipc::DRIVER_NUM => f(Some(&self.ipc)),
            capsules::gpio::DRIVER_NUM => f(Some(self.gpio)),
            capsules::adc::DRIVER_NUM => f(Some(self.adc)),
            capsules::touch::DRIVER_NUM => f(Some(self.touch)),
            capsules::screen::DRIVER_NUM => f(Some(self.screen)),
            capsules::temperature::DRIVER_NUM => f(Some(self.temperature)),
            capsules::rng::DRIVER_NUM => f(Some(self.rng)),
            _ => f(None),
        }
    }
}

impl
    KernelResources<
        stm32f412g::chip::Stm32f4xx<
            'static,
            stm32f412g::interrupt_service::Stm32f412gDefaultPeripherals<'static>,
        >,
    > for STM32F412GDiscovery
{
    type SyscallDriverLookup = Self;
    type SyscallFilter = ();
    type ProcessFault = ();
    type Scheduler = RoundRobinSched<'static>;
    type SchedulerTimer = cortexm4::systick::SysTick;
    type WatchDog = ();
    type ContextSwitchCallback = ();

    fn syscall_driver_lookup(&self) -> &Self::SyscallDriverLookup {
        &self
    }
    fn syscall_filter(&self) -> &Self::SyscallFilter {
        &()
    }
    fn process_fault(&self) -> &Self::ProcessFault {
        &()
    }
    fn scheduler(&self) -> &Self::Scheduler {
        self.scheduler
    }
    fn scheduler_timer(&self) -> &Self::SchedulerTimer {
        &self.systick
    }
    fn watchdog(&self) -> &Self::WatchDog {
        &()
    }
    fn context_switch_callback(&self) -> &Self::ContextSwitchCallback {
        &()
    }
}

/// Helper function called during bring-up that configures DMA.
unsafe fn setup_dma(
    dma: &stm32f412g::dma::Dma1,
    dma_streams: &'static [stm32f412g::dma::Stream<stm32f412g::dma::Dma1>; 8],
    usart2: &'static stm32f412g::usart::Usart<stm32f412g::dma::Dma1>,
) {
    use stm32f412g::dma::Dma1Peripheral;
    use stm32f412g::usart;

    dma.enable_clock();

    let usart2_tx_stream = &dma_streams[Dma1Peripheral::USART2_TX.get_stream_idx()];
    let usart2_rx_stream = &dma_streams[Dma1Peripheral::USART2_RX.get_stream_idx()];

    usart2.set_dma(
        usart::TxDMA(usart2_tx_stream),
        usart::RxDMA(usart2_rx_stream),
    );

    usart2_tx_stream.set_client(usart2);
    usart2_rx_stream.set_client(usart2);

    usart2_tx_stream.setup(Dma1Peripheral::USART2_TX);
    usart2_rx_stream.setup(Dma1Peripheral::USART2_RX);

    cortexm4::nvic::Nvic::new(Dma1Peripheral::USART2_TX.get_stream_irqn()).enable();
    cortexm4::nvic::Nvic::new(Dma1Peripheral::USART2_RX.get_stream_irqn()).enable();
}

/// Helper function called during bring-up that configures multiplexed I/O.
unsafe fn set_pin_primary_functions(
    syscfg: &stm32f412g::syscfg::Syscfg,
    i2c1: &stm32f412g::i2c::I2C,
    gpio_ports: &'static stm32f412g::gpio::GpioPorts<'static>,
) {
    use kernel::hil::gpio::Configure;
    use stm32f412g::gpio::{AlternateFunction, Mode, PinId, PortId};

    syscfg.enable_clock();

    gpio_ports.get_port_from_port_id(PortId::E).enable_clock();

    // User LD3 is connected to PE02. Configure PE02 as `debug_gpio!(0, ...)`
    gpio_ports.get_pin(PinId::PE02).map(|pin| {
        pin.make_output();

        // Configure kernel debug gpios as early as possible
        kernel::debug::assign_gpios(Some(pin), None, None);
    });

    gpio_ports.get_port_from_port_id(PortId::A).enable_clock();

    // pa2 and pa3 (USART2) is connected to ST-LINK virtual COM port
    gpio_ports.get_pin(PinId::PA02).map(|pin| {
        pin.set_mode(Mode::AlternateFunctionMode);
        // AF7 is USART2_TX
        pin.set_alternate_function(AlternateFunction::AF7);
    });
    gpio_ports.get_pin(PinId::PA03).map(|pin| {
        pin.set_mode(Mode::AlternateFunctionMode);
        // AF7 is USART2_RX
        pin.set_alternate_function(AlternateFunction::AF7);
    });

    // uncomment this if you do not plan to use the joystick up, as they both use Exti0
    // joystick selection is connected on pa00
    // gpio_ports.get_pin(PinId::PA00).map(|pin| {
    //     pin.enable_interrupt();
    // });

    // joystick down is connected on pg01
    gpio_ports.get_pin(PinId::PG01).map(|pin| {
        pin.enable_interrupt();
    });

    // joystick left is connected on pf15
    gpio_ports.get_pin(PinId::PF15).map(|pin| {
        pin.enable_interrupt();
    });

    // joystick right is connected on pf14
    gpio_ports.get_pin(PinId::PF14).map(|pin| {
        pin.enable_interrupt();
    });

    // joystick up is connected on pg00
    gpio_ports.get_pin(PinId::PG00).map(|pin| {
        pin.enable_interrupt();
    });

    // enable interrupt for D0
    gpio_ports.get_pin(PinId::PG09).map(|pin| {
        pin.enable_interrupt();
    });

    // Enable clocks for GPIO Ports
    // Disable some of them if you don't need some of the GPIOs
    gpio_ports.get_port_from_port_id(PortId::B).enable_clock();
    // Ports A and E are already enabled
    gpio_ports.get_port_from_port_id(PortId::C).enable_clock();
    gpio_ports.get_port_from_port_id(PortId::D).enable_clock();
    gpio_ports.get_port_from_port_id(PortId::F).enable_clock();
    gpio_ports.get_port_from_port_id(PortId::G).enable_clock();
    gpio_ports.get_port_from_port_id(PortId::H).enable_clock();

    // I2C1 has the TouchPanel connected
    gpio_ports.get_pin(PinId::PB06).map(|pin| {
        // pin.make_output();
        pin.set_mode_output_opendrain();
        pin.set_mode(Mode::AlternateFunctionMode);
        pin.set_floating_state(kernel::hil::gpio::FloatingState::PullNone);
        // AF4 is I2C
        pin.set_alternate_function(AlternateFunction::AF4);
    });
    gpio_ports.get_pin(PinId::PB07).map(|pin| {
        // pin.make_output();
        pin.set_mode_output_opendrain();
        pin.set_floating_state(kernel::hil::gpio::FloatingState::PullNone);
        pin.set_mode(Mode::AlternateFunctionMode);
        // AF4 is I2C
        pin.set_alternate_function(AlternateFunction::AF4);
    });

    i2c1.enable_clock();
    i2c1.set_speed(stm32f412g::i2c::I2CSpeed::Speed100k, 16);

    // FT6206 interrupt
    gpio_ports.get_pin(PinId::PG05).map(|pin| {
        pin.enable_interrupt();
    });

    // ADC

    // Arduino A0
    gpio_ports.get_pin(PinId::PA01).map(|pin| {
        pin.set_mode(stm32f412g::gpio::Mode::AnalogMode);
    });

    // Arduino A1
    gpio_ports.get_pin(PinId::PC01).map(|pin| {
        pin.set_mode(stm32f412g::gpio::Mode::AnalogMode);
    });

    // Arduino A2
    gpio_ports.get_pin(PinId::PC03).map(|pin| {
        pin.set_mode(stm32f412g::gpio::Mode::AnalogMode);
    });

    // Arduino A3
    gpio_ports.get_pin(PinId::PC04).map(|pin| {
        pin.set_mode(stm32f412g::gpio::Mode::AnalogMode);
    });

    // Arduino A4
    gpio_ports.get_pin(PinId::PC05).map(|pin| {
        pin.set_mode(stm32f412g::gpio::Mode::AnalogMode);
    });

    // Arduino A5
    gpio_ports.get_pin(PinId::PB00).map(|pin| {
        pin.set_mode(stm32f412g::gpio::Mode::AnalogMode);
    });

    // EXTI9_5 interrupts is delivered at IRQn 23 (EXTI9_5)
    cortexm4::nvic::Nvic::new(stm32f412g::nvic::EXTI9_5).enable();

    // LCD

    let pins = [
        PinId::PD00,
        PinId::PD01,
        PinId::PD04,
        PinId::PD05,
        PinId::PD08,
        PinId::PD09,
        PinId::PD10,
        PinId::PD14,
        PinId::PD15,
        PinId::PD07,
        PinId::PE07,
        PinId::PE08,
        PinId::PE09,
        PinId::PE10,
        PinId::PE11,
        PinId::PE12,
        PinId::PE13,
        PinId::PE14,
        PinId::PE15,
        PinId::PF00,
    ];

    for pin in pins.iter() {
        gpio_ports.get_pin(*pin).map(|pin| {
            pin.set_mode(stm32f412g::gpio::Mode::AlternateFunctionMode);
            pin.set_floating_state(gpio::FloatingState::PullUp);
            pin.set_speed();
            pin.set_alternate_function(stm32f412g::gpio::AlternateFunction::AF12);
        });
    }

    use kernel::hil::gpio::Output;

    gpio_ports.get_pin(PinId::PF05).map(|pin| {
        pin.make_output();
        pin.set_floating_state(gpio::FloatingState::PullNone);
        pin.set();
    });

    gpio_ports.get_pin(PinId::PG04).map(|pin| {
        pin.make_input();
    });
}

/// Helper function for miscellaneous peripheral functions
unsafe fn setup_peripherals(
    tim2: &stm32f412g::tim2::Tim2,
    fsmc: &stm32f412g::fsmc::Fsmc,
    trng: &stm32f412g::trng::Trng,
) {
    // USART2 IRQn is 38
    cortexm4::nvic::Nvic::new(stm32f412g::nvic::USART2).enable();

    // TIM2 IRQn is 28
    tim2.enable_clock();
    tim2.start();
    cortexm4::nvic::Nvic::new(stm32f412g::nvic::TIM2).enable();

    // FSMC
    fsmc.enable();

    // RNG
    trng.enable_clock();
}

/// Statically initialize the core peripherals for the chip.
///
/// This is in a separate, inline(never) function so that its stack frame is
/// removed when this function returns. Otherwise, the stack space used for
/// these static_inits is wasted.
#[inline(never)]
unsafe fn get_peripherals() -> (
    &'static mut Stm32f412gDefaultPeripherals<'static>,
    &'static stm32f412g::syscfg::Syscfg<'static>,
    &'static stm32f412g::dma::Dma1<'static>,
) {
    let rcc = static_init!(stm32f412g::rcc::Rcc, stm32f412g::rcc::Rcc::new());
    let syscfg = static_init!(
        stm32f412g::syscfg::Syscfg,
        stm32f412g::syscfg::Syscfg::new(rcc)
    );

    let exti = static_init!(stm32f412g::exti::Exti, stm32f412g::exti::Exti::new(syscfg));

    let dma1 = static_init!(stm32f412g::dma::Dma1, stm32f412g::dma::Dma1::new(rcc));
    let dma2 = static_init!(stm32f412g::dma::Dma2, stm32f412g::dma::Dma2::new(rcc));

    let peripherals = static_init!(
        Stm32f412gDefaultPeripherals,
        Stm32f412gDefaultPeripherals::new(rcc, exti, dma1, dma2)
    );
    (peripherals, syscfg, dma1)
}

/// Main function.
///
/// This is called after RAM initialization is complete.
#[no_mangle]
pub unsafe fn main() {
    stm32f412g::init();

    let (peripherals, syscfg, dma1) = get_peripherals();
    peripherals.init();
    let base_peripherals = &peripherals.stm32f4;
    setup_peripherals(
        &base_peripherals.tim2,
        &base_peripherals.fsmc,
        &peripherals.trng,
    );

    // We use the default HSI 16Mhz clock
    set_pin_primary_functions(syscfg, &base_peripherals.i2c1, &base_peripherals.gpio_ports);

    setup_dma(
        dma1,
        &base_peripherals.dma1_streams,
        &base_peripherals.usart2,
    );

    let board_kernel = static_init!(kernel::Kernel, kernel::Kernel::new(&PROCESSES));

    let dynamic_deferred_call_clients =
        static_init!([DynamicDeferredCallClientState; 2], Default::default());
    let dynamic_deferred_caller = static_init!(
        DynamicDeferredCall,
        DynamicDeferredCall::new(dynamic_deferred_call_clients)
    );
    DynamicDeferredCall::set_global_instance(dynamic_deferred_caller);

    let chip = static_init!(
        stm32f412g::chip::Stm32f4xx<Stm32f412gDefaultPeripherals>,
        stm32f412g::chip::Stm32f4xx::new(peripherals)
    );
    CHIP = Some(chip);

    // UART

    // Create a shared UART channel for kernel debug.
    base_peripherals.usart2.enable_clock();
    let uart_mux = components::console::UartMuxComponent::new(
        &base_peripherals.usart2,
        115200,
        dynamic_deferred_caller,
    )
    .finalize(());

    io::WRITER.set_initialized();

    // Create capabilities that the board needs to call certain protected kernel
    // functions.
    let memory_allocation_capability = create_capability!(capabilities::MemoryAllocationCapability);
    let main_loop_capability = create_capability!(capabilities::MainLoopCapability);
    let process_management_capability =
        create_capability!(capabilities::ProcessManagementCapability);

    // Setup the console.
    let console = components::console::ConsoleComponent::new(
        board_kernel,
        capsules::console::DRIVER_NUM,
        uart_mux,
    )
    .finalize(components::console_component_helper!());
    // Create the debugger object that handles calls to `debug!()`.
    components::debug_writer::DebugWriterComponent::new(uart_mux).finalize(());

    // LEDs

    // Clock to Port A is enabled in `set_pin_primary_functions()`

    let led = components::led::LedsComponent::new().finalize(components::led_component_helper!(
        LedLow<'static, stm32f412g::gpio::Pin>,
        LedLow::new(
            base_peripherals
                .gpio_ports
                .get_pin(stm32f412g::gpio::PinId::PE00)
                .unwrap()
        ),
        LedLow::new(
            base_peripherals
                .gpio_ports
                .get_pin(stm32f412g::gpio::PinId::PE01)
                .unwrap()
        ),
        LedLow::new(
            base_peripherals
                .gpio_ports
                .get_pin(stm32f412g::gpio::PinId::PE02)
                .unwrap()
        ),
        LedLow::new(
            base_peripherals
                .gpio_ports
                .get_pin(stm32f412g::gpio::PinId::PE03)
                .unwrap()
        ),
    ));

    // BUTTONs
    let button = components::button::ButtonComponent::new(
        board_kernel,
        capsules::button::DRIVER_NUM,
        components::button_component_helper!(
            stm32f412g::gpio::Pin,
            // Select
            (
                base_peripherals
                    .gpio_ports
                    .get_pin(stm32f412g::gpio::PinId::PA00)
                    .unwrap(),
                kernel::hil::gpio::ActivationMode::ActiveHigh,
                kernel::hil::gpio::FloatingState::PullNone
            ),
            // Down
            (
                base_peripherals
                    .gpio_ports
                    .get_pin(stm32f412g::gpio::PinId::PG01)
                    .unwrap(),
                kernel::hil::gpio::ActivationMode::ActiveHigh,
                kernel::hil::gpio::FloatingState::PullNone
            ),
            // Left
            (
                base_peripherals
                    .gpio_ports
                    .get_pin(stm32f412g::gpio::PinId::PF15)
                    .unwrap(),
                kernel::hil::gpio::ActivationMode::ActiveHigh,
                kernel::hil::gpio::FloatingState::PullNone
            ),
            // Right
            (
                base_peripherals
                    .gpio_ports
                    .get_pin(stm32f412g::gpio::PinId::PF14)
                    .unwrap(),
                kernel::hil::gpio::ActivationMode::ActiveHigh,
                kernel::hil::gpio::FloatingState::PullNone
            ),
            // Up
            (
                base_peripherals
                    .gpio_ports
                    .get_pin(stm32f412g::gpio::PinId::PG00)
                    .unwrap(),
                kernel::hil::gpio::ActivationMode::ActiveHigh,
                kernel::hil::gpio::FloatingState::PullNone
            )
        ),
    )
    .finalize(components::button_component_buf!(stm32f412g::gpio::Pin));

    // ALARM

    let tim2 = &base_peripherals.tim2;
    let mux_alarm = components::alarm::AlarmMuxComponent::new(tim2).finalize(
        components::alarm_mux_component_helper!(stm32f412g::tim2::Tim2),
    );

    let alarm = components::alarm::AlarmDriverComponent::new(
        board_kernel,
        capsules::alarm::DRIVER_NUM,
        mux_alarm,
    )
    .finalize(components::alarm_component_helper!(stm32f412g::tim2::Tim2));

    // GPIO
    let gpio = GpioComponent::new(
        board_kernel,
        capsules::gpio::DRIVER_NUM,
        components::gpio_component_helper!(
            stm32f412g::gpio::Pin,
            // Arduino like RX/TX
            0 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PG09).unwrap(), //D0
            1 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PG14).unwrap(), //D1
            2 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PG13).unwrap(), //D2
            3 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PF04).unwrap(), //D3
            4 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PG12).unwrap(), //D4
            5 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PF10).unwrap(), //D5
            6 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PF03).unwrap(), //D6
            7 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PG11).unwrap(), //D7
            8 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PG10).unwrap(), //D8
            9 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PB08).unwrap(), //D9
            // SPI Pins
            10 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PA15).unwrap(), //D10
            11 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PA07).unwrap(),  //D11
            12 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PA06).unwrap(),  //D12
            13 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PA15).unwrap()  //D13

            // ADC Pins
            // Enable the to use the ADC pins as GPIO
            // 14 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PA01).unwrap(), //A0
            // 15 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PC01).unwrap(), //A1
            // 16 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PC03).unwrap(), //A2
            // 17 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PC04).unwrap(), //A3
            // 19 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PC05).unwrap(), //A4
            // 20 => base_peripherals.gpio_ports.get_pin(stm32f412g::gpio::PinId::PB00).unwrap() //A5
        ),
    )
    .finalize(components::gpio_component_buf!(stm32f412g::gpio::Pin));

    // RNG
    let rng =
        RngComponent::new(board_kernel, capsules::rng::DRIVER_NUM, &peripherals.trng).finalize(());

    // FT6206

    let mux_i2c = components::i2c::I2CMuxComponent::new(
        &base_peripherals.i2c1,
        None,
        dynamic_deferred_caller,
    )
    .finalize(components::i2c_mux_component_helper!());

    let ft6x06 = components::ft6x06::Ft6x06Component::new(
        base_peripherals
            .gpio_ports
            .get_pin(stm32f412g::gpio::PinId::PG05)
            .unwrap(),
    )
    .finalize(components::ft6x06_i2c_component_helper!(mux_i2c));

    let bus = components::bus::Bus8080BusComponent::new().finalize(
        components::bus8080_bus_component_helper!(
            // bus type
            stm32f412g::fsmc::Fsmc,
            // bus
            &base_peripherals.fsmc
        ),
    );

    let tft = components::st77xx::ST77XXComponent::new(mux_alarm).finalize(
        components::st77xx_component_helper!(
            // screen
            &capsules::st77xx::ST7789H2,
            // bus type
            capsules::bus::Bus8080Bus<'static, stm32f412g::fsmc::Fsmc>,
            // bus
            &bus,
            // timer type
            stm32f412g::tim2::Tim2,
            // pin type
            stm32f412g::gpio::Pin,
            // dc pin (optional)
            None,
            // reset pin
            base_peripherals
                .gpio_ports
                .get_pin(stm32f412g::gpio::PinId::PD11)
        ),
    );

    let _ = tft.init();

    let screen = components::screen::ScreenComponent::new(
        board_kernel,
        capsules::screen::DRIVER_NUM,
        tft,
        Some(tft),
    )
    .finalize(components::screen_buffer_size!(57600));

    let touch = components::touch::MultiTouchComponent::new(
        board_kernel,
        capsules::touch::DRIVER_NUM,
        ft6x06,
        Some(ft6x06),
        Some(tft),
    )
    .finalize(());

    touch.set_screen_rotation_offset(ScreenRotation::Rotated90);

    // Uncomment this for multi touch support
    // let touch =
    //     components::touch::MultiTouchComponent::new(board_kernel, ft6x06, Some(ft6x06), None)
    //         .finalize(());

    // ADC
    let adc_mux = components::adc::AdcMuxComponent::new(&base_peripherals.adc1)
        .finalize(components::adc_mux_component_helper!(stm32f412g::adc::Adc));

    let temp_sensor = components::temperature_stm::TemperatureSTMComponent::new(2.5, 0.76)
        .finalize(components::temperaturestm_adc_component_helper!(
            // spi type
            stm32f412g::adc::Adc,
            // chip select
            stm32f412g::adc::Channel::Channel18,
            // spi mux
            adc_mux
        ));
    let grant_cap = create_capability!(capabilities::MemoryAllocationCapability);
    let grant_temperature =
        board_kernel.create_grant(capsules::temperature::DRIVER_NUM, &grant_cap);

    let temp = static_init!(
        capsules::temperature::TemperatureSensor<'static>,
        capsules::temperature::TemperatureSensor::new(temp_sensor, grant_temperature)
    );
    kernel::hil::sensors::TemperatureDriver::set_client(temp_sensor, temp);

    let adc_channel_0 =
        components::adc::AdcComponent::new(&adc_mux, stm32f412g::adc::Channel::Channel1)
            .finalize(components::adc_component_helper!(stm32f412g::adc::Adc));

    let adc_channel_1 =
        components::adc::AdcComponent::new(&adc_mux, stm32f412g::adc::Channel::Channel11)
            .finalize(components::adc_component_helper!(stm32f412g::adc::Adc));

    let adc_channel_2 =
        components::adc::AdcComponent::new(&adc_mux, stm32f412g::adc::Channel::Channel13)
            .finalize(components::adc_component_helper!(stm32f412g::adc::Adc));

    let adc_channel_3 =
        components::adc::AdcComponent::new(&adc_mux, stm32f412g::adc::Channel::Channel14)
            .finalize(components::adc_component_helper!(stm32f412g::adc::Adc));

    let adc_channel_4 =
        components::adc::AdcComponent::new(&adc_mux, stm32f412g::adc::Channel::Channel15)
            .finalize(components::adc_component_helper!(stm32f412g::adc::Adc));

    let adc_channel_5 =
        components::adc::AdcComponent::new(&adc_mux, stm32f412g::adc::Channel::Channel8)
            .finalize(components::adc_component_helper!(stm32f412g::adc::Adc));

    let adc_syscall =
        components::adc::AdcVirtualComponent::new(board_kernel, capsules::adc::DRIVER_NUM)
            .finalize(components::adc_syscall_component_helper!(
                adc_channel_0,
                adc_channel_1,
                adc_channel_2,
                adc_channel_3,
                adc_channel_4,
                adc_channel_5
            ));

    let process_printer =
        components::process_printer::ProcessPrinterTextComponent::new().finalize(());
    PROCESS_PRINTER = Some(process_printer);

    // PROCESS CONSOLE
    let process_console = components::process_console::ProcessConsoleComponent::new(
        board_kernel,
        uart_mux,
        mux_alarm,
        process_printer,
    )
    .finalize(components::process_console_component_helper!(
        stm32f412g::tim2::Tim2
    ));
    let _ = process_console.start();

    let scheduler = components::sched::round_robin::RoundRobinComponent::new(&PROCESSES)
        .finalize(components::rr_component_helper!(NUM_PROCS));

    let stm32f412g = STM32F412GDiscovery {
        console,
        ipc: kernel::ipc::IPC::new(
            board_kernel,
            kernel::ipc::DRIVER_NUM,
            &memory_allocation_capability,
        ),
        led,
        button,
        alarm,
        gpio,
        adc: adc_syscall,
        touch,
        screen,
        temperature: temp,
        rng,

        scheduler,
        systick: cortexm4::systick::SysTick::new(),
    };

    // // Optional kernel tests
    // //
    // // See comment in `boards/imix/src/main.rs`
    // virtual_uart_rx_test::run_virtual_uart_receive(mux_uart);
    // base_peripherals.fsmc.write(0x04, 120);
    // debug!("id {}", base_peripherals.fsmc.read(0x05));

    debug!("Initialization complete. Entering main loop");

    extern "C" {
        /// Beginning of the ROM region containing app images.
        ///
        /// This symbol is defined in the linker script.
        static _sapps: u8;

        /// End of the ROM region containing app images.
        ///
        /// This symbol is defined in the linker script.
        static _eapps: u8;

        /// Beginning of the RAM region for app memory.
        ///
        /// This symbol is defined in the linker script.
        static mut _sappmem: u8;

        /// End of the RAM region for app memory.
        ///
        /// This symbol is defined in the linker script.
        static _eappmem: u8;
    }

    kernel::process::load_processes(
        board_kernel,
        chip,
        core::slice::from_raw_parts(
            &_sapps as *const u8,
            &_eapps as *const u8 as usize - &_sapps as *const u8 as usize,
        ),
        core::slice::from_raw_parts_mut(
            &mut _sappmem as *mut u8,
            &_eappmem as *const u8 as usize - &_sappmem as *const u8 as usize,
        ),
        &FAULT_RESPONSE,
        &process_management_capability,
    )
    .unwrap_or_else(|err| {
        debug!("Error loading processes!");
        debug!("{:?}", err);
    });

    //Uncomment to run multi alarm test
    /*components::test::multi_alarm_test::MultiAlarmTestComponent::new(mux_alarm)
    .finalize(components::multi_alarm_test_component_buf!(stm32f412g::tim2::Tim2))
    .run();*/

    board_kernel.kernel_loop(
        &stm32f412g,
        chip,
        Some(&stm32f412g.ipc),
        &main_loop_capability,
    );
}
