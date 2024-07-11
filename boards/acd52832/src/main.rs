//! Tock kernel for the Aconno ACD52832 board based on the Nordic nRF52832 MCU.

#![no_std]
// Disable this attribute when documenting, as a workaround for
// https://github.com/rust-lang/rust/issues/62184.
#![cfg_attr(not(doc), no_main)]
#![deny(missing_docs)]

use capsules::virtual_alarm::VirtualMuxAlarm;
use kernel::capabilities;
use kernel::component::Component;
use kernel::dynamic_deferred_call::{DynamicDeferredCall, DynamicDeferredCallClientState};
use kernel::hil;
use kernel::hil::adc::Adc;
use kernel::hil::entropy::Entropy32;
use kernel::hil::gpio::{Configure, InterruptWithValue, Output};
use kernel::hil::i2c::I2CMaster;
use kernel::hil::led::LedLow;
use kernel::hil::rng::Rng;
use kernel::hil::time::{Alarm, Counter};
use kernel::platform::{KernelResources, SyscallDriverLookup};
use kernel::scheduler::round_robin::RoundRobinSched;
#[allow(unused_imports)]
use kernel::{create_capability, debug, debug_gpio, static_init};
use nrf52832::gpio::Pin;
use nrf52832::interrupt_service::Nrf52832DefaultPeripherals;
use nrf52832::rtc::Rtc;

use nrf52_components::ble::BLEComponent;

const LED1_PIN: Pin = Pin::P0_26;
const LED2_PIN: Pin = Pin::P0_22;
const LED3_PIN: Pin = Pin::P0_23;
const LED4_PIN: Pin = Pin::P0_24;

const BUTTON1_PIN: Pin = Pin::P0_25;
const BUTTON2_PIN: Pin = Pin::P0_14;
const BUTTON3_PIN: Pin = Pin::P0_15;
const BUTTON4_PIN: Pin = Pin::P0_16;
const BUTTON_RST_PIN: Pin = Pin::P0_19;

/// UART Writer
pub mod io;

// State for loading and holding applications.
// How should the kernel respond when a process faults.
const FAULT_RESPONSE: kernel::process::PanicFaultPolicy = kernel::process::PanicFaultPolicy {};

// Number of concurrent processes this platform supports.
const NUM_PROCS: usize = 4;

static mut PROCESSES: kernel::ProcessArray<NUM_PROCS> = kernel::Kernel::init_process_array();

/// Dummy buffer that causes the linker to reserve enough space for the stack.
#[no_mangle]
#[link_section = ".stack_buffer"]
pub static mut STACK_MEMORY: [u8; 0x1000] = [0; 0x1000];

/// Supported drivers by the platform
pub struct Platform {
    ble_radio: &'static capsules::ble_advertising_driver::BLE<
        'static,
        nrf52832::ble_radio::Radio<'static>,
        VirtualMuxAlarm<'static, Rtc<'static>>,
    >,
    button: &'static capsules::button::Button<'static, nrf52832::gpio::GPIOPin<'static>>,
    console: &'static capsules::console::Console<'static>,
    gpio: &'static capsules::gpio::GPIO<'static, nrf52832::gpio::GPIOPin<'static>>,
    led: &'static capsules::led::LedDriver<
        'static,
        LedLow<'static, nrf52832::gpio::GPIOPin<'static>>,
        4,
    >,
    rng: &'static capsules::rng::RngDriver<'static>,
    temp: &'static capsules::temperature::TemperatureSensor<'static>,
    ipc: kernel::ipc::IPC<{ NUM_PROCS as u8 }>,
    alarm: &'static capsules::alarm::AlarmDriver<
        'static,
        VirtualMuxAlarm<'static, nrf52832::rtc::Rtc<'static>>,
    >,
    gpio_async:
        &'static capsules::gpio_async::GPIOAsync<'static, capsules::mcp230xx::MCP230xx<'static>>,
    light: &'static capsules::ambient_light::AmbientLight<'static>,
    buzzer: &'static capsules::buzzer_driver::Buzzer<
        'static,
        capsules::virtual_alarm::VirtualMuxAlarm<'static, nrf52832::rtc::Rtc<'static>>,
    >,
    scheduler: &'static RoundRobinSched<'static>,
    systick: cortexm4::systick::SysTick,
}

impl SyscallDriverLookup for Platform {
    fn with_driver<F, R>(&self, driver_num: usize, f: F) -> R
    where
        F: FnOnce(Option<&dyn kernel::syscall::SyscallDriver>) -> R,
    {
        match driver_num {
            capsules::console::DRIVER_NUM => f(Some(self.console)),
            capsules::gpio::DRIVER_NUM => f(Some(self.gpio)),
            capsules::alarm::DRIVER_NUM => f(Some(self.alarm)),
            capsules::led::DRIVER_NUM => f(Some(self.led)),
            capsules::button::DRIVER_NUM => f(Some(self.button)),
            capsules::rng::DRIVER_NUM => f(Some(self.rng)),
            capsules::ble_advertising_driver::DRIVER_NUM => f(Some(self.ble_radio)),
            capsules::temperature::DRIVER_NUM => f(Some(self.temp)),
            capsules::gpio_async::DRIVER_NUM => f(Some(self.gpio_async)),
            capsules::ambient_light::DRIVER_NUM => f(Some(self.light)),
            capsules::buzzer_driver::DRIVER_NUM => f(Some(self.buzzer)),
            kernel::ipc::DRIVER_NUM => f(Some(&self.ipc)),
            _ => f(None),
        }
    }
}

impl KernelResources<nrf52832::chip::NRF52<'static, Nrf52832DefaultPeripherals<'static>>>
    for Platform
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

/// This is in a separate, inline(never) function so that its stack frame is
/// removed when this function returns. Otherwise, the stack space used for
/// these static_inits is wasted.
#[inline(never)]
unsafe fn get_peripherals() -> &'static mut Nrf52832DefaultPeripherals<'static> {
    // Initialize chip peripheral drivers
    let nrf52832_peripherals = static_init!(
        Nrf52832DefaultPeripherals,
        Nrf52832DefaultPeripherals::new()
    );

    nrf52832_peripherals
}

/// Main function called after RAM initialized.
#[no_mangle]
pub unsafe fn main() {
    nrf52832::init();

    let nrf52832_peripherals = get_peripherals();

    // set up circular peripheral dependencies
    nrf52832_peripherals.init();
    let base_peripherals = &nrf52832_peripherals.nrf52;

    // Create capabilities that the board needs to call certain protected kernel
    // functions.
    let process_management_capability =
        create_capability!(capabilities::ProcessManagementCapability);
    let main_loop_capability = create_capability!(capabilities::MainLoopCapability);
    let memory_allocation_capability = create_capability!(capabilities::MemoryAllocationCapability);

    let board_kernel = static_init!(kernel::Kernel, kernel::Kernel::new(&PROCESSES));

    let dynamic_deferred_call_clients =
        static_init!([DynamicDeferredCallClientState; 2], Default::default());
    let dynamic_deferred_caller = static_init!(
        DynamicDeferredCall,
        DynamicDeferredCall::new(dynamic_deferred_call_clients)
    );
    DynamicDeferredCall::set_global_instance(dynamic_deferred_caller);

    // Make non-volatile memory writable and activate the reset button
    let uicr = nrf52832::uicr::Uicr::new();
    base_peripherals.nvmc.erase_uicr();
    base_peripherals.nvmc.configure_writeable();
    while !base_peripherals.nvmc.is_ready() {}
    uicr.set_psel0_reset_pin(BUTTON_RST_PIN);
    while !base_peripherals.nvmc.is_ready() {}
    uicr.set_psel1_reset_pin(BUTTON_RST_PIN);

    // Configure kernel debug gpios as early as possible
    kernel::debug::assign_gpios(
        Some(&nrf52832_peripherals.gpio_port[LED2_PIN]),
        Some(&nrf52832_peripherals.gpio_port[LED3_PIN]),
        Some(&nrf52832_peripherals.gpio_port[LED4_PIN]),
    );

    //
    // GPIO Pins
    //
    let gpio = components::gpio::GpioComponent::new(
        board_kernel,
        capsules::gpio::DRIVER_NUM,
        components::gpio_component_helper!(
            nrf52832::gpio::GPIOPin,
            0 => &nrf52832_peripherals.gpio_port[Pin::P0_25],
            1 => &nrf52832_peripherals.gpio_port[Pin::P0_26],
            2 => &nrf52832_peripherals.gpio_port[Pin::P0_27],
            3 => &nrf52832_peripherals.gpio_port[Pin::P0_28],
            4 => &nrf52832_peripherals.gpio_port[Pin::P0_29],
            5 => &nrf52832_peripherals.gpio_port[Pin::P0_30],
            6 => &nrf52832_peripherals.gpio_port[Pin::P0_31]
        ),
    )
    .finalize(components::gpio_component_buf!(nrf52832::gpio::GPIOPin));

    //
    // LEDs
    //
    let led = components::led::LedsComponent::new().finalize(components::led_component_helper!(
        LedLow<'static, nrf52832::gpio::GPIOPin>,
        LedLow::new(&nrf52832_peripherals.gpio_port[LED1_PIN]),
        LedLow::new(&nrf52832_peripherals.gpio_port[LED2_PIN]),
        LedLow::new(&nrf52832_peripherals.gpio_port[LED3_PIN]),
        LedLow::new(&nrf52832_peripherals.gpio_port[LED4_PIN]),
    ));

    //
    // Buttons
    //
    let button = components::button::ButtonComponent::new(
        board_kernel,
        capsules::button::DRIVER_NUM,
        components::button_component_helper!(
            nrf52832::gpio::GPIOPin,
            // 13
            (
                &nrf52832_peripherals.gpio_port[BUTTON1_PIN],
                hil::gpio::ActivationMode::ActiveLow,
                hil::gpio::FloatingState::PullUp
            ),
            // 14
            (
                &nrf52832_peripherals.gpio_port[BUTTON2_PIN],
                hil::gpio::ActivationMode::ActiveLow,
                hil::gpio::FloatingState::PullUp
            ),
            // 15
            (
                &nrf52832_peripherals.gpio_port[BUTTON3_PIN],
                hil::gpio::ActivationMode::ActiveLow,
                hil::gpio::FloatingState::PullUp
            ),
            // 16
            (
                &nrf52832_peripherals.gpio_port[BUTTON4_PIN],
                hil::gpio::ActivationMode::ActiveLow,
                hil::gpio::FloatingState::PullUp
            )
        ),
    )
    .finalize(components::button_component_buf!(nrf52832::gpio::GPIOPin));

    //
    // RTC for Timers
    //
    let rtc = &base_peripherals.rtc;
    let _ = rtc.start();
    let mux_alarm = static_init!(
        capsules::virtual_alarm::MuxAlarm<'static, nrf52832::rtc::Rtc>,
        capsules::virtual_alarm::MuxAlarm::new(&base_peripherals.rtc)
    );
    rtc.set_alarm_client(mux_alarm);

    //
    // Timer/Alarm
    //

    // Virtual alarm for the userspace timers
    let alarm_driver_virtual_alarm = static_init!(
        capsules::virtual_alarm::VirtualMuxAlarm<'static, nrf52832::rtc::Rtc>,
        capsules::virtual_alarm::VirtualMuxAlarm::new(mux_alarm)
    );
    alarm_driver_virtual_alarm.setup();

    // Userspace timer driver
    let alarm = static_init!(
        capsules::alarm::AlarmDriver<
            'static,
            capsules::virtual_alarm::VirtualMuxAlarm<'static, nrf52832::rtc::Rtc>,
        >,
        capsules::alarm::AlarmDriver::new(
            alarm_driver_virtual_alarm,
            board_kernel.create_grant(capsules::alarm::DRIVER_NUM, &memory_allocation_capability)
        )
    );
    alarm_driver_virtual_alarm.set_alarm_client(alarm);

    //
    // RTT and Console and `debug!()`
    //

    // RTT communication channel
    let rtt_memory = components::segger_rtt::SeggerRttMemoryComponent::new().finalize(());
    let rtt = components::segger_rtt::SeggerRttComponent::new(mux_alarm, rtt_memory)
        .finalize(components::segger_rtt_component_helper!(nrf52832::rtc::Rtc));

    //
    // Virtual UART
    //

    // Create a shared UART channel for the console and for kernel debug.
    let uart_mux = components::console::UartMuxComponent::new(rtt, 115200, dynamic_deferred_caller)
        .finalize(());

    // Setup the console.
    let console = components::console::ConsoleComponent::new(
        board_kernel,
        capsules::console::DRIVER_NUM,
        uart_mux,
    )
    .finalize(components::console_component_helper!());
    // Create the debugger object that handles calls to `debug!()`.
    components::debug_writer::DebugWriterComponent::new(uart_mux).finalize(());

    //
    // I2C Devices
    //

    // Create shared mux for the I2C bus
    let i2c_mux = static_init!(
        capsules::virtual_i2c::MuxI2C<'static>,
        capsules::virtual_i2c::MuxI2C::new(&base_peripherals.twi0, None, dynamic_deferred_caller)
    );
    base_peripherals.twi0.configure(
        nrf52832::pinmux::Pinmux::new(21),
        nrf52832::pinmux::Pinmux::new(20),
    );
    base_peripherals.twi0.set_master_client(i2c_mux);

    // Configure the MCP23017. Device address 0x20.
    let mcp_pin0 = static_init!(
        hil::gpio::InterruptValueWrapper<'static, nrf52832::gpio::GPIOPin>,
        hil::gpio::InterruptValueWrapper::new(&nrf52832_peripherals.gpio_port[Pin::P0_11])
    )
    .finalize();
    let mcp_pin1 = static_init!(
        hil::gpio::InterruptValueWrapper<'static, nrf52832::gpio::GPIOPin>,
        hil::gpio::InterruptValueWrapper::new(&nrf52832_peripherals.gpio_port[Pin::P0_12])
    )
    .finalize();
    let mcp23017_i2c = static_init!(
        capsules::virtual_i2c::I2CDevice,
        capsules::virtual_i2c::I2CDevice::new(i2c_mux, 0x40)
    );
    let mcp23017 = static_init!(
        capsules::mcp230xx::MCP230xx<'static>,
        capsules::mcp230xx::MCP230xx::new(
            mcp23017_i2c,
            Some(mcp_pin0),
            Some(mcp_pin1),
            &mut capsules::mcp230xx::BUFFER,
            8,
            2
        )
    );
    mcp23017_i2c.set_client(mcp23017);
    mcp_pin0.set_client(mcp23017);
    mcp_pin1.set_client(mcp23017);

    //
    // GPIO Extenders
    //

    // Create an array of the GPIO extenders so we can pass them to an
    // administrative layer that provides a single interface to them all.
    let async_gpio_ports = static_init!([&'static capsules::mcp230xx::MCP230xx; 1], [mcp23017]);

    // `gpio_async` is the object that manages all of the extenders.
    let gpio_async = static_init!(
        capsules::gpio_async::GPIOAsync<'static, capsules::mcp230xx::MCP230xx<'static>>,
        capsules::gpio_async::GPIOAsync::new(
            async_gpio_ports,
            board_kernel.create_grant(
                capsules::gpio_async::DRIVER_NUM,
                &memory_allocation_capability,
            ),
        ),
    );
    // Setup the clients correctly.
    for port in async_gpio_ports.iter() {
        port.set_client(gpio_async);
    }

    //
    // BLE
    //

    let ble_radio = BLEComponent::new(
        board_kernel,
        capsules::ble_advertising_driver::DRIVER_NUM,
        &base_peripherals.ble_radio,
        mux_alarm,
    )
    .finalize(());

    //
    // Temperature
    //

    // Setup internal temperature sensor
    let temp = static_init!(
        capsules::temperature::TemperatureSensor<'static>,
        capsules::temperature::TemperatureSensor::new(
            &base_peripherals.temp,
            board_kernel.create_grant(
                capsules::temperature::DRIVER_NUM,
                &memory_allocation_capability
            )
        )
    );
    kernel::hil::sensors::TemperatureDriver::set_client(&base_peripherals.temp, temp);

    //
    // RNG
    //

    // Convert hardware RNG to the Random interface.
    let entropy_to_random = static_init!(
        capsules::rng::Entropy32ToRandom<'static>,
        capsules::rng::Entropy32ToRandom::new(&base_peripherals.trng)
    );
    base_peripherals.trng.set_client(entropy_to_random);

    // Setup RNG for userspace
    let rng = static_init!(
        capsules::rng::RngDriver<'static>,
        capsules::rng::RngDriver::new(
            entropy_to_random,
            board_kernel.create_grant(capsules::rng::DRIVER_NUM, &memory_allocation_capability)
        )
    );
    entropy_to_random.set_client(rng);

    //
    // Light Sensor
    //

    // Setup Analog Light Sensor
    let analog_light_channel = static_init!(
        nrf52832::adc::AdcChannelSetup,
        nrf52832::adc::AdcChannelSetup::new(nrf52832::adc::AdcChannel::AnalogInput5)
    );

    let analog_light_sensor = static_init!(
        capsules::analog_sensor::AnalogLightSensor<'static, nrf52832::adc::Adc>,
        capsules::analog_sensor::AnalogLightSensor::new(
            &base_peripherals.adc,
            analog_light_channel,
            capsules::analog_sensor::AnalogLightSensorType::LightDependentResistor,
        )
    );
    base_peripherals.adc.set_client(analog_light_sensor);

    // Create userland driver for ambient light sensor
    let light = static_init!(
        capsules::ambient_light::AmbientLight<'static>,
        capsules::ambient_light::AmbientLight::new(
            analog_light_sensor,
            board_kernel.create_grant(
                capsules::ambient_light::DRIVER_NUM,
                &memory_allocation_capability
            )
        )
    );
    hil::sensors::AmbientLight::set_client(analog_light_sensor, light);

    //
    // PWM
    //
    let mux_pwm = static_init!(
        capsules::virtual_pwm::MuxPwm<'static, nrf52832::pwm::Pwm>,
        capsules::virtual_pwm::MuxPwm::new(&base_peripherals.pwm0)
    );
    let virtual_pwm_buzzer = static_init!(
        capsules::virtual_pwm::PwmPinUser<'static, nrf52832::pwm::Pwm>,
        capsules::virtual_pwm::PwmPinUser::new(mux_pwm, nrf52832::pinmux::Pinmux::new(31))
    );
    virtual_pwm_buzzer.add_to_mux();

    //
    // Buzzer
    //
    let virtual_alarm_buzzer = static_init!(
        capsules::virtual_alarm::VirtualMuxAlarm<'static, nrf52832::rtc::Rtc>,
        capsules::virtual_alarm::VirtualMuxAlarm::new(mux_alarm)
    );
    virtual_alarm_buzzer.setup();

    let buzzer = static_init!(
        capsules::buzzer_driver::Buzzer<
            'static,
            capsules::virtual_alarm::VirtualMuxAlarm<'static, nrf52832::rtc::Rtc>,
        >,
        capsules::buzzer_driver::Buzzer::new(
            virtual_pwm_buzzer,
            virtual_alarm_buzzer,
            capsules::buzzer_driver::DEFAULT_MAX_BUZZ_TIME_MS,
            board_kernel.create_grant(
                capsules::buzzer_driver::DRIVER_NUM,
                &memory_allocation_capability
            )
        )
    );
    virtual_alarm_buzzer.set_alarm_client(buzzer);

    // Start all of the clocks. Low power operation will require a better
    // approach than this.
    base_peripherals.clock.low_stop();
    base_peripherals.clock.high_stop();

    base_peripherals
        .clock
        .low_set_source(nrf52832::clock::LowClockSource::XTAL);
    base_peripherals.clock.low_start();
    base_peripherals.clock.high_start();
    while !base_peripherals.clock.low_started() {}
    while !base_peripherals.clock.high_started() {}

    let scheduler = components::sched::round_robin::RoundRobinComponent::new(&PROCESSES)
        .finalize(components::rr_component_helper!(NUM_PROCS));

    let platform = Platform {
        button: button,
        ble_radio: ble_radio,
        console: console,
        led: led,
        gpio: gpio,
        rng: rng,
        temp: temp,
        alarm: alarm,
        gpio_async: gpio_async,
        light: light,
        buzzer: buzzer,
        ipc: kernel::ipc::IPC::new(
            board_kernel,
            kernel::ipc::DRIVER_NUM,
            &memory_allocation_capability,
        ),
        scheduler,
        systick: cortexm4::systick::SysTick::new_with_calibration(64000000),
    };

    let chip = static_init!(
        nrf52832::chip::NRF52<Nrf52832DefaultPeripherals>,
        nrf52832::chip::NRF52::new(nrf52832_peripherals)
    );

    nrf52832_peripherals.gpio_port[Pin::P0_31].make_output();
    nrf52832_peripherals.gpio_port[Pin::P0_31].clear();

    debug!("Initialization complete. Entering main loop\r");
    debug!("{}", &nrf52832::ficr::FICR_INSTANCE);

    // These symbols are defined in the linker script.
    extern "C" {
        /// Beginning of the ROM region containing app images.
        static _sapps: u8;
        /// End of the ROM region containing app images.
        static _eapps: u8;
        /// Beginning of the RAM region for app memory.
        static mut _sappmem: u8;
        /// End of the RAM region for app memory.
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

    board_kernel.kernel_loop(&platform, chip, Some(&platform.ipc), &main_loop_capability);
}
