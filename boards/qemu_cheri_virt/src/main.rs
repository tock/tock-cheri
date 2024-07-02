//! Board file for qemu CHERI virt board

#![no_std]
#![feature(macro_metavar_expr, const_mut_refs, const_trait_impl)]
#![cfg_attr(not(doc), no_main)]

use capsules::{
    console_zero::{self, Console},
    virtual_alarm::VirtualMuxAlarm,
    virtual_uart_zero::mux3,
    virtual_uart_zero::mux3::UartMuxComponent,
};
use cheri::cheri_mpu::CheriMPU;
use components::{
    alarm::{AlarmDriverComponent, AlarmMuxComponent, VirtualSchedulerTimerComponent},
    debug_writer::LegacyDebugWriterComponent,
    sched::round_robin::StaticRoundRobinComponent,
};
use core::fmt::Write;
use core::panic::PanicInfo;
use kernel::{
    capabilities, create_capability, create_static_capability, debug,
    debug::IoWrite,
    dynamic_deferred_call::ProtoDynamicDeferredCallSized,
    hil::{uart, uart::LegacyTransmitComponent, uart::ZeroTransmitLegacyWrapper},
    platform::chip::Chip,
    platform::chip::InterruptService,
    platform::scheduler_timer::VirtualSchedulerTimer,
    platform::KernelResources,
    process::ProcessPrinterText,
    scheduler::round_robin::RoundRobinSched,
    utilities::singleton_checker::SingletonChecker,
    utilities::StaticRef,
    Kernel, ProtoKernel,
};
use misc::const_env_int;
use riscv::plic::Plic;
use riscv::plic::PlicRegisters;
use uarts::ns16550::UartRegisters;
use uarts::ns16550::ZeroUartComponent;

// Config
const_env_int!(PLIC_BASE_ADDR: usize);
const_env_int!(pub NUM_PROCS : usize);
const_env_int!(UART0_BASE_ADDR: usize);
const_env_int!(BAUD_RATE: u32);
const_env_int!(STACK_SIZE: usize);
const_env_int!(pub UART0_IRQ : u32);

static mut PROCESSES: kernel::ProcessArray<NUM_PROCS> = kernel::Kernel::init_process_array();

/// Placeholder buffer that causes the linker to reserve enough space for the stack.
#[no_mangle]
#[link_section = ".stack_buffer"]
pub static mut STACK_MEMORY: [u8; STACK_SIZE] = [0; STACK_SIZE];

// How should the kernel respond when a process faults.
const FAULT_RESPONSE: kernel::process::PanicFaultPolicy = kernel::process::PanicFaultPolicy {};

pub const UART0_BASE: StaticRef<UartRegisters> =
    unsafe { StaticRef::new(UART0_BASE_ADDR as *const UartRegisters) };
pub const PLIC_BASE: StaticRef<PlicRegisters<N_IRQS, PLIC_REGS>> =
    unsafe { StaticRef::new(PLIC_BASE_ADDR as *const PlicRegisters<N_IRQS, PLIC_REGS>) };

const N_IRQS: usize = 128;
const PLIC_REGS: usize = riscv::plic::plic_regs_for_n_irqs(N_IRQS);

const MAX_DEFERRED_CALLERS: usize = 2;

// TODO: Clint instead of no timer
type TimerComponant = kernel::component::NoComponent;
type Timer = ();

kernel::define_components!(structs Components, CState, CStateMut {
    // Core kernel things
    kernel : Kernel,
    mpu : CheriMPU,
    process_printer: ProcessPrinterText,
    scheduler : StaticRoundRobinComponent::<NUM_PROCS>,
    scheduler_timer : VirtualSchedulerTimerComponent::<Timer>,
    userspace_kernel_boundary: riscv::syscall::SysCall,
    timer : TimerComponant,
    // Alarms
    alarm_mux : AlarmMuxComponent<Timer>,
    alarm_capsule : AlarmDriverComponent<Timer>,
    // Printing things
    uart_and_console : ZeroUartComponent<kernel::hil::time::Freq1MHz, UartMuxComponent<
        console_zero::Buffer, // A buffer that works for all clients
        Console,
        components::lldb::LowLevelDebugZeroComponent,
        LegacyTransmitComponent<LegacyDebugWriterComponent>
    >>,
    // PLIC, also good to come pretty late as it will enable interrupts
    plic : Plic<N_IRQS, PLIC_REGS>,
    // Deferred calls. Construct last to make sure they have been registered.
    dyn_def : kernel::dynamic_deferred_call::DynamicDeferredCallComponent::<MAX_DEFERRED_CALLERS>,
});

/// Root structure
struct Platform {
    /// All components
    components: Components,
    /// Shared state
    state: CState,
    /// Owned state
    state_mut: CStateMut,
}

create_static_capability!(static PROC_MNG_CAP : MCap = capabilities::ProcessManagementCapability);

static mut BOARD: Platform = {
    // Safety: this is the only time in init we take the reference to the platform
    let slf = unsafe { &mut BOARD };

    // Safety: we never take mut references to processes
    let procs = unsafe { &PROCESSES };

    // Make reference to individual elements, we don't need the very top level one (and it would
    // alias with the mutable bit anyway)
    let c_state_mut = &mut slf.state_mut;
    let c_state = &slf.state;
    let componants = &slf.components;
    let board_kernel = &componants.kernel;

    // Safety: only one instance of this checker should be made. We do so only at top-level board
    // logic.
    let mut checker = unsafe { SingletonChecker::new_sized::<100>() };
    let chk = checker.as_unsized();

    // This builds the kernel object
    let (proto, counter) = ProtoKernel::new(chk);

    // This builds the dynamic deferred object
    let deferred = ProtoDynamicDeferredCallSized::<MAX_DEFERRED_CALLERS>::new();

    // Capabilities (that we only need for construction. those that get held are globals.)
    let memory_allocation_cap = create_capability!(capabilities::MemoryAllocationCapability);

    // Grants for capsules
    kernel::construct_grants!(board_kernel, proto, counter, &memory_allocation_cap, {
        alarm_grant : capsules::alarm::DRIVER_NUM,
        console_grant : capsules::console::DRIVER_NUM,
        lldb_grant : capsules::low_level_debug::DRIVER_NUM,
        cheri_grant : capsules::driver::NUM::MMU as usize,
    });

    // This gunk builds a non zero-copy bridge for the debug
    let bridge =
        ZeroTransmitLegacyWrapper::transmitter_as_legacy(mux3::c(&slf.components.uart_and_console));

    // Build all components
    construct_components!(
        let components, component_state, component_state_mut = &slf.components, c_state, c_state_mut,
        {
            (procs, counter), // kernel
            (cheri_grant, board_kernel, &PROC_MNG_CAP), // MPU,
            (), // printer
            procs, // sched
            &slf.components.alarm_mux, // sched_timer
            chk, // boundary
            (), // timer
            &slf.components.timer, // alarm mux
            (&slf.components.alarm_mux, alarm_grant), // alarm capsule
            ( // uart
                ( // mux
                    console_grant, // console
                    lldb_grant, // lldb
                    bridge, // debug
                    (), // mux
                ),
                UART0_BASE // uart
            ),
            PLIC_BASE, // PLIC
            (deferred, chk), // dynamic deferred calls
        }
    );

    Platform {
        components,
        state: component_state,
        state_mut: component_state_mut,
    }
};

#[no_mangle]
fn main() {
    // only machine mode
    unsafe {
        riscv::configure_trap_handler(riscv::PermissionMode::Machine);
    }

    // If we support a PMP, we must enable an entry, even if using another mechanism
    // This is because RISCV defines no entries to fail any mode but M-Mode.
    riscv::pmp::pmp_permit_all();

    let components = unsafe { &BOARD.components };
    let state = unsafe { &BOARD.state };
    let board_kernel = &components.kernel;

    // initialize capabilities
    let process_mgmt_cap = create_capability!(capabilities::ProcessManagementCapability);
    let main_loop_cap = create_capability!(capabilities::MainLoopCapability);

    finalize_components!(components, state, {
        (), // kernel
        (), // mpu,
        (), // process printer
        (), // sched
        (), // sched_timer
        (), // boundary
        (), // timer,
        &components.timer, // alarm mux
        (), // alarm capsule
        ( // uart+clients
            (
                (), // console
                (), // lldb
                (), // debug
                (), // mux
            ),
            uart::Parameters { // uart
                baud_rate: BAUD_RATE,
                width: uart::Width::Eight,
                stop_bits: uart::StopBits::One,
                parity: uart::Parity::None,
                hw_flow_control: false,
            },
        ),
        true, // plic,
        (), // dyn_def
    });

    debug!("CHERI platform initialization complete.");

    let (flash, mem) = unsafe { kernel::process::get_mems() };

    let _ = kernel::process::load_processes_advanced(
        board_kernel,
        components,
        flash,
        mem,
        &FAULT_RESPONSE,
        true,
        &process_mgmt_cap,
    )
    .unwrap_or_else(|err| {
        debug!("Error loading processes!");
        debug!("{:?}", err);
        None
    });

    debug!("Entering main loop.");
    board_kernel.kernel_loop::<_, _, { NUM_PROCS as u8 }>(
        components,
        components,
        None,
        &main_loop_cap,
    );
}

impl kernel::platform::SyscallDriverLookup for Components {
    fn with_driver<F, R>(&self, driver_num: usize, f: F) -> R
    where
        F: FnOnce(Option<&dyn kernel::syscall::SyscallDriver>) -> R,
    {
        use capsules::low_level_debug::LowLevelDebugZero;
        const MMU_NUM: usize = capsules::driver::NUM::MMU as usize;
        f(match driver_num {
            capsules::console::DRIVER_NUM => {
                Some(Console::get_syscall_driver(mux3::a(&self.uart_and_console)))
            }
            capsules::alarm::DRIVER_NUM => Some(&self.alarm_capsule),
            capsules::low_level_debug::DRIVER_NUM => Some(LowLevelDebugZero::get_syscall_driver(
                mux3::b(&self.uart_and_console),
            )),
            MMU_NUM => Some(&self.mpu),
            _ => None,
        })
    }
}

impl kernel::platform::chip::InterruptService<()> for Components {
    unsafe fn service_interrupt(&self, interrupt: u32) -> bool {
        match interrupt {
            UART0_IRQ => self.uart_and_console.handle_interrupt(),
            _ => return false,
        }
        true
    }

    unsafe fn service_deferred_call(&self, _: ()) -> bool {
        false
    }
}

use kernel::utilities::registers::interfaces::{ReadWriteable, Readable};
use riscv::csr::mie::mie;
use riscv::csr::{mcause, CSR};

impl KernelResources<Components> for Components {
    type SyscallDriverLookup = Self;
    type SyscallFilter = ();
    type ProcessFault = ();
    type Scheduler = RoundRobinSched<'static>;
    type SchedulerTimer = VirtualSchedulerTimer<VirtualMuxAlarm<'static, Timer>>;
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
        self.scheduler.get_sched()
    }
    fn scheduler_timer(&self) -> &Self::SchedulerTimer {
        &self.scheduler_timer
    }
    fn watchdog(&self) -> &Self::WatchDog {
        &()
    }
    fn context_switch_callback(&self) -> &Self::ContextSwitchCallback {
        &()
    }
}

impl Chip for Components {
    type MPU = CheriMPU;

    type UserspaceKernelBoundary = riscv::syscall::SysCall;

    fn service_pending_interrupts(&self) {
        use riscv::csr::mip::mip;

        while self.has_pending_interrupts() {
            let mip = CSR.mip.extract();

            if mip.is_set(mip::mtimer) {
                //self.timer.handle_interrupt();
            }

            if self.plic.has_pending() {
                unsafe {
                    let mut ctr = 0;
                    while let Some(interrupt) = self.plic.get_saved_interrupts() {
                        ctr += 1;
                        if ctr == 100 {
                            debug!("WARN: Interrupt storm detected. Possibly one of your devices is not acking interrupts properly");
                        }
                        if !self.service_interrupt(interrupt) {
                            debug!("Unexpected IRQ: {}", interrupt);
                            self.plic.disable_and_complete(interrupt);
                        } else {
                            self.atomic(|| {
                                self.plic.complete(interrupt);
                            });
                        }
                    }
                }
            }
        }

        // Re-enable all MIE interrupts that we care about. Since we looped
        // until we handled them all, we can re-enable all of them.
        CSR.mie.modify(mie::mext::SET + mie::mtimer::SET);
    }

    fn has_pending_interrupts(&self) -> bool {
        use riscv::csr::mip::mip;
        // First check if the global machine timer interrupt is set.
        // We would also need to check for additional global interrupt bits
        // if there were to be used for anything in the future.

        if CSR.mip.is_set(mip::mtimer) {
            return true;
        }

        // Then we can check the PLIC.
        self.plic.has_pending()
    }

    fn mpu(&self) -> &Self::MPU {
        &self.mpu
    }

    fn userspace_kernel_boundary(&self) -> &riscv::syscall::SysCall {
        &self.userspace_kernel_boundary
    }

    fn sleep(&self) {
        unsafe {
            riscv::support::wfi();
        }
    }

    unsafe fn atomic<F, R>(&self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        riscv::support::atomic(f)
    }

    unsafe fn print_state(&self, writer: &mut dyn Write) {
        unsafe {
            riscv::print_riscv_state(writer);
        }
    }
}

struct Writer {}

static mut WRITER: Writer = Writer {};

impl Write for Writer {
    fn write_str(&mut self, s: &str) -> ::core::fmt::Result {
        self.write(s.as_bytes());
        Ok(())
    }
}

impl IoWrite for Writer {
    fn write(&mut self, buf: &[u8]) {
        let uart = unsafe { &BOARD.components.uart_and_console };
        uart.transmit_sync(buf);
    }
}

pub fn panic_reset() -> ! {
    #[allow(dead_code)]
    pub enum SifiveShutdownStatus {
        FinisherFail = 0x3333,
        FinisherPass = 0x5555,
        FinisherReset = 0x7777,
    }

    pub fn reset_sifive(status: SifiveShutdownStatus, code: u16) -> ! {
        unsafe {
            let val: u32 = (status as u32) | ((code as u32) << 16);
            let reset_ptr: *mut u32 = 0x100000 as *mut u32;
            *reset_ptr = val;

            loop {
                riscv::support::wfi()
            }
        }
    }

    reset_sifive(SifiveShutdownStatus::FinisherFail, 1)
}

/// Panic handler.
#[cfg(not(test))]
#[no_mangle]
#[panic_handler]
pub unsafe extern "C" fn panic_fmt(pi: &PanicInfo) -> ! {
    let writer = &mut WRITER;

    debug::panic_print_2(
        writer,
        pi,
        &riscv::support::nop,
        &PROCESSES,
        Some(&BOARD.components),
        Some(&BOARD.components.process_printer),
    );

    panic_reset()
}

fn handle_exception(exception: mcause::Exception) {
    match exception {
        mcause::Exception::UserEnvCall | mcause::Exception::SupervisorEnvCall => (),
        _ => {
            panic!("fatal exception {}", exception as u32);
        }
    }
}

unsafe fn handle_interrupt(intr: mcause::Interrupt) {
    match intr {
        mcause::Interrupt::UserSoft
        | mcause::Interrupt::UserTimer
        | mcause::Interrupt::UserExternal => {
            panic!("unexpected user-mode interrupt");
        }
        mcause::Interrupt::SupervisorExternal
        | mcause::Interrupt::SupervisorTimer
        | mcause::Interrupt::SupervisorSoft => {
            panic!("unexpected supervisor-mode interrupt");
        }

        mcause::Interrupt::MachineSoft => {
            CSR.mie.modify(mie::msoft::CLEAR);
        }
        mcause::Interrupt::MachineTimer => {
            CSR.mie.modify(mie::mtimer::CLEAR);
        }
        mcause::Interrupt::MachineExternal => {
            // We received an interrupt, disable interrupts while we handle them
            CSR.mie.modify(mie::mext::CLEAR);

            // Set to handle later
            BOARD.components.plic.save_pending();
        }

        mcause::Interrupt::Unknown => {
            panic!("interrupt of unknown cause");
        }
    }
}

/// Trap handler for board/chip specific code.
///
#[export_name = "_start_trap_rust_from_kernel"]
pub unsafe extern "C" fn start_trap_rust() {
    match mcause::Trap::from(CSR.mcause.extract()) {
        mcause::Trap::Interrupt(interrupt) => {
            handle_interrupt(interrupt);
        }
        mcause::Trap::Exception(exception) => {
            handle_exception(exception);
        }
    }
}

/// Function that gets called if an interrupt occurs while an app was running.
/// mcause is passed in, and this function should correctly handle disabling the
/// interrupt that fired so that it does not trigger again.
#[export_name = "_disable_interrupt_trap_rust_from_app"]
pub unsafe extern "C" fn disable_interrupt_trap_handler(mcause_val: usize) {
    match mcause::Trap::from(mcause_val as usize) {
        mcause::Trap::Interrupt(interrupt) => {
            handle_interrupt(interrupt);
        }
        _ => {
            panic!("unexpected non-interrupt mcause: {}", mcause_val);
        }
    }
}
