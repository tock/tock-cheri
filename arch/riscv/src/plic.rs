//! Platform Level Interrupt Control peripheral driver.

// TODO I found several copies of this. Hopefully this can become canonical,
// I have written it to be a superset.

use crate::csr;
use core::cell::Cell;
use kernel::utilities::registers::ReadWrite;
use kernel::utilities::StaticRef;
use kernel::very_simple_component;
use tock_registers::fields::FieldValue;
use tock_registers::interfaces::{ReadWriteable, Readable, Writeable};
use tock_registers::{register_bitfields, register_structs};

// Can actually be fewer, we don't use priorities for anything.
pub const N_PRIO_BITS: u32 = 3;

register_structs! {
    pub PlicRegisters<const N_IRQS : usize, const PLIC_REGS: usize> test_defaults<1,1> {
        /// Interrupt Priority Registers
        (0x000 => pad priority: [ReadWrite<u32, priority::Register>; N_IRQS]),
        /// Interrupt Pending Register
        (0x1000 => pad pending: [ReadWrite<u32>; PLIC_REGS]),
        /// Interrupt Enable Register
        (0x2000 => pad enable: [ReadWrite<u32>; PLIC_REGS]),
        /// Priority Threshold Register
        (0x200000 => threshold: ReadWrite<u32, priority::Register>),
        /// Claim/Complete Register
        (0x200004 => claim: ReadWrite<u32>),
        (0x200008 => _reserved3),
        /// MSIP Register
        (0x4000000 => msip: ReadWrite<u32>),
        (0x4000004 => _reserved4),
        (0x4004000 => alert_test: ReadWrite<u32>),
        (0x4004004 => @END),
    }
}

register_bitfields![u32,
    priority [
        Priority OFFSET(0) NUMBITS(crate::plic::N_PRIO_BITS) []
    ]
];

// 32 IRQs per register (need to round up)
pub struct Plic<const N_IRQS: usize, const PLIC_REGS: usize> {
    registers: StaticRef<PlicRegisters<N_IRQS, PLIC_REGS>>,
    pending: Cell<bool>,
}

pub const fn plic_regs_for_n_irqs(n_irqs: usize) -> usize {
    (n_irqs + 31) / 32
}

impl<const N_IRQS: usize, const PLIC_REGS: usize> Plic<N_IRQS, PLIC_REGS> {
    pub const fn new(base: StaticRef<PlicRegisters<N_IRQS, PLIC_REGS>>) -> Self {
        Plic {
            registers: base,
            pending: Cell::new(false),
        }
    }

    pub fn split_index(index: u32) -> (usize, u32) {
        let res = ((index / 32) as usize, index % 32);
        if res.0 >= PLIC_REGS {
            panic!("Invalid IRQ: {}", index);
        }
        res
    }

    /// Clear all pending interrupts.
    pub fn clear_all_pending(&self) {
        for pending in self.registers.pending.iter() {
            pending.set(0);
        }
    }

    /// Enable all interrupts.
    pub fn enable_all(&self) {
        for enable in self.registers.enable.iter() {
            enable.set(0xFFFF_FFFF);
        }

        // Set some default priority for each interrupt. This is not really used
        // at this point. We set here the maximum value.
        for priority in self.registers.priority.iter() {
            priority.write(priority::Priority::SET);
        }

        // Accept all interrupts.
        self.registers.threshold.write(priority::Priority.val(0));
    }

    /// Disable all interrupts.
    pub fn disable_all(&self) {
        for enable in self.registers.enable.iter() {
            enable.set(0);
        }
    }

    /// Disable a specific interrupt
    pub fn disable_interrupt(&self, index: u32) {
        let (index, shift) = Self::split_index(index);
        self.registers.enable[index].modify(FieldValue::<u32, ()>::new(1, shift as usize, 0));
    }

    /// Save the current interrupt to be handled later
    /// Interrupts must be disabled before this is called.
    /// Saved interrupts can be retrieved by calling `get_saved_interrupts()`.
    /// Saved interrupts are cleared when `'complete()` is called.
    pub fn save_pending(&self) {
        self.pending.set(true)
    }

    pub fn has_pending(&self) -> bool {
        self.pending.get()
    }

    /// Get the next pending interrupt, if there are any
    pub fn get_saved_interrupts(&self) -> Option<u32> {
        let claim = self.registers.claim.get();
        if claim == 0 {
            self.pending.set(false);
            None
        } else {
            Some(claim)
        }
    }

    /// Mark the interrupt as handled (internally) without a signal to disable it
    pub unsafe fn disable_and_complete(&self, index: u32) {
        self.disable_interrupt(index);
        self.complete(index);
    }

    /// Signal that an interrupt is finished being handled. In Tock, this should be
    /// called from the normal main loop (not the interrupt handler).
    /// Interrupts must be disabled before this is called.
    pub unsafe fn complete(&self, index: u32) {
        self.registers.claim.set(index);
    }

    /// This is a generic implementation. There may be board specific versions as
    /// some platforms have added more bits to the `mtvec` register.
    pub fn suppress_all(&self) {
        // Accept all interrupts.
        self.registers.threshold.write(priority::Priority.val(0));
    }

    pub fn fin(&self, enable_interrupts: bool) {
        // Reset interrupts at PLIC level
        self.disable_all();
        self.clear_all_pending();
        self.enable_all();

        // Then enable interrupts globally if required
        if enable_interrupts {
            csr::CSR.mie.modify(
                csr::mie::mie::mext::SET + csr::mie::mie::msoft::SET + csr::mie::mie::mtimer::SET,
            );

            csr::CSR.mstatus.modify(csr::mstatus::mstatus::mie::SET);
        }
    }
}

very_simple_component!(impl<{const N_IRQS : usize, const PLIC_REGS : usize}> for Plic::<N_IRQS, PLIC_REGS>,
    new(StaticRef<PlicRegisters<N_IRQS, PLIC_REGS>>),
    fin(bool)
);
