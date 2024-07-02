use kernel::utilities::registers::{register_bitfields, LocalRegisterCopy};

register_bitfields![usize,
    pub mcause [
        is_interrupt OFFSET(crate::XLEN - 1) NUMBITS(1) [],
        reason OFFSET(0) NUMBITS(crate::XLEN - 1) []
    ],
    // Although the base spec only defines the first 4 bits, some patterns in the first 6 bits
    // are designated for custom use so we should include them here.
    // I don't like the truncation here and as nothing is actually checking that reserved is 0
    // and this can lead to weird errors.
    reason [
        reserved OFFSET(6) NUMBITS(crate::XLEN - 7) [],
        std OFFSET(0) NUMBITS(6) []
    ]
];

/// Trap Cause
#[derive(Copy, Clone, Debug)]
pub enum Trap {
    Interrupt(Interrupt),
    Exception(Exception),
}

impl From<LocalRegisterCopy<usize, mcause::Register>> for Trap {
    fn from(val: LocalRegisterCopy<usize, mcause::Register>) -> Self {
        if val.is_set(mcause::is_interrupt) {
            Trap::Interrupt(Interrupt::from_reason(val.read(mcause::reason)))
        } else {
            Trap::Exception(Exception::from_reason(val.read(mcause::reason)))
        }
    }
}

impl From<usize> for Trap {
    fn from(csr_val: usize) -> Self {
        Self::from(LocalRegisterCopy::<usize, mcause::Register>::new(csr_val))
    }
}

/// Interrupt
#[derive(Copy, Clone, Debug)]
pub enum Interrupt {
    UserSoft,
    SupervisorSoft,
    MachineSoft,
    UserTimer,
    SupervisorTimer,
    MachineTimer,
    UserExternal,
    SupervisorExternal,
    MachineExternal,
    Unknown,
}

/// Exception
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Exception {
    InstructionMisaligned,
    InstructionFault,
    IllegalInstruction,
    Breakpoint,
    LoadMisaligned,
    LoadFault,
    StoreMisaligned,
    StoreFault,
    UserEnvCall,
    SupervisorEnvCall,
    MachineEnvCall,
    InstructionPageFault,
    LoadPageFault,
    StorePageFault,
    #[cfg(target_feature = "xcheri")]
    CHERIPageException,
    #[cfg(target_feature = "xcheri")]
    CHERIException,
    Unknown,
}

impl Interrupt {
    fn from_reason(val: usize) -> Self {
        let reason = LocalRegisterCopy::<usize, reason::Register>::new(val);
        match reason.read(reason::std) {
            0 => Interrupt::UserSoft,
            1 => Interrupt::SupervisorSoft,
            3 => Interrupt::MachineSoft,
            4 => Interrupt::UserTimer,
            5 => Interrupt::SupervisorTimer,
            7 => Interrupt::MachineTimer,
            8 => Interrupt::UserExternal,
            9 => Interrupt::SupervisorExternal,
            11 => Interrupt::MachineExternal,
            _ => Interrupt::Unknown,
        }
    }
}

impl Exception {
    fn from_reason(val: usize) -> Self {
        let reason = LocalRegisterCopy::<usize, reason::Register>::new(val);
        match reason.read(reason::std) {
            0 => Exception::InstructionMisaligned,
            1 => Exception::InstructionFault,
            2 => Exception::IllegalInstruction,
            3 => Exception::Breakpoint,
            4 => Exception::LoadMisaligned,
            5 => Exception::LoadFault,
            6 => Exception::StoreMisaligned,
            7 => Exception::StoreFault,
            8 => Exception::UserEnvCall,
            9 => Exception::SupervisorEnvCall,
            11 => Exception::MachineEnvCall,
            12 => Exception::InstructionPageFault,
            13 => Exception::LoadPageFault,
            15 => Exception::StorePageFault,
            #[cfg(target_feature = "xcheri")]
            0x1b => Exception::CHERIPageException,
            #[cfg(target_feature = "xcheri")]
            0x1c => Exception::CHERIException,
            _ => Exception::Unknown,
        }
    }
}
