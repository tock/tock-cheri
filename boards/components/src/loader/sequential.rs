// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2024.

//! Component for creating a sequential process loader.
//!
//! `ProcessLoaderSequentialComponent` uses the standard Tock assumptions about
//! where processes are stored in flash and what RAM is allocated for process
//! use.

use core::mem::MaybeUninit;
use kernel::component::Component;
use kernel::deferred_call::DeferredCallClient;
use kernel::platform::chip::Chip;
use kernel::process::ProcessLoadingAsync;

#[macro_export]
macro_rules! process_loader_sequential_component_static {
    ($C:ty, $NUMPROCS:expr $(,)?) => {{
        let loader = kernel::static_buf!(kernel::process::SequentialProcessLoaderMachine<
            $C,
        >);
        let process_binary_array = kernel::static_buf!(
            [Option<kernel::process::ProcessBinary>; $NUMPROCS]
        );

       (loader, process_binary_array)
    };};
}

pub type ProcessLoaderSequentialComponentType<C> =
    kernel::process::SequentialProcessLoaderMachine<'static, C>;

pub struct ProcessLoaderSequentialComponent<C: Chip + 'static, const NUM_PROCS: usize> {
    checker: &'static kernel::process::ProcessCheckerMachine,
    kernel: &'static kernel::Kernel,
    chip: &'static C,
    fault_policy: &'static dyn kernel::process::ProcessFaultPolicy,
    appid_policy: &'static dyn kernel::process_checker::AppIdPolicy,
    storage_policy: &'static dyn kernel::process::ProcessStandardStoragePermissionsPolicy<C>,
}

impl<C: Chip, const NUM_PROCS: usize> ProcessLoaderSequentialComponent<C, NUM_PROCS> {
    pub fn new(
        checker: &'static kernel::process::ProcessCheckerMachine,
        kernel: &'static kernel::Kernel,
        chip: &'static C,
        fault_policy: &'static dyn kernel::process::ProcessFaultPolicy,
        appid_policy: &'static dyn kernel::process_checker::AppIdPolicy,
        storage_policy: &'static dyn kernel::process::ProcessStandardStoragePermissionsPolicy<C>,
    ) -> Self {
        Self {
            checker,
            kernel,
            chip,
            fault_policy,
            appid_policy,
            storage_policy,
        }
    }
}

impl<C: Chip, const NUM_PROCS: usize> Component for ProcessLoaderSequentialComponent<C, NUM_PROCS> {
    type StaticInput = (
        &'static mut MaybeUninit<kernel::process::SequentialProcessLoaderMachine<'static, C>>,
        &'static mut MaybeUninit<[Option<kernel::process::ProcessBinary>; NUM_PROCS]>,
    );

    type Output = &'static kernel::process::SequentialProcessLoaderMachine<'static, C>;

    fn finalize(self, s: Self::StaticInput) -> Self::Output {
        let proc_manage_cap =
            kernel::create_capability!(kernel::capabilities::ProcessManagementCapability);

        const ARRAY_REPEAT_VALUE: Option<kernel::process::ProcessBinary> = None;
        let process_binary_array = s.1.write([ARRAY_REPEAT_VALUE; NUM_PROCS]);

        let (flash, ram) = unsafe { kernel::process_loading::get_mems() };

        let loader =
            s.0.write(kernel::process::SequentialProcessLoaderMachine::new(
                self.checker,
                process_binary_array,
                self.kernel,
                self.chip,
                flash,
                ram,
                self.fault_policy,
                self.storage_policy,
                self.appid_policy,
                &proc_manage_cap,
            ));

        self.checker.set_client(loader);
        loader.register();
        loader.start();
        loader
    }
}
