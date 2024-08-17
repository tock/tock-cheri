// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2023.

#![forbid(unsafe_code)]
#![cfg_attr(
    all(target_feature = "xcheri", feature = "use_static_init"),
    feature(const_refs_to_cell),
    feature(const_trait_impl),
    feature(macro_metavar_expr),
    feature(const_mut_refs),
    feature(const_precise_live_drops)
)]
#![cfg_attr(target_feature = "xcheri", feature(result_option_inspect))]
#![no_std]

pub mod test;

#[macro_use]
pub mod stream;

pub mod adc;
pub mod alarm;
pub mod button;
pub mod console;
pub mod console_ordered;
pub mod console_zero;
pub mod driver;
pub mod gpio;
pub mod i2c_master;
pub mod i2c_master_slave_combo;
pub mod i2c_master_slave_driver;
pub mod led;
pub mod low_level_debug;
pub mod process_console;
pub mod rng;
pub mod spi_controller;
pub mod spi_peripheral;
pub mod virtualizers;
