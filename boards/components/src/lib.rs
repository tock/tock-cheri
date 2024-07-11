#![feature(const_trait_impl)]
#![feature(const_mut_refs)]
#![feature(const_slice_split_at_mut)]
#![feature(maybe_uninit_array_assume_init)]
#![feature(const_maybe_uninit_array_assume_init)]
#![feature(macro_metavar_expr)]
#![no_std]

pub mod adc;
pub mod adc_microphone;
pub mod air_quality;
pub mod alarm;
pub mod analog_comparator;
pub mod app_flash_driver;
pub mod bme280;
pub mod bmp280;
pub mod bus;
pub mod button;
pub mod ccs811;
pub mod cdc;
pub mod console;
pub mod crc;
pub mod ctap;
pub mod debug_queue;
pub mod debug_writer;
pub mod digest;
pub mod flash;
pub mod ft6x06;
pub mod fxos8700;
pub mod gpio;
pub mod hd44780;
pub mod hmac;
pub mod hts221;
pub mod humidity;
pub mod i2c;
pub mod ieee802154;
pub mod isl29035;
pub mod kv_system;
pub mod l3gd20;
pub mod led;
pub mod led_matrix;
pub mod lldb;
pub mod lpm013m126;
pub mod lsm303agr;
pub mod lsm303dlhc;
pub mod lsm6dsox;
pub mod mlx90614;
pub mod mx25r6435f;
pub mod ninedof;
pub mod nonvolatile_storage;
pub mod nrf51822;
pub mod panic_button;
pub mod process_console;
pub mod process_printer;
pub mod rng;
pub mod sched;
pub mod screen;
pub mod segger_rtt;
pub mod sha;
pub mod sht3x;
pub mod si7021;
pub mod sound_pressure;
pub mod spi;
pub mod st77xx;
pub mod temperature;
pub mod temperature_rp2040;
pub mod temperature_stm;
pub mod test;
pub mod text_screen;
pub mod tickv;
pub mod touch;
pub mod udp_driver;
pub mod udp_mux;
