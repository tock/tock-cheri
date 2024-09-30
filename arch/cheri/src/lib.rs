//! Generalised support for CHERI architectures

#![no_std]
#![feature(const_trait_impl, const_mut_refs, const_slice_split_at_mut)]
#![feature(macro_metavar_expr)]

pub mod cheri_mpu;
