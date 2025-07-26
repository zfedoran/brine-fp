#![cfg_attr(not(feature = "std"), no_std)]

// clippy suppressions
#![allow(clippy::assign_op_pattern)]
#![allow(clippy::ptr_offset_with_cast)]
#![allow(clippy::manual_range_contains)]
#![allow(clippy::reversed_empty_ranges)]

use uint::construct_uint;

#[cfg(feature = "256-bit")]
construct_uint! {
    pub struct InnerUint(4);
}

#[cfg(not(feature = "256-bit"))]
construct_uint! {
    pub struct InnerUint(3);
}

pub mod consts;
pub mod unsigned;
pub mod signed;
mod exp;
mod log;

pub use consts::*;
pub use unsigned::*;
pub use signed::*;
