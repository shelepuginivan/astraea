//! # libastraea
pub mod core;
pub mod math;
pub mod natural;
mod parse;

pub use core::{errors::*, instruction::*, module::*};
pub use math::digit::*;
pub use natural::number::*;
