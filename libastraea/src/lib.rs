//! # libastraea
pub mod core;
pub mod natural;

pub use core::{errors::*, instruction::*, module::*};
pub use natural::{digit::*, number::*};
