use std::fmt::Debug;
use std::str::FromStr;

/// The base trait for all mathematical objects in the system.
///
/// This trait serves as a marker for types that represent mathematical entities, requiring cloning
/// and parsing capabilities.
pub trait MathObject: Sized + Clone + FromStr<Err: Debug> {}
