//! Safe, verified parsing of untrusted inputs.
//!
//! The functional behaviour of this crate is extracted to Lean with
//! [Aeneas](https://github.com/AeneasVerif/aeneas) and proved correct in
//! `proofs/`.

#![no_std]

mod bytes;
mod int;

pub use bytes::{BigEndian, LittleEndian};

/// A value that came from an untrusted source.
///
/// The wrapped value can only be extracted by validating it into a type that
/// implements [`Validate`].
#[repr(transparent)]
pub struct Untrusted<T>(T);

impl<T> Untrusted<T> {
    pub fn new(inner: T) -> Self {
        Untrusted(inner)
    }

    /// Consumes the untrusted value, validating it as a `U`.
    pub fn validate<U: Validate<T>>(self) -> Result<U, U::Err> {
        U::validate(self.0)
    }
}

/// Fallible construction of `Self` from an untrusted `Input`.
pub trait Validate<Input>: Sized {
    type Err;
    fn validate(input: Input) -> Result<Self, Self::Err>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValidationError {
    /// The input did not have the exact number of bytes the target requires.
    LengthMismatch { expected: usize, actual: usize },
    /// The input value is not representable in the target type.
    OutOfRange,
}
