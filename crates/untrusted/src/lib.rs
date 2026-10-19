//! Safe, verified parsing of untrusted inputs.
//!
//! The functional behaviour of this crate is extracted to Lean with
//! [Aeneas](https://github.com/AeneasVerif/aeneas) and proved correct in
//! `proofs/`.
//!
//! # Verified, not zero-copy
//!
//! Correctness takes priority over ergonomics and performance. Every function
//! is proved never to panic and to return exactly what its specification
//! says. The cost is that values produced by [`Parse`] own their data and
//! cannot borrow from the input: tying a parsed value's lifetime to the input
//! is beyond what Aeneas can currently translate. If you need zero-copy
//! parsing and can do without formal verification, a crate such as `nom`
//! is a better fit.

#![no_std]

mod bytes;
mod int;
mod reader;

pub use bytes::{BigEndian, FixedLen, LittleEndian};
pub use reader::{Parse, Reader};

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
    /// A [`Reader`] was asked for more bytes than remain.
    EndOfInput,
    /// A [`Reader`] was finished with bytes left unread.
    TrailingData,
}
