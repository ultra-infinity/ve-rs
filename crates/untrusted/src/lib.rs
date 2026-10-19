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
//! says. The cost is that values produced by [`Decode`] own their data and
//! cannot borrow from the input: tying a decoded value's lifetime to the input
//! is beyond what Aeneas can currently translate. If you need zero-copy
//! parsing and can do without formal verification, a crate such as `nom`
//! is a better fit.
//!
//! # Deriving `Decode`
//!
//! `#[derive(Decode)]` decodes a struct's fields one after another, in
//! declaration order. Every field type must implement [`Decode`]:
//!
//! ```
//! use untrusted::{BigEndian, Decode, Untrusted, ValidationError};
//!
//! #[derive(Decode, Debug, PartialEq)]
//! struct Header {
//!     version: BigEndian<u8>,
//!     len: BigEndian<u16>,
//! }
//!
//! assert_eq!(
//!     Untrusted::new(&[1, 0, 2][..]).read_all::<Header>(),
//!     Ok(Header { version: BigEndian(1), len: BigEndian(2) })
//! );
//! assert_eq!(
//!     Untrusted::new(&[1, 0, 2, 3][..]).read_all::<Header>(),
//!     Err(ValidationError::TrailingData)
//! );
//! ```
//!
//! The macro itself is not trusted. Run `cargo untrusted verify -p <your-crate>`
//! (from `crates/cargo-untrusted`) and every derived impl is extracted to Lean
//! and proved to decode exactly its fields, in declaration order.
//!
//! Enums, unions and generic structs are rejected:
//!
//! ```compile_fail
//! #[derive(untrusted::Decode)]
//! enum Kind { A, B }
//! ```
//!
//! ```compile_fail
//! #[derive(untrusted::Decode)]
//! struct Wrapper<T> { inner: T }
//! ```

#![no_std]

mod bytes;
mod int;
mod reader;

pub use bytes::{BigEndian, FixedLen, LittleEndian};
pub use reader::{Decode, Reader};
pub use untrusted_derive::Decode;

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
