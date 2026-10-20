//! Fixed-width integers from byte slices.
//!
//! The input must be exactly as long as the target integer; there is no
//! implicit truncation or padding. `usize`/`isize` are deliberately not
//! supported since their width is platform dependent.

use crate::{Decode, Reader, Validate, ValidationError};

/// An integer decoded from big-endian (network order) bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BigEndian<T>(pub T);

/// An integer decoded from little-endian bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LittleEndian<T>(pub T);

impl<T> BigEndian<T> {
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> LittleEndian<T> {
    pub fn into_inner(self) -> T {
        self.0
    }
}

/// Types decoded from a fixed number of bytes.
pub trait FixedLen {
    /// The number of bytes in the encoding.
    const LEN: usize;
}

fn check_len(input: &[u8], expected: usize) -> Result<(), ValidationError> {
    if input.len() == expected {
        Ok(())
    } else {
        Err(ValidationError::LengthMismatch {
            expected,
            actual: input.len(),
        })
    }
}

/// Single-byte integers: byte order is irrelevant.
macro_rules! impl_byte {
    ($($t:ty),+) => {$(
        impl FixedLen for BigEndian<$t> {
            const LEN: usize = 1;
        }

        impl FixedLen for LittleEndian<$t> {
            const LEN: usize = 1;
        }

        impl<'a> Validate<&'a [u8]> for BigEndian<$t> {
            type Err = ValidationError;
            fn validate(input: &'a [u8]) -> Result<Self, Self::Err> {
                check_len(input, 1)?;
                Ok(BigEndian(input[0] as $t))
            }
        }

        impl<'a> Validate<&'a [u8]> for LittleEndian<$t> {
            type Err = ValidationError;
            fn validate(input: &'a [u8]) -> Result<Self, Self::Err> {
                check_len(input, 1)?;
                Ok(LittleEndian(input[0] as $t))
            }
        }
    )+};
}

/// Multi-byte integers `$t`, assembled in the unsigned type `$u` of the same
/// width (`$n` bytes) and then reinterpreted as `$t`.
///
/// Explicit shifts are used instead of `from_be_bytes`/`from_le_bytes` so that
/// Aeneas can translate the decoding.
macro_rules! impl_multi_byte {
    ($($t:ty, $u:ty, $n:expr;)+) => {$(
        impl FixedLen for BigEndian<$t> {
            const LEN: usize = $n;
        }

        impl FixedLen for LittleEndian<$t> {
            const LEN: usize = $n;
        }

        impl<'a> Validate<&'a [u8]> for BigEndian<$t> {
            type Err = ValidationError;
            fn validate(input: &'a [u8]) -> Result<Self, Self::Err> {
                check_len(input, $n)?;
                let mut acc: $u = 0;
                let mut i = 0;
                while i < $n {
                    acc = (acc << 8) | (input[i] as $u);
                    i += 1;
                }
                Ok(BigEndian(acc as $t))
            }
        }

        impl<'a> Validate<&'a [u8]> for LittleEndian<$t> {
            type Err = ValidationError;
            fn validate(input: &'a [u8]) -> Result<Self, Self::Err> {
                check_len(input, $n)?;
                let mut acc: $u = 0;
                let mut i = $n;
                while i > 0 {
                    i -= 1;
                    acc = (acc << 8) | (input[i] as $u);
                }
                Ok(LittleEndian(acc as $t))
            }
        }
    )+};
}

impl_byte!(u8, i8);

impl_multi_byte! {
    u16, u16, 2;
    u32, u32, 4;
    u64, u64, 8;
    u128, u128, 16;
    i16, u16, 2;
    i32, u32, 4;
    i64, u64, 8;
    i128, u128, 16;
}

/// Every fixed-width integer is also a [`Decode`] field, read with
/// [`Reader::read`], so derived decoders handle all fields uniformly.
/// (The parameter is not named `reader`: that would shadow the `reader`
/// namespace in the generated Lean.)
macro_rules! impl_decode {
    ($($t:ty),+) => {$(
        impl Decode for BigEndian<$t> {
            fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
                r.read::<Self>()
            }
        }

        impl Decode for LittleEndian<$t> {
            fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
                r.read::<Self>()
            }
        }
    )+};
}

impl_decode!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

/// Exactly `N` bytes, copied out of the input: a key, a nonce, a MAC. Fails
/// without consuming anything if fewer than `N` bytes remain.
impl<const N: usize> Decode for [u8; N] {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        if r.remaining() < N {
            return Err(ValidationError::EndOfInput);
        }
        let mut out = [0u8; N];
        let mut i = 0;
        while i < N {
            out[i] = r.read_byte()?;
            i += 1;
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_arrays() {
        use crate::Untrusted;
        assert_eq!(Untrusted::new(&[1, 2, 3][..]).read_all::<[u8; 3]>(), Ok([1, 2, 3]));
        assert_eq!(Untrusted::new(&[][..]).read_all::<[u8; 0]>(), Ok([]));
        assert_eq!(
            Untrusted::new(&[1, 2][..]).read_all::<[u8; 3]>(),
            Err(ValidationError::EndOfInput)
        );
        assert_eq!(
            Untrusted::new(&[1, 2, 3, 4][..]).read_all::<[u8; 3]>(),
            Err(ValidationError::TrailingData)
        );
    }

    #[test]
    fn big_endian() {
        let bytes = [0x12, 0x34, 0x56, 0x78];
        assert_eq!(
            BigEndian::<u32>::validate(&bytes),
            Ok(BigEndian(0x1234_5678))
        );
        assert_eq!(
            BigEndian::<u16>::validate(&bytes[..2]),
            Ok(BigEndian(0x1234))
        );
        assert_eq!(BigEndian::<i16>::validate(&[0xff, 0xfe]), Ok(BigEndian(-2)));
        assert_eq!(BigEndian::<i8>::validate(&[0x80]), Ok(BigEndian(i8::MIN)));
    }

    #[test]
    fn little_endian() {
        let bytes = [0x12, 0x34, 0x56, 0x78];
        assert_eq!(
            LittleEndian::<u32>::validate(&bytes),
            Ok(LittleEndian(0x7856_3412))
        );
        assert_eq!(
            LittleEndian::<i16>::validate(&[0xfe, 0xff]),
            Ok(LittleEndian(-2))
        );
    }

    /// Every decoder must agree with `core`'s `from_{be,le}_bytes`.
    #[test]
    fn matches_core() {
        let bytes: [u8; 16] = core::array::from_fn(|i| (i as u8).wrapping_mul(37) ^ 0xa5);
        macro_rules! check {
            ($($t:ty, $n:expr;)+) => {$(
                let b: [u8; $n] = bytes[..$n].try_into().unwrap();
                assert_eq!(BigEndian::<$t>::validate(&b), Ok(BigEndian(<$t>::from_be_bytes(b))));
                assert_eq!(
                    LittleEndian::<$t>::validate(&b),
                    Ok(LittleEndian(<$t>::from_le_bytes(b)))
                );
            )+};
        }
        check! {
            u8, 1; u16, 2; u32, 4; u64, 8; u128, 16;
            i8, 1; i16, 2; i32, 4; i64, 8; i128, 16;
        }
    }

    #[test]
    fn wrong_length() {
        assert_eq!(
            BigEndian::<u32>::validate(&[1, 2, 3]),
            Err(ValidationError::LengthMismatch {
                expected: 4,
                actual: 3
            })
        );
        assert_eq!(
            LittleEndian::<u8>::validate(&[]),
            Err(ValidationError::LengthMismatch {
                expected: 1,
                actual: 0
            })
        );
    }
}
