//! Fixed-width integers from byte slices.
//!
//! The input must be exactly as long as the target integer; there is no
//! implicit truncation or padding. `usize`/`isize` are deliberately not
//! supported since their width is platform dependent.

use crate::{Validate, ValidationError};

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

#[cfg(test)]
mod tests {
    use super::*;

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
