//! Checked conversions between every pair of distinct primitive integer types.
//!
//! A conversion succeeds exactly when the input value is representable in the
//! target type, and then preserves the value.

use crate::{Validate, ValidationError};

// Each check casts to the target and back: the value is representable iff the
// round trip is lossless and, when signedness differs, the value is not
// negative.

macro_rules! unsigned_to_unsigned {
    ($($src:ty => $($dst:ty),+;)+) => {$($(
        impl Validate<$src> for $dst {
            type Err = ValidationError;
            fn validate(input: $src) -> Result<Self, Self::Err> {
                let out = input as $dst;
                if out as $src == input {
                    Ok(out)
                } else {
                    Err(ValidationError::OutOfRange)
                }
            }
        }
    )+)+};
}

macro_rules! unsigned_to_signed {
    ($($src:ty => $($dst:ty),+;)+) => {$($(
        impl Validate<$src> for $dst {
            type Err = ValidationError;
            fn validate(input: $src) -> Result<Self, Self::Err> {
                let out = input as $dst;
                if out >= 0 && out as $src == input {
                    Ok(out)
                } else {
                    Err(ValidationError::OutOfRange)
                }
            }
        }
    )+)+};
}

macro_rules! signed_to_unsigned {
    ($($src:ty => $($dst:ty),+;)+) => {$($(
        impl Validate<$src> for $dst {
            type Err = ValidationError;
            fn validate(input: $src) -> Result<Self, Self::Err> {
                let out = input as $dst;
                if input >= 0 && out as $src == input {
                    Ok(out)
                } else {
                    Err(ValidationError::OutOfRange)
                }
            }
        }
    )+)+};
}

macro_rules! signed_to_signed {
    ($($src:ty => $($dst:ty),+;)+) => {$($(
        impl Validate<$src> for $dst {
            type Err = ValidationError;
            fn validate(input: $src) -> Result<Self, Self::Err> {
                let out = input as $dst;
                if out as $src == input {
                    Ok(out)
                } else {
                    Err(ValidationError::OutOfRange)
                }
            }
        }
    )+)+};
}

unsigned_to_unsigned! {
    u8 => u16, u32, u64, u128, usize;
    u16 => u8, u32, u64, u128, usize;
    u32 => u8, u16, u64, u128, usize;
    u64 => u8, u16, u32, u128, usize;
    u128 => u8, u16, u32, u64, usize;
    usize => u8, u16, u32, u64, u128;
}

unsigned_to_signed! {
    u8 => i8, i16, i32, i64, i128, isize;
    u16 => i8, i16, i32, i64, i128, isize;
    u32 => i8, i16, i32, i64, i128, isize;
    u64 => i8, i16, i32, i64, i128, isize;
    u128 => i8, i16, i32, i64, i128, isize;
    usize => i8, i16, i32, i64, i128, isize;
}

signed_to_unsigned! {
    i8 => u8, u16, u32, u64, u128, usize;
    i16 => u8, u16, u32, u64, u128, usize;
    i32 => u8, u16, u32, u64, u128, usize;
    i64 => u8, u16, u32, u64, u128, usize;
    i128 => u8, u16, u32, u64, u128, usize;
    isize => u8, u16, u32, u64, u128, usize;
}

signed_to_signed! {
    i8 => i16, i32, i64, i128, isize;
    i16 => i8, i32, i64, i128, isize;
    i32 => i8, i16, i64, i128, isize;
    i64 => i8, i16, i32, i128, isize;
    i128 => i8, i16, i32, i64, isize;
    isize => i8, i16, i32, i64, i128;
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every conversion must agree with `core`'s `TryFrom`.
    macro_rules! agrees_with_try_from {
        ($src:ty => $($dst:ty),+) => {{
            let samples: [$src; 11] = [
                <$src>::MIN,
                <$src>::MIN / 2,
                0,
                1,
                127u8 as $src,
                128u8 as $src,
                255u8 as $src,
                256u16 as $src,
                65536u32 as $src,
                <$src>::MAX / 2,
                <$src>::MAX,
            ];
            for x in samples {
                $(
                    assert_eq!(
                        <$dst as Validate<$src>>::validate(x).ok(),
                        <$dst>::try_from(x).ok(),
                        "{} {} -> {}", x, stringify!($src), stringify!($dst),
                    );
                )+
            }
        }};
    }

    #[test]
    fn matches_core() {
        agrees_with_try_from!(u8 => u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
        agrees_with_try_from!(u16 => u8, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
        agrees_with_try_from!(u32 => u8, u16, u64, u128, usize, i8, i16, i32, i64, i128, isize);
        agrees_with_try_from!(u64 => u8, u16, u32, u128, usize, i8, i16, i32, i64, i128, isize);
        agrees_with_try_from!(u128 => u8, u16, u32, u64, usize, i8, i16, i32, i64, i128, isize);
        agrees_with_try_from!(usize => u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, isize);
        agrees_with_try_from!(i8 => u8, u16, u32, u64, u128, usize, i16, i32, i64, i128, isize);
        agrees_with_try_from!(i16 => u8, u16, u32, u64, u128, usize, i8, i32, i64, i128, isize);
        agrees_with_try_from!(i32 => u8, u16, u32, u64, u128, usize, i8, i16, i64, i128, isize);
        agrees_with_try_from!(i64 => u8, u16, u32, u64, u128, usize, i8, i16, i32, i128, isize);
        agrees_with_try_from!(i128 => u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, isize);
        agrees_with_try_from!(isize => u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128);
    }
}
