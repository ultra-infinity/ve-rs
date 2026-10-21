//! Sequential writing of byte strings: the counterpart of [`Reader`].
//!
//! A [`Writer`] is only available inside [`Encode::encode`], called by
//! [`encode_into`]. Every writer method either succeeds and advances, or
//! fails with [`EncodeError::NoRoom`] and leaves the writer unchanged.
//! Encoding never fails for any other reason: a value the decoder would
//! reject (say, a field out of its range) is still written, and
//! `proofs/Untrusted` proves the round trip only for values it accepts.
//!
//! [`Reader`]: crate::Reader

use crate::{BigEndian, LittleEndian};

/// Why encoding failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EncodeError {
    /// The output is too short for the encoding.
    NoRoom,
}

/// A cursor over the output.
///
/// Invariant: `pos <= out.len()`.
pub struct Writer<'a> {
    out: &'a mut [u8],
    pos: usize,
}

/// A type encoded to a sequence of bytes with a [`Writer`].
///
/// `encode` only ever borrows the writer, so it cannot change where the
/// encoding starts; [`encode_into`] reports how many bytes were written.
pub trait Encode {
    fn encode(&self, w: &mut Writer<'_>) -> Result<(), EncodeError>;
}

/// Writes `v` to the start of `out`, and returns the length of its
/// encoding; fails if `out` is too short.
///
/// ```
/// use untrusted::{encode_into, BigEndian, Decode, Encode, EncodeError, Untrusted};
///
/// #[derive(Decode, Encode, Debug, PartialEq)]
/// struct Header {
///     version: BigEndian<u8>,
///     len: BigEndian<u16>,
/// }
///
/// let h = Header { version: BigEndian(1), len: BigEndian(0x0203) };
/// let mut out = [0u8; 8];
/// assert_eq!(encode_into(&h, &mut out), Ok(3));
/// assert_eq!(&out[..3], &[1, 2, 3]);
/// assert_eq!(Untrusted::new(&out[..3]).read_all::<Header>(), Ok(h));
/// assert_eq!(encode_into(&Header { version: BigEndian(1), len: BigEndian(2) }, &mut out[..2]),
///            Err(EncodeError::NoRoom));
/// ```
pub fn encode_into<T: Encode>(v: &T, out: &mut [u8]) -> Result<usize, EncodeError> {
    // Not named `writer`: that would shadow the `writer` namespace in the
    // generated Lean.
    let mut cursor = Writer { out, pos: 0 };
    v.encode(&mut cursor)?;
    Ok(cursor.pos)
}

/// Copies `src` to `out[pos..pos + src.len()]`, which must exist.
fn put_bytes(out: &mut [u8], pos: usize, src: &[u8]) {
    let mut i = 0;
    while i < src.len() {
        out[pos + i] = src[i];
        i += 1;
    }
}

/// Writes the `n` low bytes of `v`, most significant first, to
/// `out[pos..pos + n]`, which must exist.
fn put_be(out: &mut [u8], pos: usize, v: u128, n: usize) {
    let mut v = v;
    let mut i = n;
    while i > 0 {
        i -= 1;
        out[pos + i] = (v % 256) as u8;
        v /= 256;
    }
}

/// Writes the `n` low bytes of `v`, least significant first, to
/// `out[pos..pos + n]`, which must exist.
fn put_le(out: &mut [u8], pos: usize, v: u128, n: usize) {
    let mut v = v;
    let mut i = 0;
    while i < n {
        out[pos + i] = (v % 256) as u8;
        v /= 256;
        i += 1;
    }
}

impl<'a> Writer<'a> {
    /// Number of bytes that still fit.
    pub fn remaining(&self) -> usize {
        self.out.len() - self.pos
    }

    /// Writes one byte.
    pub fn write_byte(&mut self, b: u8) -> Result<(), EncodeError> {
        if self.pos < self.out.len() {
            self.out[self.pos] = b;
            self.pos += 1;
            Ok(())
        } else {
            Err(EncodeError::NoRoom)
        }
    }

    /// Writes `b`.
    pub fn write_bytes(&mut self, b: &[u8]) -> Result<(), EncodeError> {
        // Compared against `remaining()` rather than computing `pos + n`,
        // which could overflow.
        if b.len() > self.remaining() {
            return Err(EncodeError::NoRoom);
        }
        put_bytes(self.out, self.pos, b);
        self.pos += b.len();
        Ok(())
    }

    /// Writes the `n` low bytes of `v`, most significant first.
    fn write_be(&mut self, v: u128, n: usize) -> Result<(), EncodeError> {
        if n > self.remaining() {
            return Err(EncodeError::NoRoom);
        }
        put_be(self.out, self.pos, v, n);
        self.pos += n;
        Ok(())
    }

    /// Writes the `n` low bytes of `v`, least significant first.
    fn write_le(&mut self, v: u128, n: usize) -> Result<(), EncodeError> {
        if n > self.remaining() {
            return Err(EncodeError::NoRoom);
        }
        put_le(self.out, self.pos, v, n);
        self.pos += n;
        Ok(())
    }

    /// Encodes `v` at the current position, e.g. a nested struct or field.
    /// On failure the position is unchanged.
    pub fn encode<T: Encode>(&mut self, v: &T) -> Result<(), EncodeError> {
        let start = self.pos;
        match v.encode(self) {
            Ok(()) => Ok(()),
            Err(e) => {
                self.pos = start;
                Err(e)
            }
        }
    }
}

/// Every fixed-width integer is written as the bytes it is decoded from: its
/// value (as the unsigned integer of the same width) in `$n` bytes. (The
/// parameter is not named `writer`: that would shadow the `writer` namespace
/// in the generated Lean.)
macro_rules! impl_encode {
    ($($t:ty, $u:ty, $n:expr;)+) => {$(
        impl Encode for BigEndian<$t> {
            fn encode(&self, w: &mut Writer<'_>) -> Result<(), EncodeError> {
                w.write_be(self.0 as $u as u128, $n)
            }
        }

        impl Encode for LittleEndian<$t> {
            fn encode(&self, w: &mut Writer<'_>) -> Result<(), EncodeError> {
                w.write_le(self.0 as $u as u128, $n)
            }
        }
    )+};
}

impl_encode! {
    u8, u8, 1;
    u16, u16, 2;
    u32, u32, 4;
    u64, u64, 8;
    u128, u128, 16;
    i8, u8, 1;
    i16, u16, 2;
    i32, u32, 4;
    i64, u64, 8;
    i128, u128, 16;
}

/// The `N` bytes, as they are.
impl<const N: usize> Encode for [u8; N] {
    fn encode(&self, w: &mut Writer<'_>) -> Result<(), EncodeError> {
        w.write_bytes(self)
    }
}

/// The bytes, as they are: a payload, say. Nothing records their length.
impl Encode for &[u8] {
    fn encode(&self, w: &mut Writer<'_>) -> Result<(), EncodeError> {
        w.write_bytes(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Untrusted;

    fn writer(out: &mut [u8]) -> Writer<'_> {
        Writer { out, pos: 0 }
    }

    #[test]
    fn writes_and_runs_out_of_room() {
        let mut out = [0u8; 4];
        let mut w = writer(&mut out);
        assert_eq!(w.write_byte(1), Ok(()));
        assert_eq!(w.write_bytes(&[2, 3]), Ok(()));
        assert_eq!(w.remaining(), 1);
        assert_eq!(w.write_bytes(&[4, 5]), Err(EncodeError::NoRoom));
        assert_eq!(w.remaining(), 1);
        assert_eq!(w.write_byte(4), Ok(()));
        assert_eq!(w.write_byte(5), Err(EncodeError::NoRoom));
        assert_eq!(w.write_bytes(&[]), Ok(()));
        assert_eq!(out, [1, 2, 3, 4]);
    }

    struct Pair(BigEndian<u16>, BigEndian<u16>);

    impl Encode for Pair {
        fn encode(&self, w: &mut Writer<'_>) -> Result<(), EncodeError> {
            w.encode(&self.0)?;
            w.encode(&self.1)
        }
    }

    #[test]
    fn a_failed_encode_leaves_the_position() {
        let mut out = [0u8; 3];
        let mut w = writer(&mut out);
        assert_eq!(w.encode(&Pair(BigEndian(1), BigEndian(2))), Err(EncodeError::NoRoom));
        assert_eq!(w.remaining(), 3);
        assert_eq!(encode_into(&Pair(BigEndian(0x0102), BigEndian(0x0304)), &mut [0u8; 4]), Ok(4));
    }

    /// Every encoder agrees with `core`'s `to_{be,le}_bytes`, and decodes
    /// back.
    #[test]
    fn matches_core() {
        macro_rules! check {
            ($($t:ty, $n:expr, $v:expr;)+) => {$(
                let v: $t = $v;
                let mut out = [0u8; 16];
                assert_eq!(encode_into(&BigEndian(v), &mut out), Ok($n));
                assert_eq!(&out[..$n], &v.to_be_bytes());
                assert_eq!(Untrusted::new(&out[..$n]).read_all::<BigEndian<$t>>(), Ok(BigEndian(v)));
                assert_eq!(encode_into(&LittleEndian(v), &mut out), Ok($n));
                assert_eq!(&out[..$n], &v.to_le_bytes());
                assert_eq!(Untrusted::new(&out[..$n]).read_all::<LittleEndian<$t>>(), Ok(LittleEndian(v)));
                assert_eq!(encode_into(&BigEndian(v), &mut out[..$n - 1]), Err(EncodeError::NoRoom));
            )+};
        }
        check! {
            u8, 1, 0xa5; u16, 2, 0x1234; u32, 4, 0xdead_beef; u64, 8, u64::MAX - 7;
            u128, 16, u128::MAX / 3;
            i8, 1, -2; i16, 2, -300; i32, 4, i32::MIN; i64, 8, -1; i128, 16, i128::MIN + 5;
        }
    }

    #[test]
    fn byte_strings() {
        let mut out = [0u8; 4];
        assert_eq!(encode_into(&[7u8, 8, 9], &mut out), Ok(3));
        assert_eq!(encode_into(&&[1u8, 2][..], &mut out[1..]), Ok(2));
        assert_eq!(out, [7, 1, 2, 0]);
        assert_eq!(encode_into(&[0u8; 5], &mut out), Err(EncodeError::NoRoom));
    }
}
