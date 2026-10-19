//! Sequential reading of untrusted byte strings.
//!
//! A [`Reader`] is only available inside [`Decode::decode`], called by
//! [`Untrusted::read_all`], which fails unless decoding consumes every byte:
//! trailing data can never be ignored by accident. Every reader method either
//! succeeds and advances, or fails and leaves the reader unchanged. Sub-slices
//! are handed out as [`Untrusted`] again, so they too must be validated (exact
//! length) or decoded with `read_all` (must finish) before use.

use crate::{FixedLen, Untrusted, Validate, ValidationError};

/// A cursor over untrusted bytes.
///
/// Invariant: `pos <= input.len()`.
pub struct Reader<'a> {
    input: &'a [u8],
    pos: usize,
}

/// A type decoded from a sequence of bytes with a [`Reader`].
///
/// `decode` only ever borrows the reader, so it cannot skip the trailing-data
/// check that [`Untrusted::read_all`] performs once it returns.
///
/// Decoded values own their data: they cannot borrow from the input. (A
/// lifetime linking the two is beyond what Aeneas can currently translate.)
pub trait Decode: Sized {
    fn decode(reader: &mut Reader<'_>) -> Result<Self, ValidationError>;
}

impl Untrusted<&[u8]> {
    /// Decodes the whole input as a `P`.
    ///
    /// Fails with [`ValidationError::TrailingData`] if `P::decode` succeeds
    /// without consuming every byte, so decoding can never silently ignore
    /// extra input.
    ///
    /// ```
    /// use untrusted::{BigEndian, Decode, Reader, Untrusted, ValidationError};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Port(u16);
    ///
    /// impl Decode for Port {
    ///     fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
    ///         Ok(Port(r.read::<BigEndian<u16>>()?.0))
    ///     }
    /// }
    ///
    /// assert_eq!(Untrusted::new(&[0x1f, 0x90][..]).read_all::<Port>(), Ok(Port(8080)));
    /// assert_eq!(
    ///     Untrusted::new(&[0x1f, 0x90, 0][..]).read_all::<Port>(),
    ///     Err(ValidationError::TrailingData)
    /// );
    /// ```
    ///
    /// A reader cannot be obtained any other way, nor finished early:
    ///
    /// ```compile_fail,E0599
    /// # use untrusted::Untrusted;
    /// let r = Untrusted::new(&[1u8][..]).reader();
    /// ```
    ///
    /// ```compile_fail,E0624
    /// # use untrusted::{Decode, Reader, ValidationError};
    /// struct Skip;
    /// impl Decode for Skip {
    ///     fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
    ///         r.finish()?;
    ///         Ok(Skip)
    ///     }
    /// }
    /// ```
    pub fn read_all<P: Decode>(self) -> Result<P, ValidationError> {
        // Not named `reader`: that would shadow the `reader` namespace in the
        // generated Lean.
        let mut cursor = Reader {
            input: self.0,
            pos: 0,
        };
        let value = P::decode(&mut cursor)?;
        cursor.finish()?;
        Ok(value)
    }
}

impl<'a> Reader<'a> {
    /// Number of bytes not yet read.
    pub fn remaining(&self) -> usize {
        self.input.len() - self.pos
    }

    /// Whether every byte has been read.
    pub fn at_end(&self) -> bool {
        self.pos == self.input.len()
    }

    /// Whether the next byte is `b`, without consuming it.
    pub fn peek(&self, b: u8) -> bool {
        self.pos < self.input.len() && self.input[self.pos] == b
    }

    /// Reads one byte.
    pub fn read_byte(&mut self) -> Result<u8, ValidationError> {
        if self.pos < self.input.len() {
            let b = self.input[self.pos];
            self.pos += 1;
            Ok(b)
        } else {
            Err(ValidationError::EndOfInput)
        }
    }

    /// Reads the next `n` bytes.
    pub fn read_bytes(&mut self, n: usize) -> Result<Untrusted<&'a [u8]>, ValidationError> {
        // Compared against `remaining()` rather than computing `pos + n`,
        // which could overflow.
        if n > self.remaining() {
            return Err(ValidationError::EndOfInput);
        }
        let start = self.pos;
        let end = start + n;
        self.pos = end;
        Ok(Untrusted(&self.input[start..end]))
    }

    /// Skips the next `n` bytes.
    pub fn skip(&mut self, n: usize) -> Result<(), ValidationError> {
        self.read_bytes(n)?;
        Ok(())
    }

    /// Reads all remaining bytes.
    pub fn read_bytes_to_end(&mut self) -> Untrusted<&'a [u8]> {
        let rest = &self.input[self.pos..];
        self.pos = self.input.len();
        Untrusted(rest)
    }

    /// Decodes a `P` from the next bytes, e.g. a nested struct or field. On
    /// failure nothing is consumed.
    pub fn decode<P: Decode>(&mut self) -> Result<P, ValidationError> {
        let start = self.pos;
        match P::decode(self) {
            Ok(value) => Ok(value),
            Err(e) => {
                self.pos = start;
                Err(e)
            }
        }
    }

    /// Reads exactly `T::LEN` bytes and validates them as a `T`, e.g.
    /// `reader.read::<BigEndian<u32>>()`. On failure nothing is consumed.
    pub fn read<T>(&mut self) -> Result<T, ValidationError>
    where
        T: FixedLen + Validate<&'a [u8], Err = ValidationError>,
    {
        if T::LEN > self.remaining() {
            return Err(ValidationError::EndOfInput);
        }
        let start = self.pos;
        let end = start + T::LEN;
        let value = T::validate(&self.input[start..end])?;
        self.pos = end;
        Ok(value)
    }

    /// Ends reading, failing if any bytes were left unread. Only
    /// [`Untrusted::read_all`] calls this.
    fn finish(self) -> Result<(), ValidationError> {
        if self.at_end() {
            Ok(())
        } else {
            Err(ValidationError::TrailingData)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BigEndian, LittleEndian};

    // The tests below exercise the methods directly; `read_all` is the only
    // public way to get a reader.
    fn reader(bytes: &[u8]) -> Reader<'_> {
        Reader {
            input: bytes,
            pos: 0,
        }
    }

    fn all<P: Decode>(bytes: &[u8]) -> Result<P, ValidationError> {
        Untrusted::new(bytes).read_all::<P>()
    }

    fn bytes(u: Untrusted<&[u8]>) -> &[u8] {
        u.0
    }

    #[derive(Debug, PartialEq)]
    struct Pair(u8, u8);

    impl Decode for Pair {
        fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
            Ok(Pair(r.read_byte()?, r.read_byte()?))
        }
    }

    #[derive(Debug, PartialEq)]
    struct Nothing;

    impl Decode for Nothing {
        fn decode(_: &mut Reader<'_>) -> Result<Self, ValidationError> {
            Ok(Nothing)
        }
    }

    /// Consumes everything, keeping a copy of the first byte.
    #[derive(Debug, PartialEq)]
    struct FirstOfRest(Option<u8>);

    impl Decode for FirstOfRest {
        fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
            Ok(FirstOfRest(bytes(r.read_bytes_to_end()).first().copied()))
        }
    }

    /// A length byte followed by exactly that many bytes holding a `u16`.
    #[derive(Debug, PartialEq)]
    struct Prefixed(u16);

    impl Decode for Prefixed {
        fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
            let len = r.read_byte()?;
            let body = r.read_bytes(len as usize)?;
            Ok(Prefixed(body.read_all::<Be16>()?.0))
        }
    }

    struct Be16(u16);

    impl Decode for Be16 {
        fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
            Ok(Be16(r.read::<BigEndian<u16>>()?.0))
        }
    }

    #[test]
    fn empty() {
        let mut r = reader(&[]);
        assert!(r.at_end());
        assert_eq!(r.remaining(), 0);
        assert!(!r.peek(0));
        assert_eq!(r.read_byte(), Err(ValidationError::EndOfInput));
        assert_eq!(bytes(r.read_bytes(0).unwrap()), &[] as &[u8]);
        assert_eq!(bytes(r.read_bytes_to_end()), &[] as &[u8]);
        assert_eq!(r.finish(), Ok(()));
    }

    #[test]
    fn sequential() {
        let mut r = reader(&[1, 2, 3, 4, 5, 6, 7]);
        assert!(r.peek(1));
        assert!(!r.peek(2));
        assert_eq!(r.read_byte(), Ok(1));
        assert_eq!(bytes(r.read_bytes(2).unwrap()), &[2, 3]);
        assert_eq!(r.skip(1), Ok(()));
        assert_eq!(r.remaining(), 3);
        assert_eq!(bytes(r.read_bytes_to_end()), &[5, 6, 7]);
        assert!(r.at_end());
        assert_eq!(r.finish(), Ok(()));
    }

    #[test]
    fn errors_leave_reader_unchanged() {
        let mut r = reader(&[1, 2, 3]);
        assert_eq!(r.read_byte(), Ok(1));
        assert!(matches!(r.read_bytes(3), Err(ValidationError::EndOfInput)));
        assert!(matches!(
            r.read_bytes(usize::MAX),
            Err(ValidationError::EndOfInput)
        ));
        assert_eq!(r.skip(3), Err(ValidationError::EndOfInput));
        assert_eq!(r.read::<BigEndian<u32>>(), Err(ValidationError::EndOfInput));
        assert_eq!(r.remaining(), 2);
        assert_eq!(bytes(r.read_bytes(2).unwrap()), &[2, 3]);
    }

    #[test]
    fn exact_and_trailing() {
        let mut r = reader(&[1, 2]);
        assert_eq!(bytes(r.read_bytes(2).unwrap()), &[1, 2]);
        assert_eq!(r.read_byte(), Err(ValidationError::EndOfInput));
        assert_eq!(r.finish(), Ok(()));

        let r = reader(&[1, 2]);
        assert_eq!(r.finish(), Err(ValidationError::TrailingData));
    }

    #[test]
    fn typed_reads() {
        let mut r = reader(&[0x12, 0x34, 0x56, 0x78, 0xff, 0xfe, 0x01]);
        assert_eq!(r.read::<BigEndian<u32>>(), Ok(BigEndian(0x1234_5678)));
        assert_eq!(r.read::<LittleEndian<i16>>(), Ok(LittleEndian(-257)));
        assert_eq!(r.read::<BigEndian<u8>>(), Ok(BigEndian(1)));
        assert_eq!(r.finish(), Ok(()));
    }

    #[test]
    fn read_all_requires_full_consumption() {
        assert_eq!(all::<Pair>(&[1, 2]), Ok(Pair(1, 2)));
        assert_eq!(all::<Pair>(&[1, 2, 3]), Err(ValidationError::TrailingData));
        assert_eq!(all::<Pair>(&[1]), Err(ValidationError::EndOfInput));
        assert_eq!(all::<Nothing>(&[]), Ok(Nothing));
        assert_eq!(all::<Nothing>(&[0]), Err(ValidationError::TrailingData));
        assert_eq!(all::<FirstOfRest>(&[1, 2, 3]), Ok(FirstOfRest(Some(1))));
        assert_eq!(all::<FirstOfRest>(&[]), Ok(FirstOfRest(None)));
    }

    /// Two fields, the second of which must not be consumed on failure.
    #[derive(Debug, PartialEq)]
    struct Header(BigEndian<u8>, BigEndian<u16>);

    impl Decode for Header {
        fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
            Ok(Header(r.decode()?, r.decode()?))
        }
    }

    #[test]
    fn parse_is_transactional() {
        let mut r = reader(&[1, 2]);
        assert_eq!(r.decode::<Header>(), Err(ValidationError::EndOfInput));
        assert_eq!(r.remaining(), 2);
        assert_eq!(r.decode::<BigEndian<u16>>(), Ok(BigEndian(0x0102)));
        assert_eq!(
            all::<Header>(&[1, 0, 2]),
            Ok(Header(BigEndian(1), BigEndian(2)))
        );
        assert_eq!(
            all::<Header>(&[1, 0, 2, 3]),
            Err(ValidationError::TrailingData)
        );
    }

    #[test]
    fn nested_read_all() {
        // The length-prefixed body must itself be consumed exactly.
        assert_eq!(all::<Prefixed>(&[2, 0xab, 0xcd]), Ok(Prefixed(0xabcd)));
        assert_eq!(
            all::<Prefixed>(&[3, 0xab, 0xcd, 0xef]),
            Err(ValidationError::TrailingData)
        );
        assert_eq!(
            all::<Prefixed>(&[2, 0xab, 0xcd, 0xef]),
            Err(ValidationError::TrailingData)
        );
    }
}
