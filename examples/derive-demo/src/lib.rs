//! A user crate whose derived `Decode` impls are verified against the
//! `untrusted` model by `derive_decode_spec`.

#![no_std]

use untrusted::{BigEndian, Decode, LittleEndian};

/// Named fields.
#[derive(Decode, Debug, PartialEq)]
pub struct Header {
    pub version: BigEndian<u8>,
    pub len: BigEndian<u16>,
}

/// A derived struct used as a field: formats compose.
#[derive(Decode, Debug, PartialEq)]
pub struct Packet {
    pub header: Header,
    pub checksum: LittleEndian<u32>,
}

/// A tuple struct mixing byte orders.
#[derive(Decode, Debug, PartialEq)]
pub struct Pair(pub BigEndian<u16>, pub LittleEndian<u16>);

/// Fixed-size byte arrays as fields: copied out as is.
#[derive(Decode, Debug, PartialEq)]
pub struct Keyed {
    pub id: LittleEndian<u32>,
    pub key: [u8; 32],
    pub tag: [u8; 16],
}

/// No fields: consumes nothing.
#[derive(Decode, Debug, PartialEq)]
pub struct Marker;

#[cfg(test)]
mod tests {
    use super::*;
    use untrusted::{Untrusted, ValidationError};

    #[test]
    fn derived() {
        let packet = Untrusted::new(&[1, 0, 2, 0xef, 0xbe, 0xad, 0xde][..]).read_all::<Packet>();
        assert_eq!(
            packet,
            Ok(Packet {
                header: Header {
                    version: BigEndian(1),
                    len: BigEndian(2)
                },
                checksum: LittleEndian(0xdead_beef),
            })
        );
        assert_eq!(
            Untrusted::new(&[0, 1, 1, 0][..]).read_all::<Pair>(),
            Ok(Pair(BigEndian(1), LittleEndian(1)))
        );
        assert_eq!(Untrusted::new(&[][..]).read_all::<Marker>(), Ok(Marker));
        assert_eq!(
            Untrusted::new(&[0][..]).read_all::<Marker>(),
            Err(ValidationError::TrailingData)
        );
        let mut bytes = [0u8; 52];
        bytes[0] = 7;
        bytes[4..36].fill(0xaa);
        bytes[36..].fill(0xbb);
        assert_eq!(
            Untrusted::new(&bytes[..]).read_all::<Keyed>(),
            Ok(Keyed {
                id: LittleEndian(7),
                key: [0xaa; 32],
                tag: [0xbb; 16]
            })
        );
        assert_eq!(
            Untrusted::new(&bytes[..51]).read_all::<Keyed>(),
            Err(ValidationError::EndOfInput)
        );
    }
}
