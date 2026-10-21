//! A user crate whose derived `Decode` and `Encode` impls are verified against the
//! `untrusted` model by `derive_decode_spec` and `derive_encode_spec`, which also
//! prove that each decodes back what it encodes.

#![no_std]

use untrusted::{BigEndian, Decode, Encode, LittleEndian};

/// Named fields.
#[derive(Decode, Encode, Debug, PartialEq)]
pub struct Header {
    pub version: BigEndian<u8>,
    pub len: BigEndian<u16>,
}

/// A derived struct used as a field: formats compose.
#[derive(Decode, Encode, Debug, PartialEq)]
pub struct Packet {
    pub header: Header,
    pub checksum: LittleEndian<u32>,
}

/// A tuple struct mixing byte orders.
#[derive(Decode, Encode, Debug, PartialEq)]
pub struct Pair(pub BigEndian<u16>, pub LittleEndian<u16>);

/// Fixed-size byte arrays as fields: copied out as is.
#[derive(Decode, Encode, Debug, PartialEq)]
pub struct Keyed {
    pub id: LittleEndian<u32>,
    pub key: [u8; 32],
    pub tag: [u8; 16],
}

/// One field.
#[derive(Decode, Encode, Debug, PartialEq)]
pub struct Version(pub BigEndian<u8>);

/// No fields: consumes nothing.
#[derive(Decode, Encode, Debug, PartialEq)]
pub struct Marker;

/// A borrowed payload: encoded as is (it has no `Decode`, since nothing records
/// its length).
#[derive(Encode)]
pub struct Framed<'a> {
    pub header: Header,
    pub payload: &'a [u8],
}

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

    #[test]
    fn encoded() {
        use untrusted::{encode_into, EncodeError};
        let packet = Packet {
            header: Header { version: BigEndian(1), len: BigEndian(2) },
            checksum: LittleEndian(0xdead_beef),
        };
        let mut out = [0u8; 64];
        assert_eq!(encode_into(&packet, &mut out), Ok(7));
        assert_eq!(&out[..7], &[1, 0, 2, 0xef, 0xbe, 0xad, 0xde]);
        assert_eq!(Untrusted::new(&out[..7]).read_all::<Packet>(), Ok(packet));
        assert_eq!(encode_into(&Marker, &mut out), Ok(0));
        assert_eq!(encode_into(&Version(BigEndian(9)), &mut out), Ok(1));
        let keyed = Keyed { id: LittleEndian(7), key: [0xaa; 32], tag: [0xbb; 16] };
        assert_eq!(encode_into(&keyed, &mut out[..51]), Err(EncodeError::NoRoom));
        assert_eq!(encode_into(&keyed, &mut out), Ok(52));
        assert_eq!(Untrusted::new(&out[..52]).read_all::<Keyed>(), Ok(keyed));
        let framed = Framed { header: Header { version: BigEndian(2), len: BigEndian(3) }, payload: b"hi" };
        assert_eq!(encode_into(&framed, &mut out), Ok(5));
        assert_eq!(&out[..5], &[2, 0, 3, b'h', b'i']);
    }
}
