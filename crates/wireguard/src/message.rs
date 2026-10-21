//! The four WireGuard message formats (whitepaper section 5.4), all
//! little-endian:
//!
//! ```text
//! initiation (148): | 1 | sender | ephemeral (32) | static (48) | timestamp (28) | mac1 (16) | mac2 (16) |
//! response    (92): | 2 | sender | receiver | ephemeral (32) | empty (16) | mac1 (16) | mac2 (16) |
//! cookie      (64): | 3 | receiver | nonce (24) | cookie (32) |
//! transport  (32+): | 4 | receiver | counter (8) | encrypted packet (16+) |
//! ```
//!
//! The first 4 bytes hold the type: one byte and three zero bytes, so a
//! little-endian `u32`. [`Message`] accepts exactly the byte strings of one of
//! these shapes. The bodies after the type are derived structs.
//!
//! The encrypted packet of a transport message is at least its 16-byte
//! authentication tag. Its length is not required to be a multiple of 16:
//! senders pad to a multiple of 16 only up to the MTU, so full-size packets
//! are unaligned when the MTU is (as with Linux's default 1420).
//!
//! Each fixed-size message has an encoder (its type, then its body with the
//! derived `Encode`), proved to produce bytes that [`Message`] decodes back to
//! the same message.

use untrusted::{encode_into, Decode, Encode, LittleEndian, Untrusted, Validate, ValidationError};

/// The type of a handshake initiation.
pub const TYPE_INITIATION: u32 = 1;
/// The type of a handshake response.
pub const TYPE_RESPONSE: u32 = 2;
/// The type of a cookie reply.
pub const TYPE_COOKIE_REPLY: u32 = 3;
/// The type of a transport data message.
pub const TYPE_TRANSPORT: u32 = 4;

/// Length of the type field.
pub const TYPE_LEN: usize = 4;
/// Length of a handshake initiation.
pub const INITIATION_LEN: usize = 148;
/// Length of a handshake response.
pub const RESPONSE_LEN: usize = 92;
/// Length of a cookie reply.
pub const COOKIE_REPLY_LEN: usize = 64;
/// Length of the header of a transport message: type, receiver, counter.
pub const TRANSPORT_HEADER_LEN: usize = 16;
/// Length of an authentication tag.
pub const TAG_LEN: usize = 16;

/// A handshake initiation, after its type.
#[derive(Decode, Encode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Initiation {
    pub sender: LittleEndian<u32>,
    pub ephemeral: [u8; 32],
    pub encrypted_static: [u8; 48],
    pub encrypted_timestamp: [u8; 28],
    pub mac1: [u8; 16],
    pub mac2: [u8; 16],
}

/// A handshake response, after its type.
#[derive(Decode, Encode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Response {
    pub sender: LittleEndian<u32>,
    pub receiver: LittleEndian<u32>,
    pub ephemeral: [u8; 32],
    pub encrypted_nothing: [u8; 16],
    pub mac1: [u8; 16],
    pub mac2: [u8; 16],
}

/// A cookie reply, after its type.
#[derive(Decode, Encode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct CookieReply {
    pub receiver: LittleEndian<u32>,
    pub nonce: [u8; 24],
    pub encrypted_cookie: [u8; 32],
}

/// The header of a transport message, after its type.
#[derive(Decode, Encode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct TransportHeader {
    pub receiver: LittleEndian<u32>,
    pub counter: LittleEndian<u64>,
}

/// A transport message: its header, and the encrypted packet borrowed from the
/// input.
pub struct Transport<'a> {
    pub header: TransportHeader,
    /// The encrypted packet and its tag: at least [`TAG_LEN`] bytes.
    pub packet: Untrusted<&'a [u8]>,
}

/// A WireGuard message.
pub enum Message<'a> {
    Initiation(Initiation),
    Response(Response),
    CookieReply(CookieReply),
    Transport(Transport<'a>),
}

impl<'a> Validate<&'a [u8]> for Message<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        if input.len() < TYPE_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let kind = Untrusted::new(&input[..TYPE_LEN])
            .validate::<LittleEndian<u32>>()?
            .0;
        let body = Untrusted::new(&input[TYPE_LEN..]);
        if kind == TYPE_INITIATION {
            Ok(Message::Initiation(body.read_all::<Initiation>()?))
        } else if kind == TYPE_RESPONSE {
            Ok(Message::Response(body.read_all::<Response>()?))
        } else if kind == TYPE_COOKIE_REPLY {
            Ok(Message::CookieReply(body.read_all::<CookieReply>()?))
        } else if kind == TYPE_TRANSPORT {
            if input.len() < TRANSPORT_HEADER_LEN + TAG_LEN {
                return Err(ValidationError::EndOfInput);
            }
            let header = Untrusted::new(&input[TYPE_LEN..TRANSPORT_HEADER_LEN])
                .read_all::<TransportHeader>()?;
            Ok(Message::Transport(Transport {
                header,
                packet: Untrusted::new(&input[TRANSPORT_HEADER_LEN..]),
            }))
        } else {
            Err(ValidationError::OutOfRange)
        }
    }
}
/// Writes `src` at `out[pos..pos + src.len()]`, which must exist. Returns
/// `pos + src.len()`.
pub(crate) fn put_bytes(out: &mut [u8], pos: usize, src: &[u8]) -> usize {
    let mut i = 0;
    while i < src.len() {
        out[pos + i] = src[i];
        i += 1;
    }
    pos + src.len()
}

/// Writes a message of type `kind` with `body` to `out`, which holds exactly
/// the type and the body: the type, little-endian, then the body as derived.
/// (Not named `message`: that would shadow the `message` namespace in Lean.)
fn put_message<T: Encode>(kind: u32, body: &T, out: &mut [u8]) {
    let _ = encode_into(&LittleEndian(kind), out);
    let _ = encode_into(body, &mut out[TYPE_LEN..]);
}

impl Initiation {
    /// The message's bytes, type included.
    pub fn encode(&self) -> [u8; INITIATION_LEN] {
        let mut out = [0u8; INITIATION_LEN];
        put_message(TYPE_INITIATION, self, &mut out);
        out
    }
}

impl Response {
    /// The message's bytes, type included.
    pub fn encode(&self) -> [u8; RESPONSE_LEN] {
        let mut out = [0u8; RESPONSE_LEN];
        put_message(TYPE_RESPONSE, self, &mut out);
        out
    }
}

impl CookieReply {
    /// The message's bytes, type included.
    pub fn encode(&self) -> [u8; COOKIE_REPLY_LEN] {
        let mut out = [0u8; COOKIE_REPLY_LEN];
        put_message(TYPE_COOKIE_REPLY, self, &mut out);
        out
    }
}

impl TransportHeader {
    /// The first 16 bytes of a transport message: its type, then this header.
    pub fn encode(&self) -> [u8; TRANSPORT_HEADER_LEN] {
        let mut out = [0u8; TRANSPORT_HEADER_LEN];
        put_message(TYPE_TRANSPORT, self, &mut out);
        out
    }
}
#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    fn decode(bytes: &[u8]) -> Result<Message<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Message>()
    }

    /// Consumes everything, recording how many bytes there were.
    #[derive(Debug, PartialEq)]
    struct Count(usize);

    impl Decode for Count {
        fn decode(r: &mut untrusted::Reader<'_>) -> Result<Self, ValidationError> {
            let n = r.remaining();
            r.skip(n)?;
            Ok(Count(n))
        }
    }

    fn initiation() -> Initiation {
        Initiation {
            sender: LittleEndian(0x0403_0201),
            ephemeral: [0xe0; 32],
            encrypted_static: [0x5a; 48],
            encrypted_timestamp: [0x7b; 28],
            mac1: [0x11; 16],
            mac2: [0x22; 16],
        }
    }

    #[test]
    fn initiation_round_trip() {
        let m = initiation();
        let bytes = m.encode();
        assert_eq!(&bytes[..8], &[1, 0, 0, 0, 1, 2, 3, 4]);
        assert_eq!(&bytes[8..40], &[0xe0; 32]);
        assert_eq!(&bytes[132..], &[0x22; 16]);
        assert!(matches!(decode(&bytes), Ok(Message::Initiation(d)) if d == m));
    }

    #[test]
    fn response_and_cookie_round_trip() {
        let r = Response {
            sender: LittleEndian(7),
            receiver: LittleEndian(0xdead_beef),
            ephemeral: [1; 32],
            encrypted_nothing: [2; 16],
            mac1: [3; 16],
            mac2: [4; 16],
        };
        let bytes = r.encode();
        assert_eq!(
            &bytes[..12],
            &[2, 0, 0, 0, 7, 0, 0, 0, 0xef, 0xbe, 0xad, 0xde]
        );
        assert!(matches!(decode(&bytes), Ok(Message::Response(d)) if d == r));

        let c = CookieReply {
            receiver: LittleEndian(9),
            nonce: [5; 24],
            encrypted_cookie: [6; 32],
        };
        assert!(matches!(decode(&c.encode()), Ok(Message::CookieReply(d)) if d == c));
    }

    #[test]
    fn transport() {
        let mut bytes = [0u8; 48];
        bytes[0] = 4;
        bytes[4] = 9;
        bytes[8] = 1;
        bytes[15] = 0x80;
        let Ok(Message::Transport(t)) = decode(&bytes) else {
            panic!("not a transport message")
        };
        assert_eq!(t.header.receiver, LittleEndian(9));
        assert_eq!(t.header.counter, LittleEndian(0x8000_0000_0000_0001));
        assert_eq!(t.packet.read_all::<Count>(), Ok(Count(32)));
        // Just the tag (a keepalive): accepted. Shorter: rejected.
        assert!(matches!(decode(&bytes[..32]), Ok(Message::Transport(_))));
        assert!(matches!(
            decode(&bytes[..31]),
            Err(ValidationError::EndOfInput)
        ));
    }

    #[test]
    fn rejects_malformed_messages() {
        let bytes = initiation().encode();
        // Wrong lengths.
        assert!(matches!(
            decode(&bytes[..147]),
            Err(ValidationError::EndOfInput)
        ));
        let mut longer = [0u8; 149];
        longer[..148].copy_from_slice(&bytes);
        assert!(matches!(
            decode(&longer),
            Err(ValidationError::TrailingData)
        ));
        // Unknown types, and non-zero reserved bytes.
        for (i, v) in [(0, 0), (0, 5), (1, 1), (3, 0x80)] {
            let mut b = bytes;
            b[i] = v;
            assert!(
                matches!(decode(&b), Err(ValidationError::OutOfRange)),
                "byte {i}"
            );
        }
        assert!(matches!(
            decode(&bytes[..3]),
            Err(ValidationError::EndOfInput)
        ));
    }

    fn hex(bytes: &[u8]) -> std::string::String {
        bytes.iter().map(|b| std::format!("{b:02x}")).collect()
    }

    /// The exact bytes the encoders write: the wire format must not change
    /// when the encoders are rebuilt.
    #[test]
    fn golden_messages() {
        assert_eq!(hex(&initiation().encode()), "0100000001020304e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e05a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b1111111111111111111111111111111122222222222222222222222222222222");
        let r = Response {
            sender: LittleEndian(0x0102_0304),
            receiver: LittleEndian(0xa0b0_c0d0),
            ephemeral: [0x33; 32],
            encrypted_nothing: [0x44; 16],
            mac1: [0x55; 16],
            mac2: [0x66; 16],
        };
        assert_eq!(hex(&r.encode()), "0200000004030201d0c0b0a03333333333333333333333333333333333333333333333333333333333333333444444444444444444444444444444445555555555555555555555555555555566666666666666666666666666666666");
        let c = CookieReply { receiver: LittleEndian(9), nonce: [0x77; 24], encrypted_cookie: [0x88; 32] };
        assert_eq!(hex(&c.encode()), "03000000090000007777777777777777777777777777777777777777777777778888888888888888888888888888888888888888888888888888888888888888");
        let t = TransportHeader { receiver: LittleEndian(0xdead_beef), counter: LittleEndian(0x0102_0304_0506_0708) };
        assert_eq!(hex(&t.encode()), "04000000efbeadde0807060504030201");
    }
}
