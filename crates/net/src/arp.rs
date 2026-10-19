//! ARP packets (RFC 826) for IPv4 over Ethernet.
//!
//! ```text
//! | htype 1 (2) | ptype 0x0800 (2) | hlen 6 (1) | plen 4 (1) | operation (2) |
//! | sender MAC (6) | sender IPv4 (4) | target MAC (6) | target IPv4 (4) | padding |
//! ```
//!
//! [`Arp`] accepts exactly the byte strings of this shape whose operation is a
//! request (1) or a reply (2). A minimum-size Ethernet frame pads the 28-byte
//! packet; the padding is handed back too.

use crate::ethernet::MacAddr;
use crate::ipv4::Ipv4Addr;
use untrusted::{BigEndian, Decode, Reader, Untrusted, Validate, ValidationError};

/// The EtherType of ARP.
pub const ETHER_TYPE_ARP: u16 = 0x0806;
/// Length of an Ethernet/IPv4 ARP packet.
pub const PACKET_LEN: usize = 28;
/// The operation of a request.
pub const OP_REQUEST: u16 = 1;
/// The operation of a reply.
pub const OP_REPLY: u16 = 2;

/// The fixed start of an Ethernet/IPv4 ARP packet: hardware type 1
/// (Ethernet), protocol type `0x0800` (IPv4), and address lengths 6 and 4.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EthernetIpv4;

impl Decode for EthernetIpv4 {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        if r.read::<BigEndian<u32>>()?.0 != 0x0001_0800 {
            return Err(ValidationError::OutOfRange);
        }
        if r.read::<BigEndian<u16>>()?.0 != 0x0604 {
            return Err(ValidationError::OutOfRange);
        }
        Ok(EthernetIpv4)
    }
}

/// The operation: [`OP_REQUEST`] or [`OP_REPLY`]. Decoded together with the
/// fixed fields before it ([`EthernetIpv4`]), so it covers the first 8 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Operation(pub u16);

impl Decode for Operation {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        r.decode::<EthernetIpv4>()?;
        let op = r.read::<BigEndian<u16>>()?.0;
        if op != OP_REQUEST && op != OP_REPLY {
            return Err(ValidationError::OutOfRange);
        }
        Ok(Operation(op))
    }
}

/// An Ethernet/IPv4 ARP packet.
#[derive(Decode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArpPacket {
    pub op: Operation,
    pub sender_mac: MacAddr,
    pub sender_ip: Ipv4Addr,
    pub target_mac: MacAddr,
    pub target_ip: Ipv4Addr,
}

/// An ARP packet followed by link-layer padding, borrowed from the input.
pub struct Arp<'a> {
    pub packet: ArpPacket,
    /// The bytes after the 28-byte packet.
    pub padding: Untrusted<&'a [u8]>,
}

impl<'a> Validate<&'a [u8]> for Arp<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        if input.len() < PACKET_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let packet = Untrusted::new(&input[..PACKET_LEN]).read_all::<ArpPacket>()?;
        Ok(Arp {
            packet,
            padding: Untrusted::new(&input[PACKET_LEN..]),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ipv4::tests::Count;

    /// A request from `02:00:00:00:00:01` (192.168.0.1) for 192.168.0.199.
    const REQUEST: [u8; 28] = [
        0x00, 0x01, 0x08, 0x00, 6, 4, 0x00, 0x01, 0x02, 0, 0, 0, 0, 0x01, 192, 168, 0, 1, 0, 0, 0,
        0, 0, 0, 192, 168, 0, 199,
    ];

    fn validate(bytes: &[u8]) -> Result<Arp<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Arp>()
    }

    #[test]
    fn accepts_requests_and_replies() {
        // Padded to the 46-byte minimum Ethernet payload.
        let mut buf = [0u8; 46];
        buf[..28].copy_from_slice(&REQUEST);
        let a = validate(&buf).unwrap();
        assert_eq!(a.packet.op, Operation(OP_REQUEST));
        assert_eq!(a.packet.sender_mac, MacAddr([2, 0, 0, 0, 0, 1]));
        assert_eq!(a.packet.sender_ip, Ipv4Addr(0xC0A8_0001));
        assert_eq!(a.packet.target_mac, MacAddr([0; 6]));
        assert_eq!(a.packet.target_ip, Ipv4Addr(0xC0A8_00C7));
        assert_eq!(a.padding.read_all::<Count>(), Ok(Count(18)));

        let mut reply = REQUEST;
        reply[7] = 2;
        assert_eq!(validate(&reply).unwrap().packet.op, Operation(OP_REPLY));
    }

    #[test]
    fn rejects_malformed_packets() {
        assert_eq!(validate(&REQUEST[..27]).err(), Some(ValidationError::EndOfInput));
        // Hardware type, protocol type, address lengths, operation.
        for (i, v) in [(1, 6), (2, 0x86), (4, 8), (5, 16), (7, 0), (7, 3)] {
            let mut b = REQUEST;
            b[i] = v;
            assert_eq!(validate(&b).err(), Some(ValidationError::OutOfRange), "byte {i}");
        }
    }
}
