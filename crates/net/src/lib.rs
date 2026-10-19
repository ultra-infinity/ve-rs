//! Verified decoding of network frames, from Ethernet up to UDP.
//!
//! Every decoder here is extracted to Lean and proved correct by
//! `cargo untrusted verify -p net` (`make verify-net`): it accepts exactly the
//! well-formed input, never panics, and hands the next layer's bytes back as
//! [`untrusted::Untrusted`]. Layers stack by validating that payload:
//!
//! - [`ethernet::Frame`] / [`ethernet::FrameWithFcs`]: Ethernet II, 802.1Q;
//! - [`arp::Arp`]: ARP for IPv4 over Ethernet;
//! - [`ipv4::Ipv4Packet`], [`ipv6::Ipv6Packet`]: IP packets;
//! - [`udp::Ipv4Udp`], [`udp::Ipv6Udp`]: UDP datagrams, with their checksums;
//! - [`icmp::Icmpv4`], [`icmp::Icmpv6`]: ICMP messages, with their checksums.
//!
//! The UDP and ICMP validators take the whole IP packet, since their checksums
//! cover fields of the IP header.

#![no_std]

pub mod arp;
pub mod crc32;
pub mod ethernet;
pub mod icmp;
pub mod inet;
pub mod ipv4;
pub mod ipv6;
pub mod udp;

#[cfg(test)]
mod tests {
    use crate::arp::{Arp, Operation, ETHER_TYPE_ARP, OP_REQUEST};
    use crate::crc32::crc32;
    use crate::ethernet::{EtherType, FrameWithFcs};
    use crate::ipv4::tests::Count;
    use crate::ipv4::ETHER_TYPE_IPV4;
    use crate::udp::{self, Ipv4Udp};
    use untrusted::{BigEndian, Untrusted};

    /// Writes the Ethernet header, then calls `body` on the rest, then appends
    /// the FCS. Returns the frame's length.
    fn frame(buf: &mut [u8], ether_type: u16, body: impl FnOnce(&mut [u8]) -> usize) -> usize {
        buf[..6].fill(0xff);
        buf[6..12].copy_from_slice(&[2, 0, 0, 0, 0, 1]);
        buf[12..14].copy_from_slice(&ether_type.to_be_bytes());
        let end = 14 + body(&mut buf[14..]);
        let fcs = crc32(&buf[..end]);
        buf[end..end + 4].copy_from_slice(&fcs.to_le_bytes());
        end + 4
    }

    #[test]
    fn ethernet_to_udp() {
        let mut buf = [0u8; 128];
        // 20 + 8 + 4 bytes of IPv4/UDP, padded to the 46-byte minimum payload.
        let n = frame(&mut buf, ETHER_TYPE_IPV4, |b| udp::tests::datagram(b, 4, true, 14));
        let f = Untrusted::new(&buf[..n]).validate::<FrameWithFcs>().unwrap();
        assert_eq!(f.frame.header.tagging.ether_type, EtherType(ETHER_TYPE_IPV4));
        let u = f.frame.payload.validate::<Ipv4Udp>().unwrap();
        assert_eq!(u.header.dst_port, BigEndian(53));
        assert_eq!(u.payload.read_all::<Count>(), Ok(Count(4)));
        assert_eq!(u.ip.padding.read_all::<Count>(), Ok(Count(14)));
    }

    #[test]
    fn ethernet_to_arp() {
        let mut buf = [0u8; 128];
        let n = frame(&mut buf, ETHER_TYPE_ARP, |b| {
            b[..46].fill(0);
            b[..8].copy_from_slice(&[0, 1, 8, 0, 6, 4, 0, 1]);
            46
        });
        let f = Untrusted::new(&buf[..n]).validate::<FrameWithFcs>().unwrap();
        let a = f.frame.payload.validate::<Arp>().unwrap();
        assert_eq!(a.packet.op, Operation(OP_REQUEST));
        assert_eq!(a.padding.read_all::<Count>(), Ok(Count(18)));
    }
}
