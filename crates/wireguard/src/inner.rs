//! The IP packets carried inside the tunnel.

use net::ipv4::Ipv4Packet;
use untrusted::Untrusted;

/// The source address of `packet`, if it is a well-formed IPv4 packet.
pub fn ipv4_source(packet: &[u8]) -> Option<u32> {
    match Untrusted::new(packet).validate::<Ipv4Packet>() {
        Ok(p) => Some(p.header.src.0),
        Err(_) => None,
    }
}
