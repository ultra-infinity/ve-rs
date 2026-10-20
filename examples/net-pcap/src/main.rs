//! `net-pcap <file.pcap>`: runs every frame of an Ethernet capture through the
//! verified decoders of the `net` crate, and reports where each one was
//! accepted or rejected.
//!
//! This harness is not verified. It reads the capture with plain `std` code
//! and picks a decoder from each layer's type field; only the decoders
//! themselves carry proofs.
//!
//! Captures hold frames without their FCS, so frames are validated as
//! `ethernet::Frame`. Linux captures of *outgoing* frames are not padded to the
//! 60-byte Ethernet minimum (the NIC pads them later), so they may be rejected
//! as too short; capture inbound traffic (`tcpdump -Q in`) to see frames as
//! they were on the wire.
//!
//! Exits with status 1 if any frame was rejected, 2 on a malformed capture.

use net::arp::{self, Arp};
use net::ethernet::Frame;
use net::icmp::{Icmpv4, Icmpv6};
use net::ipv4::{self, Ipv4Packet};
use net::ipv6::{self, Ipv6Packet};
use net::udp::{Ipv4Udp, Ipv6Udp};
use std::collections::BTreeMap;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::process::exit;
use untrusted::{Decode, Reader, Untrusted, Validate, ValidationError};

/// Copies out whatever bytes remain, to print them.
struct Bytes(Vec<u8>);

impl Decode for Bytes {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        let mut v = Vec::with_capacity(r.remaining());
        while !r.at_end() {
            v.push(r.read_byte()?);
        }
        Ok(Bytes(v))
    }
}

fn contents(u: Untrusted<&[u8]>) -> Vec<u8> {
    u.read_all::<Bytes>().map(|b| b.0).unwrap_or_default()
}

fn show(data: &[u8]) -> String {
    if data.len() <= 32 && data.iter().all(|b| b.is_ascii_graphic() || *b == b' ') {
        format!("{:?}", String::from_utf8_lossy(data))
    } else {
        format!("{} bytes", data.len())
    }
}

/// What happened to one frame: the layer it reached, and a description.
type Outcome = Result<(&'static str, String), (&'static str, ValidationError)>;

fn validate<'a, T: Validate<&'a [u8], Err = ValidationError>>(
    layer: &'static str,
    bytes: &'a [u8],
) -> Result<T, (&'static str, ValidationError)> {
    Untrusted::new(bytes).validate::<T>().map_err(|e| (layer, e))
}

fn ipv4(bytes: &[u8]) -> Outcome {
    let p = validate::<Ipv4Packet>("ipv4", bytes)?;
    let (src, dst) = (Ipv4Addr::from(p.header.src.0), Ipv4Addr::from(p.header.dst.0));
    match p.header.protocol.0 {
        ipv4::PROTO_UDP if !p.header.fragment.is_fragment() => {
            let u = validate::<Ipv4Udp>("ipv4/udp", bytes)?;
            let what = format!(
                "{src}:{} -> {dst}:{} {}{}",
                u.header.src_port.0,
                u.header.dst_port.0,
                show(&contents(u.payload)),
                if u.header.checksum.0 == 0 { " (no checksum)" } else { "" },
            );
            Ok(("ipv4/udp", what))
        }
        ipv4::PROTO_ICMP if !p.header.fragment.is_fragment() => {
            let m = validate::<Icmpv4>("ipv4/icmp", bytes)?;
            let what = format!(
                "{src} -> {dst} type {} code {}",
                m.header.kind.0, m.header.code.0
            );
            Ok(("ipv4/icmp", what))
        }
        proto => Ok(("ipv4 (other)", format!("{src} -> {dst} protocol {proto}"))),
    }
}

fn ipv6(bytes: &[u8]) -> Outcome {
    let p = validate::<Ipv6Packet>("ipv6", bytes)?;
    let (src, dst) = (Ipv6Addr::from(p.header.src.0), Ipv6Addr::from(p.header.dst.0));
    match p.header.next_header.0 {
        ipv6::NEXT_UDP => {
            let u = validate::<Ipv6Udp>("ipv6/udp", bytes)?;
            let what = format!(
                "[{src}]:{} -> [{dst}]:{} {}",
                u.header.src_port.0,
                u.header.dst_port.0,
                show(&contents(u.payload)),
            );
            Ok(("ipv6/udp", what))
        }
        ipv6::NEXT_ICMPV6 => {
            let m = validate::<Icmpv6>("ipv6/icmp", bytes)?;
            let what = format!(
                "{src} -> {dst} type {} code {}",
                m.header.kind.0, m.header.code.0
            );
            Ok(("ipv6/icmp", what))
        }
        next => Ok(("ipv6 (other)", format!("{src} -> {dst} next header {next}"))),
    }
}

fn frame(data: &[u8]) -> Outcome {
    let f = validate::<Frame>("ethernet", data)?;
    let ether_type = f.header.tagging.ether_type.0;
    // `Untrusted` payloads are consumed by validation, and the harness may
    // try more than one decoder on the same bytes, so it takes the payload
    // from the raw frame. `Frame` accepted it, so it is exactly the bytes
    // after the 14-byte header (18 with a tag).
    let header_len = if f.header.tagging.vlan.is_some() { 18 } else { 14 };
    let payload = &data[header_len..];
    match ether_type {
        arp::ETHER_TYPE_ARP => {
            let a = validate::<Arp>("arp", payload)?;
            let p = a.packet;
            let what = format!(
                "{} {} -> {}",
                if p.op.0 == arp::OP_REQUEST { "who-has" } else { "reply" },
                Ipv4Addr::from(p.sender_ip.0),
                Ipv4Addr::from(p.target_ip.0),
            );
            Ok(("arp", what))
        }
        ipv4::ETHER_TYPE_IPV4 => ipv4(payload),
        ipv6::ETHER_TYPE_IPV6 => ipv6(payload),
        t => Ok(("ethernet (other)", format!("EtherType {t:#06x}"))),
    }
}

/// The frames of a pcap capture with Ethernet link type.
fn read_pcap(file: &[u8]) -> Result<Vec<&[u8]>, String> {
    let u32_at = |b: &[u8], i: usize, le: bool| {
        let w = [b[i], b[i + 1], b[i + 2], b[i + 3]];
        if le { u32::from_le_bytes(w) } else { u32::from_be_bytes(w) }
    };
    if file.len() < 24 {
        return Err("not a pcap file: too short".into());
    }
    let le = match u32_at(file, 0, true) {
        0xa1b2_c3d4 | 0xa1b2_3c4d => true,
        0xd4c3_b2a1 | 0x4d3c_b2a1 => false,
        _ => return Err("not a pcap file (pcapng is not supported)".into()),
    };
    if u32_at(file, 20, le) != 1 {
        return Err("not an Ethernet capture (link type is not 1)".into());
    }
    let mut frames = Vec::new();
    let mut i = 24;
    while i < file.len() {
        if file.len() - i < 16 {
            return Err(format!("truncated record header at byte {i}"));
        }
        let incl = u32_at(file, i + 8, le) as usize;
        let orig = u32_at(file, i + 12, le) as usize;
        i += 16;
        if file.len() - i < incl {
            return Err(format!("truncated record at byte {i}"));
        }
        if incl != orig {
            return Err(format!("frame at byte {i} was cut short by the snap length"));
        }
        frames.push(&file[i..i + incl]);
        i += incl;
    }
    Ok(frames)
}

fn main() {
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: net-pcap <file.pcap>");
        exit(2);
    };
    let file = std::fs::read(&path).unwrap_or_else(|e| {
        eprintln!("error: {path}: {e}");
        exit(2)
    });
    let frames = read_pcap(&file).unwrap_or_else(|e| {
        eprintln!("error: {path}: {e}");
        exit(2)
    });
    let mut accepted: BTreeMap<&str, usize> = BTreeMap::new();
    let mut rejected: BTreeMap<String, usize> = BTreeMap::new();
    for (n, data) in frames.iter().enumerate() {
        match frame(data) {
            Ok((layer, what)) => {
                println!("#{:<4} {:>4}B  ok      {layer:<16} {what}", n + 1, data.len());
                *accepted.entry(layer).or_default() += 1;
            }
            Err((layer, e)) => {
                println!("#{:<4} {:>4}B  REJECT  {layer:<16} {e:?}", n + 1, data.len());
                *rejected.entry(format!("{layer}: {e:?}")).or_default() += 1;
            }
        }
    }
    println!();
    println!("{} frames", frames.len());
    for (layer, n) in &accepted {
        println!("  accepted  {layer:<16} {n}");
    }
    for (why, n) in &rejected {
        println!("  REJECTED  {why:<16} {n}");
    }
    if !rejected.is_empty() {
        exit(1);
    }
}
