//! `diomede-pcap --list hosts.txt [--list ...] [--permissive] capture.pcap [--out kept.pcap]`:
//! runs every packet of a capture through the verified ad filter
//! (`diomede::filter`) and reports what it would block.
//!
//! - A DNS query for a listed domain (or a subdomain of one) is answered with
//!   NXDOMAIN, and a query for HTTPS or SVCB records of any other name with
//!   no records: the report shows the name, and `--out` writes the answer in
//!   place of the query.
//! - A TLS ClientHello to port 443 for a listed server name is reset, and the
//!   rest of that TCP connection dropped. A ClientHello may span several
//!   segments (browsers' post-quantum key shares make it longer than one), so
//!   the start of each connection is reassembled and checked with
//!   `classify_stream`.
//! - QUIC (UDP to port 443) and DNS over QUIC (UDP to 853) are dropped, and
//!   DNS over TLS (TCP to 853) is reset.
//!
//! `--permissive` keeps only the blocklist: QUIC, DNS over TLS or QUIC and
//! HTTPS records pass.
//!
//! Lists are hosts files (`0.0.0.0 ads.example`) or one domain per line;
//! `#` starts a comment, and `localhost` and the like are skipped. The tool
//! sorts them; `Blocklist::new` (verified) checks the result.
//!
//! This harness is not verified: it reads lists and captures, reassembles
//! TCP and prints, with plain `std` code. The verdicts come from the
//! verified `classify` and `classify_stream`.
//!
//! Captures may be Ethernet (link type 1) or raw IP (101). Exits with status
//! 2 on a malformed capture or list.

use diomede::blocklist::Blocklist;
use diomede::dns::Query;
use diomede::dns;
use diomede::filter::{classify, classify_stream, Policy, Verdict, DOT_PORT, STRICT};
use diomede::tls::{self, ClientHello};
use net::tcp::{Ipv4Tcp, Ipv6Tcp, TcpHeader};
use net::udp::{Ipv4Udp, Ipv6Udp};
use std::collections::{BTreeMap, HashMap};
use std::net::IpAddr;
use std::process::exit;
use untrusted::{Decode, Reader, Untrusted, ValidationError};

/// The longest stream start reassembled: a whole TLS record.
const MAX_RECORD: usize = 5 + 16384 + 2048;
/// The TCP SYN flag.
const SYN: u8 = 0x02;

/// The bytes left in an `Untrusted` slice.
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

/// Names that hosts files map to themselves rather than block.
const NOT_BLOCKED: &[&str] = &[
    "localhost",
    "localhost.localdomain",
    "local",
    "broadcasthost",
    "ip6-localhost",
    "ip6-loopback",
    "ip6-localnet",
    "ip6-mcastprefix",
    "ip6-allnodes",
    "ip6-allrouters",
    "ip6-allhosts",
];

/// `h` as a listed domain: lowercase, without a trailing dot, made of labels
/// of 1 to 63 letters, digits, `-` and `_`.
fn domain(h: &str) -> Option<Vec<u8>> {
    let h = h.trim_end_matches('.').to_ascii_lowercase();
    if h.is_empty() || h.len() > 253 || NOT_BLOCKED.contains(&h.as_str()) {
        return None;
    }
    if h.parse::<IpAddr>().is_ok() {
        return None;
    }
    let ok = h.split('.').all(|l| {
        !l.is_empty()
            && l.len() <= 63
            && l.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'-' || c == b'_')
    });
    ok.then(|| h.into_bytes())
}

/// The domains of a hosts file or domain list.
fn parse_list(text: &str) -> Vec<Vec<u8>> {
    let mut domains = Vec::new();
    for line in text.lines() {
        let line = line.split('#').next().unwrap_or("");
        let mut words = line.split_whitespace().peekable();
        // A hosts file line starts with an address.
        if words.peek().is_some_and(|w| w.parse::<IpAddr>().is_ok()) {
            words.next();
        }
        domains.extend(words.filter_map(domain));
    }
    domains
}

/// The storage of a blocklist: the domains sorted, without duplicates.
fn storage(mut domains: Vec<Vec<u8>>) -> (Vec<u8>, Vec<u32>) {
    domains.sort();
    domains.dedup();
    let mut data = Vec::new();
    let mut ends = Vec::new();
    for d in domains {
        data.extend_from_slice(&d);
        ends.push(data.len() as u32);
    }
    (data, ends)
}

/// A pcap capture: its header and records.
struct Capture<'a> {
    header: &'a [u8],
    little_endian: bool,
    link_type: u32,
    /// Each record's header and data.
    records: Vec<(&'a [u8], &'a [u8])>,
}

fn read_pcap(file: &[u8]) -> Result<Capture<'_>, String> {
    let u32_at = |b: &[u8], i: usize, le: bool| {
        let w = [b[i], b[i + 1], b[i + 2], b[i + 3]];
        if le {
            u32::from_le_bytes(w)
        } else {
            u32::from_be_bytes(w)
        }
    };
    if file.len() < 24 {
        return Err("not a pcap file: too short".into());
    }
    let le = match u32_at(file, 0, true) {
        0xa1b2_c3d4 | 0xa1b2_3c4d => true,
        0xd4c3_b2a1 | 0x4d3c_b2a1 => false,
        _ => return Err("not a pcap file (pcapng is not supported)".into()),
    };
    let link_type = u32_at(file, 20, le);
    if link_type != 1 && link_type != 101 {
        return Err(format!("link type {link_type} is not Ethernet (1) or raw IP (101)"));
    }
    let mut records = Vec::new();
    let mut i = 24;
    while i < file.len() {
        if file.len() - i < 16 {
            return Err(format!("truncated record header at byte {i}"));
        }
        let incl = u32_at(file, i + 8, le) as usize;
        if file.len() - i - 16 < incl {
            return Err(format!("truncated record at byte {i}"));
        }
        records.push((&file[i..i + 16], &file[i + 16..i + 16 + incl]));
        i += 16 + incl;
    }
    Ok(Capture { header: &file[..24], little_endian: le, link_type, records })
}

/// The link-layer header length of a frame carrying IP, if it does.
fn link_header_len(link_type: u32, frame: &[u8]) -> Option<usize> {
    if link_type == 101 {
        return Some(0);
    }
    if frame.len() < 14 {
        return None;
    }
    let (ether_type, len) = match u16::from_be_bytes([frame[12], frame[13]]) {
        0x8100 if frame.len() >= 18 => (u16::from_be_bytes([frame[16], frame[17]]), 18),
        t => (t, 14),
    };
    matches!(ether_type, 0x0800 | 0x86DD).then_some(len)
}

/// The name asked about by the DNS query in the UDP packet `ip`.
fn query_name(ip: &[u8]) -> String {
    let payload = match Untrusted::new(ip).validate::<Ipv4Udp>() {
        Ok(u) => u.payload,
        Err(_) => match Untrusted::new(ip).validate::<Ipv6Udp>() {
            Ok(u) => u.payload,
            Err(_) => return "?".into(),
        },
    };
    match payload.validate::<Query>() {
        Ok(q) => String::from_utf8_lossy(q.query.name.as_bytes()).into_owned(),
        Err(_) => "?".into(),
    }
}

/// The server name of the ClientHello at the start of `stream`.
fn server_name(stream: &[u8]) -> String {
    match Untrusted::new(stream).validate::<ClientHello>() {
        Ok(ClientHello { server_name: Some(n) }) => String::from_utf8_lossy(n.as_bytes()).into(),
        _ => "?".into(),
    }
}

/// A TCP segment: its connection (addresses and ports), header and data.
struct Segment {
    flow: (Vec<u8>, u16, Vec<u8>, u16),
    header: TcpHeader,
    data: Vec<u8>,
}

fn tcp_segment(ip: &[u8]) -> Option<Segment> {
    if let Ok(t) = Untrusted::new(ip).validate::<Ipv4Tcp>() {
        let (src, dst) = (t.ip.header.src.0.to_be_bytes(), t.ip.header.dst.0.to_be_bytes());
        let flow = (src.to_vec(), t.header.src_port.0, dst.to_vec(), t.header.dst_port.0);
        return Some(Segment { flow, header: t.header, data: contents(t.payload) });
    }
    if let Ok(t) = Untrusted::new(ip).validate::<Ipv6Tcp>() {
        let (src, dst) = (t.ip.header.src.0.to_be_bytes(), t.ip.header.dst.0.to_be_bytes());
        let flow = (src.to_vec(), t.header.src_port.0, dst.to_vec(), t.header.dst_port.0);
        return Some(Segment { flow, header: t.header, data: contents(t.payload) });
    }
    None
}

/// The start of a TCP connection, reassembled until it holds a TLS record.
#[derive(Default)]
struct Stream {
    /// The sequence number of the first byte of data.
    start: Option<u32>,
    /// Data by offset from `start`.
    pieces: BTreeMap<u32, Vec<u8>>,
    /// The packets carrying data, by index.
    packets: Vec<usize>,
    /// Whether it was checked (or cannot be).
    done: bool,
    /// The server name, if the connection is blocked.
    blocked: Option<String>,
}

impl Stream {
    /// The data received without gaps from the start.
    fn prefix(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for (&off, piece) in &self.pieces {
            let off = off as usize;
            if off > out.len() {
                break;
            }
            if off + piece.len() > out.len() {
                out.extend_from_slice(&piece[out.len() - off..]);
            }
        }
        out
    }

    /// Adds the segment `s` (packet `index`); checks the ClientHello once
    /// its record is complete. Returns whether the check just found it
    /// blocked.
    fn add(&mut self, index: usize, s: &Segment, list: &Blocklist) -> bool {
        let seq = s.header.seq.0;
        if s.header.flags.0 & SYN != 0 {
            self.start = Some(seq.wrapping_add(1));
        }
        if s.data.is_empty() || self.done {
            return false;
        }
        self.packets.push(index);
        let start = *self.start.get_or_insert(seq);
        let off = seq.wrapping_sub(start);
        if (off as usize) < MAX_RECORD {
            self.pieces.insert(off, s.data.clone());
        }
        let prefix = self.prefix();
        if prefix.len() < 5 {
            return false;
        }
        if prefix[0] != 22 {
            self.done = true;
            return false;
        }
        let need = 5 + u16::from_be_bytes([prefix[3], prefix[4]]) as usize;
        if prefix.len() < need {
            return false;
        }
        self.done = true;
        if classify_stream(&prefix[..need], list) {
            self.blocked = Some(server_name(&prefix[..need]));
            return true;
        }
        false
    }
}

/// The destination port of the UDP datagram in `ip`, if it is one.
fn udp_dst_port(ip: &[u8]) -> Option<u16> {
    if let Ok(u) = Untrusted::new(ip).validate::<Ipv4Udp>() {
        return Some(u.header.dst_port.0);
    }
    Untrusted::new(ip).validate::<Ipv6Udp>().ok().map(|u| u.header.dst_port.0)
}

/// The frame carrying `packet` back on the link `frame` came in on: the
/// Ethernet addresses swapped, if any.
fn back(link_len: usize, frame: &[u8], packet: &[u8]) -> Vec<u8> {
    let mut f = Vec::with_capacity(link_len + packet.len());
    if link_len > 0 {
        f.extend_from_slice(&frame[6..12]);
        f.extend_from_slice(&frame[0..6]);
        f.extend_from_slice(&frame[12..link_len]);
    }
    f.extend_from_slice(packet);
    f
}

/// What was blocked, by kind.
#[derive(Default)]
struct Counts {
    answered: usize,
    stripped: usize,
    tls: usize,
    quic: usize,
    dot: usize,
}

/// What happens to a packet.
enum Action {
    Keep,
    Drop,
    /// Dropped, and this frame sent back.
    Reply(Vec<u8>),
}

fn usage() -> ! {
    eprintln!(
        "usage: diomede-pcap --list FILE [--list FILE ...] [--permissive] CAPTURE.pcap [--out KEPT.pcap]"
    );
    exit(2)
}

fn main() {
    let mut lists = Vec::new();
    let mut capture = None;
    let mut out_path = None;
    let mut policy = STRICT;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--list" => lists.push(args.next().unwrap_or_else(|| usage())),
            "--out" => out_path = Some(args.next().unwrap_or_else(|| usage())),
            "--permissive" => {
                policy = Policy { block_quic: false, block_dot: false, strip_https_rr: false }
            }
            _ if capture.is_none() && !a.starts_with('-') => capture = Some(a),
            _ => usage(),
        }
    }
    let Some(capture) = capture else { usage() };
    if lists.is_empty() {
        usage();
    }

    let mut domains = Vec::new();
    for path in &lists {
        match std::fs::read_to_string(path) {
            Ok(text) => domains.extend(parse_list(&text)),
            Err(e) => {
                eprintln!("{path}: {e}");
                exit(2);
            }
        }
    }
    let (data, ends) = storage(domains);
    let Some(list) = Blocklist::new(&data, &ends) else {
        eprintln!("the blocklist is not well formed");
        exit(2);
    };
    println!("{} blocked domains", list.len());

    let file = std::fs::read(&capture).unwrap_or_else(|e| {
        eprintln!("{capture}: {e}");
        exit(2);
    });
    let cap = read_pcap(&file).unwrap_or_else(|e| {
        eprintln!("{capture}: {e}");
        exit(2);
    });

    let mut actions: Vec<Action> = Vec::with_capacity(cap.records.len());
    let mut streams: HashMap<(Vec<u8>, u16, Vec<u8>, u16), Stream> = HashMap::new();
    let mut out = vec![0u8; 65535];
    let mut counts = Counts::default();
    for (index, &(_, frame)) in cap.records.iter().enumerate() {
        let Some(link_len) = link_header_len(cap.link_type, frame) else {
            actions.push(Action::Keep);
            continue;
        };
        let ip = &frame[link_len..];
        let action = match classify(ip, &list, &policy, &mut out) {
            Verdict::Pass => Action::Keep,
            Verdict::Drop => {
                match (tcp_segment(ip), udp_dst_port(ip)) {
                    (Some(s), _) => {
                        println!("#{index:<6} tcp  port {:<35} dropped (no room to reset)", s.flow.3)
                    }
                    (None, Some(tls::PORT)) => {
                        println!("#{index:<6} quic {:<40} dropped", "");
                        counts.quic += 1;
                    }
                    (None, Some(DOT_PORT)) => {
                        println!("#{index:<6} doq  {:<40} dropped", "");
                        counts.dot += 1;
                    }
                    _ => println!("#{index:<6} dns  {:<40} dropped (no room to answer)", query_name(ip)),
                }
                Action::Drop
            }
            Verdict::Reply(n) => {
                let dns_at = if out[0] >> 4 == 4 { 28 } else { 48 };
                if out[dns_at + 3] % 16 == dns::NXDOMAIN {
                    println!("#{index:<6} dns  {:<40} answered NXDOMAIN", query_name(ip));
                    counts.answered += 1;
                } else {
                    println!("#{index:<6} dns  {:<40} answered: no HTTPS records", query_name(ip));
                    counts.stripped += 1;
                }
                Action::Reply(back(link_len, frame, &out[..n]))
            }
            Verdict::Reset(n) => {
                if let Some(s) = tcp_segment(ip) {
                    if s.flow.3 == tls::PORT {
                        let name = server_name(&s.data);
                        println!("#{index:<6} tls  {name:<40} reset");
                        counts.tls += 1;
                        // The rest of the connection goes too.
                        streams.entry(s.flow).or_default().blocked = Some(name);
                    } else {
                        println!("#{index:<6} dot  {:<40} reset", "");
                        counts.dot += 1;
                    }
                }
                Action::Reply(back(link_len, frame, &out[..n]))
            }
        };
        actions.push(action);
        // TLS connections: reassemble the start of each one.
        if let Some(s) = tcp_segment(ip) {
            if s.flow.3 == tls::PORT {
                let stream = streams.entry(s.flow.clone()).or_default();
                if stream.blocked.is_some() {
                    if !s.data.is_empty() && matches!(actions[index], Action::Keep) {
                        actions[index] = Action::Drop;
                    }
                } else if stream.add(index, &s, &list) {
                    let name = stream.blocked.clone().unwrap_or_default();
                    println!(
                        "#{index:<6} tls  {name:<40} reset (ClientHello in {} segments)",
                        stream.packets.len()
                    );
                    counts.tls += 1;
                    for &i in &stream.packets {
                        actions[i] = Action::Drop;
                    }
                }
            }
        }
    }

    let dropped = actions.iter().filter(|a| !matches!(a, Action::Keep)).count();
    println!(
        "{} packets: {} kept, {} dropped ({} DNS queries answered NXDOMAIN, {} without HTTPS \
         records, {} TLS connections blocked, {} QUIC and {} DNS over TLS/QUIC packets refused)",
        actions.len(),
        actions.len() - dropped,
        dropped,
        counts.answered,
        counts.stripped,
        counts.tls,
        counts.quic,
        counts.dot,
    );

    if let Some(path) = out_path {
        let mut w = cap.header.to_vec();
        let le = cap.little_endian;
        let u32_bytes = |v: u32| if le { v.to_le_bytes() } else { v.to_be_bytes() };
        for (&(header, frame), action) in cap.records.iter().zip(&actions) {
            match action {
                Action::Keep => {
                    w.extend_from_slice(header);
                    w.extend_from_slice(frame);
                }
                Action::Drop => {}
                Action::Reply(reply) => {
                    w.extend_from_slice(&header[..8]);
                    w.extend_from_slice(&u32_bytes(reply.len() as u32));
                    w.extend_from_slice(&u32_bytes(reply.len() as u32));
                    w.extend_from_slice(reply);
                }
            }
        }
        if let Err(e) = std::fs::write(&path, w) {
            eprintln!("{path}: {e}");
            exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_hosts_files_and_domain_lists() {
        let text = "# A list\n\
                    127.0.0.1 localhost\n\
                    0.0.0.0 Ads.Example.  # trailing comment\n\
                    0.0.0.0 tracker.io metrics.tracker.io\n\
                    :: ip6-localhost\n\
                    doubleclick.net\n\
                    bad..name\n\
                    1.2.3.4\n";
        let got: Vec<String> =
            parse_list(text).into_iter().map(|d| String::from_utf8(d).unwrap()).collect();
        assert_eq!(got, ["ads.example", "tracker.io", "metrics.tracker.io", "doubleclick.net"]);
    }

    #[test]
    fn builds_a_valid_list() {
        let domains = parse_list("b.com\na.com\nb.com\nab.com\n");
        let (data, ends) = storage(domains);
        let list = Blocklist::new(&data, &ends).unwrap();
        assert_eq!(list.len(), 3);
        assert!(list.blocked(b"x.ab.com"));
    }

    #[test]
    fn reassembles_out_of_order_data() {
        let mut s = Stream { start: Some(100), ..Stream::default() };
        s.pieces.insert(4, b"efg".to_vec());
        s.pieces.insert(0, b"abcd".to_vec());
        s.pieces.insert(9, b"xyz".to_vec());
        assert_eq!(s.prefix(), b"abcdefg");
        s.pieces.insert(7, b"hi".to_vec());
        assert_eq!(s.prefix(), b"abcdefghixyz");
    }
}
