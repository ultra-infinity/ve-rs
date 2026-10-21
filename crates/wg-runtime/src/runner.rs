//! The event loop around the verified device.
//!
//! UDP is done with the verified `net` crate, not the kernel's sockets: every
//! IP packet the host receives comes in through a packet socket and is
//! validated with [`net::udp::Ipv4Udp`] / [`net::udp::Ipv6Udp`]; datagrams for
//! our port go to the device. Datagrams the device sends are built with
//! [`net::udp::encode_ipv4`] / [`net::udp::encode_ipv6`], proved to produce
//! packets those decoders accept, and sent whole through raw IP sockets (the
//! kernel still routes them and resolves neighbours).
//!
//! Packets the device delivers (decrypted, from a peer allowed to send them)
//! go through an [`Inner`] hook before the TUN device: delivered, dropped, or
//! answered through the tunnel.
//!
//! Peers come from the configuration and from its peers file, if any. On
//! SIGHUP the peers file is read again: peers no longer listed (or listed
//! differently) are removed, new ones added.

use crate::config::{to_base64, Config, PeerConfig, NO_PEER};
use crate::sys::{self, Fd, OsError, RawSockets, Stderr};
use core::fmt::Write;
use core::net::SocketAddr;
use net::ipv4::Ipv4Addr;
use net::ipv6::Ipv6Addr;
use net::udp::{encode_ipv4, encode_ipv6, Ipv4Udp, Ipv6Udp};
use untrusted::{Untrusted, Validate, ValidationError};
use wireguard::device::{Action, Device, Endpoint, Env, MAX_PACKET_LEN, MAX_PEERS};
use wireguard_libcrux::Libcrux;

/// Room for the largest packet, padded, plus the transport header and tag.
pub const BUF_LEN: usize = MAX_PACKET_LEN + 64;
/// Room for that, in an IPv6 packet with a UDP header.
pub const PKT_LEN: usize = BUF_LEN + 48;
const ETHER_TYPE_IPV4: u16 = 0x0800;
const ETHER_TYPE_IPV6: u16 = 0x86DD;
/// The largest peers file.
const PEERS_FILE_LEN: usize = 256 * 1024;

/// What to do with a packet a peer sent, before it reaches the TUN device.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Hook {
    /// Write it to the TUN device.
    Deliver,
    /// Drop it.
    Drop,
    /// Drop it, and send the IP packet `reply[..n]` back through the tunnel,
    /// to the peer whose allowed IPs hold its destination.
    Reply(usize),
}

/// Code run on the packets the device delivers, and on events.
pub trait Inner {
    /// A packet from a peer, decrypted and checked by the device, about to
    /// be written to the TUN device at `now` (nanoseconds, monotonic).
    fn delivered(&mut self, packet: &[u8], now: u64, reply: &mut [u8]) -> Hook;
    /// SIGHUP arrived; the peers file was read again.
    fn reload(&mut self) {}
    /// A turn of the loop, at least every 100 ms.
    fn tick(&mut self, _now: u64) {}
}

/// No hook: every packet is delivered.
pub struct Plain;

impl Inner for Plain {
    fn delivered(&mut self, _packet: &[u8], _now: u64, _reply: &mut [u8]) -> Hook {
        Hook::Deliver
    }
}

/// The bytes of a UDP payload, as they are: the device validates them.
struct Raw<'a>(&'a [u8]);

impl<'a> Validate<&'a [u8]> for Raw<'a> {
    type Err = ValidationError;
    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        Ok(Raw(input))
    }
}

/// The device's endpoint for a configured socket address.
pub fn endpoint(addr: SocketAddr) -> Endpoint {
    let mut bytes = [0u8; 16];
    let v6 = match addr {
        SocketAddr::V4(a) => {
            bytes[..4].copy_from_slice(&a.ip().octets());
            false
        }
        SocketAddr::V6(a) => {
            bytes = a.ip().octets();
            true
        }
    };
    Endpoint {
        v6,
        addr: bytes,
        port: addr.port(),
    }
}

/// Where we send from, per endpoint: the kernel's routing answer, looked up
/// once.
struct Sources {
    entries: [(Endpoint, [u8; 16]); MAX_PEERS],
    count: usize,
    next: usize,
}

impl Sources {
    fn get(&mut self, e: &Endpoint) -> Result<[u8; 16], OsError> {
        if let Some((_, s)) = self.entries[..self.count].iter().find(|(x, _)| x == e) {
            return Ok(*s);
        }
        let mut s = [0u8; 16];
        if e.v6 {
            s = sys::source_v6(e.addr)?;
        } else {
            s[..4].copy_from_slice(&sys::source_v4(e.addr[..4].try_into().unwrap())?);
        }
        self.entries[self.next] = (*e, s);
        self.next = (self.next + 1) % MAX_PEERS;
        self.count = (self.count + 1).min(MAX_PEERS);
        Ok(s)
    }
}

/// The inputs of one call: the time and fresh randomness.
fn env() -> Result<Env, OsError> {
    let mut r = [0u8; 92];
    sys::random(&mut r)?;
    Ok(Env {
        now: sys::monotonic(),
        timestamp: sys::tai64n(),
        ephemeral: r[..32].try_into().unwrap(),
        index: u32::from_le_bytes(r[32..36].try_into().unwrap()),
        nonce: r[36..60].try_into().unwrap(),
        secret: r[60..92].try_into().unwrap(),
    })
}

/// Everything the loop works with, but the device.
struct Runner {
    port: u16,
    raw: RawSockets,
    tun: Fd,
    sources: Sources,
    pkt: [u8; PKT_LEN],
    reply: [u8; BUF_LEN],
    work: [u8; BUF_LEN],
    out: [u8; BUF_LEN],
}

impl Runner {
    /// Carries out what the device asked for; a delivered packet goes
    /// through `hook` first.
    fn act<H: Inner>(&mut self, dev: &mut Device, hook: &mut H, a: Action, out: &[u8]) {
        match a {
            Action::None => {}
            Action::Send(e, n) => {
                if let Err(err) = self.send(&e, &out[..n]) {
                    let _ = writeln!(Stderr, "send: {err}");
                }
            }
            Action::Deliver(n) => match hook.delivered(&out[..n], sys::monotonic(), &mut self.reply) {
                Hook::Deliver => {
                    if let Err(err) = self.tun.write(&out[..n]) {
                        let _ = writeln!(Stderr, "deliver: {err}");
                    }
                }
                Hook::Drop => {}
                Hook::Reply(m) => {
                    let Ok(env) = env() else { return };
                    let m = m.min(BUF_LEN);
                    let a = dev.handle_packet(&Libcrux, &env, &self.reply[..m], &mut self.work, &mut self.out);
                    if let Action::Send(e, k) = a {
                        let out = self.out;
                        if let Err(err) = self.send(&e, &out[..k]) {
                            let _ = writeln!(Stderr, "send: {err}");
                        }
                    }
                }
            },
        }
    }

    /// Sends `data` in a UDP datagram from our port to `e`.
    fn send(&mut self, e: &Endpoint, data: &[u8]) -> Result<(), OsError> {
        let src = self.sources.get(e)?;
        let too_long = OsError {
            what: "datagram too long",
            errno: libc::EMSGSIZE,
        };
        if e.v6 {
            let n = encode_ipv6(
                Ipv6Addr(u128::from_be_bytes(src)),
                Ipv6Addr(u128::from_be_bytes(e.addr)),
                self.port,
                e.port,
                data,
                &mut self.pkt,
            )
            .ok_or(too_long)?;
            self.raw.send_v6(e.addr, &self.pkt[..n])
        } else {
            let dst: [u8; 4] = e.addr[..4].try_into().unwrap();
            let n = encode_ipv4(
                Ipv4Addr(u32::from_be_bytes(src[..4].try_into().unwrap())),
                Ipv4Addr(u32::from_be_bytes(dst)),
                self.port,
                e.port,
                data,
                &mut self.pkt,
            )
            .ok_or(too_long)?;
            self.raw.send_v4(dst, &self.pkt[..n])
        }
    }
}

/// The UDP datagram to `port` in the IP packet `packet` (of EtherType
/// `ether_type`), validated by `net`: its source and payload.
pub fn datagram_for(port: u16, ether_type: u16, packet: &[u8]) -> Option<(Endpoint, &[u8])> {
    if ether_type == ETHER_TYPE_IPV4 {
        let u = Untrusted::new(packet).validate::<Ipv4Udp>().ok()?;
        if u.header.dst_port.0 != port {
            return None;
        }
        let mut addr = [0u8; 16];
        addr[..4].copy_from_slice(&u.ip.header.src.0.to_be_bytes());
        let from = Endpoint {
            v6: false,
            addr,
            port: u.header.src_port.0,
        };
        Some((from, u.payload.validate::<Raw>().ok()?.0))
    } else if ether_type == ETHER_TYPE_IPV6 {
        let u = Untrusted::new(packet).validate::<Ipv6Udp>().ok()?;
        if u.header.dst_port.0 != port {
            return None;
        }
        let from = Endpoint {
            v6: true,
            addr: u.ip.header.src.0.to_be_bytes(),
            port: u.header.src_port.0,
        };
        Some((from, u.payload.validate::<Raw>().ok()?.0))
    } else {
        None
    }
}

/// Writes `what` and the peer's public key to standard error.
fn log_peer(what: &str, public: &[u8; 32]) {
    let mut text = [0u8; 64];
    let _ = writeln!(Stderr, "peer {} {what}", to_base64(public, &mut text));
}

/// The peers currently configured in the device, by slot: what each was
/// added with.
pub struct Applied {
    peers: [PeerConfig; MAX_PEERS],
}

impl Applied {
    pub const fn new() -> Applied {
        Applied {
            peers: [NO_PEER; MAX_PEERS],
        }
    }
}

impl Default for Applied {
    fn default() -> Self {
        Applied::new()
    }
}

/// Makes the device's peers those of `wanted` (in order; a key listed twice
/// is taken once): removes the others and those configured differently,
/// adds the new ones.
pub fn sync_peers(dev: &mut Device, applied: &mut Applied, wanted: &[&[PeerConfig]]) {
    let is_wanted = |p: &PeerConfig| wanted.iter().any(|w| w.iter().any(|q| q == p));
    for i in 0..dev.peer_count {
        if dev.peers[i].enabled && !is_wanted(&applied.peers[i]) {
            let public = dev.peers[i].public;
            if dev.remove_peer(i) {
                applied.peers[i] = NO_PEER;
                log_peer("removed", &public);
            }
        }
    }
    for p in wanted.iter().flat_map(|w| w.iter()) {
        let present =
            dev.peers[..dev.peer_count].iter().any(|d| d.enabled && d.public == p.public);
        if present {
            continue;
        }
        let Some(i) = dev.add_peer(&Libcrux, &p.public, &p.psk, p.persistent_keepalive * 1_000_000_000)
        else {
            log_peer("not added: the device is full", &p.public);
            continue;
        };
        if let Some(e) = p.endpoint {
            dev.set_endpoint(i, &endpoint(e));
        }
        for &(v6, addr, len) in &p.allowed_ips[..p.allowed_count] {
            if !dev.allow(i, v6, addr, len) {
                let _ = writeln!(Stderr, "allowed IP not accepted: {addr:x}/{len}");
            }
        }
        applied.peers[i] = *p;
        log_peer("added", &p.public);
    }
}

/// Reads and parses the peers file `path`.
fn read_peers(path: &[u8], text: &mut [u8; PEERS_FILE_LEN]) -> Option<Config> {
    let n = match sys::read_file(path, text) {
        Ok(n) => n,
        Err(e) => {
            let _ = writeln!(Stderr, "reading the peers file: {e}");
            return None;
        }
    };
    let Ok(s) = core::str::from_utf8(&text[..n]) else {
        let _ = writeln!(Stderr, "the peers file is not text");
        return None;
    };
    match Config::parse_peers(s) {
        Ok(c) => Some(c),
        Err(e) => {
            let _ = writeln!(Stderr, "peers file line {}: {}", e.line, e.message);
            None
        }
    }
}

/// Runs the interface `interface` with `config` until an OS error, passing
/// delivered packets through `hook`.
pub fn run<H: Inner>(interface: &[u8], config: &Config, hook: &mut H) -> Result<(), OsError> {
    let c = Libcrux;
    let mut dev = Device::new(&c, &config.private);
    let mut applied = Applied::new();
    let mut text = [0u8; PEERS_FILE_LEN];
    let mut extra = Config::parse_peers("").ok();
    if let Some(path) = config.peers_file() {
        extra = read_peers(path, &mut text).or(extra);
    }
    let file_peers = |e: &Option<Config>| -> ([PeerConfig; MAX_PEERS], usize) {
        match e {
            Some(e) => (e.peers, e.peer_count),
            None => ([NO_PEER; MAX_PEERS], 0),
        }
    };
    {
        let (fp, fc) = file_peers(&extra);
        sync_peers(&mut dev, &mut applied, &[&config.peers[..config.peer_count], &fp[..fc]]);
    }
    sys::catch_hangup()?;
    let packets = sys::packet_socket()?;
    let _reserved = sys::reserve_port(config.listen_port)?;
    let (tun, tun_index) = sys::open_tun(interface)?;
    let mut runner = Runner {
        port: config.listen_port,
        raw: RawSockets::open()?,
        tun,
        sources: Sources {
            entries: [(endpoint(SocketAddr::from(([0u8; 4], 0))), [0; 16]); MAX_PEERS],
            count: 0,
            next: 0,
        },
        pkt: [0; PKT_LEN],
        reply: [0; BUF_LEN],
        work: [0; BUF_LEN],
        out: [0; BUF_LEN],
    };
    let mut key = [0u8; 64];
    let _ = writeln!(
        Stderr,
        "listening on port {}, public key {}",
        config.listen_port,
        to_base64(&dev.public, &mut key)
    );

    let mut buf = [0u8; PKT_LEN];
    let mut work = [0u8; BUF_LEN];
    let mut out = [0u8; BUF_LEN];
    loop {
        if sys::hangup() {
            if let Some(path) = config.peers_file() {
                if let Some(e) = read_peers(path, &mut text) {
                    let (fp, fc) = file_peers(&Some(e));
                    sync_peers(&mut dev, &mut applied, &[&config.peers[..config.peer_count], &fp[..fc]]);
                }
            }
            hook.reload();
        }
        let (net, local) = sys::poll2(&packets, &runner.tun, 100)?;
        if net {
            while let Some(r) = sys::recv_packet(&packets, &mut buf)? {
                // Our own packets, and those of the tunnel itself, are not
                // for the device.
                if r.outgoing || r.ifindex == tun_index {
                    continue;
                }
                if let Some((from, data)) = datagram_for(runner.port, r.ether_type, &buf[..r.len]) {
                    let a = dev.handle_datagram(&c, &env()?, &from, false, data, &mut out);
                    runner.act(&mut dev, hook, a, &out);
                }
            }
        }
        if local {
            let n = runner.tun.read(&mut buf)?;
            let a = dev.handle_packet(&c, &env()?, &buf[..n], &mut work, &mut out);
            runner.act(&mut dev, hook, a, &out);
        }
        // The timers: until they have nothing more to do.
        loop {
            let a = dev.tick(&c, &env()?, &mut out);
            if a == Action::None {
                break;
            }
            runner.act(&mut dev, hook, a, &out);
        }
        hook.tick(sys::monotonic());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_datagrams_to_our_port() {
        let mut pkt = [0u8; 128];
        let n = encode_ipv4(
            Ipv4Addr(0x0a00_0001),
            Ipv4Addr(0x0a00_0002),
            4000,
            51820,
            b"hi",
            &mut pkt,
        )
        .unwrap();
        let (from, data) = datagram_for(51820, ETHER_TYPE_IPV4, &pkt[..n]).unwrap();
        assert_eq!(from.addr[..4], [10, 0, 0, 1]);
        assert_eq!((from.v6, from.port, data), (false, 4000, &b"hi"[..]));
        assert!(datagram_for(51821, ETHER_TYPE_IPV4, &pkt[..n]).is_none());
        let n = encode_ipv6(Ipv6Addr(1), Ipv6Addr(2), 4000, 51820, b"hi", &mut pkt).unwrap();
        let (from, data) = datagram_for(51820, ETHER_TYPE_IPV6, &pkt[..n]).unwrap();
        assert_eq!((from.v6, from.addr[15], data), (true, 1, &b"hi"[..]));
        pkt[n - 1] ^= 1;
        assert!(datagram_for(51820, ETHER_TYPE_IPV6, &pkt[..n]).is_none());
    }

    #[test]
    fn syncs_peers() {
        use wireguard::crypto::Crypto;
        let c = Libcrux;
        let mut dev = Box::new(Device::new(&c, &[1; 32]));
        let mut applied = Box::new(Applied::new());
        let peer = |k: u8, ip: u128| {
            let mut p = NO_PEER;
            c.x25519_public(&[k; 32], &mut p.public);
            p.allowed_ips[0] = (false, ip, 32);
            p.allowed_count = 1;
            p
        };
        let (a, b, b2) = (peer(2, 10), peer(3, 11), peer(3, 12));
        sync_peers(&mut dev, &mut applied, &[&[a, b]]);
        assert_eq!(dev.peer_count, 2);
        assert_eq!(dev.allowed_ips.lookup(false, 11), Some(1));
        // b is configured differently: removed and added again, in its slot.
        sync_peers(&mut dev, &mut applied, &[&[a], &[b2]]);
        assert_eq!(dev.peer_count, 2);
        assert_eq!(dev.allowed_ips.lookup(false, 11), None);
        assert_eq!(dev.allowed_ips.lookup(false, 12), Some(1));
        // a goes.
        sync_peers(&mut dev, &mut applied, &[&[b2]]);
        assert!(!dev.peers[0].enabled);
        assert_eq!(dev.allowed_ips.lookup(false, 10), None);
    }
}
