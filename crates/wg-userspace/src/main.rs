//! A userspace WireGuard interface around the verified sans-IO
//! [`wireguard::device::Device`], without the Rust standard library.
//!
//! ```text
//! wg-userspace <interface> <config file>   run the interface
//! wg-userspace genkey                      print a new private key
//! wg-userspace pubkey < private            print the public key
//! ```
//!
//! UDP is done with the verified `net` crate, not the kernel's sockets: every
//! IP packet the host receives comes in through a packet socket and is
//! validated with [`net::udp::Ipv4Udp`] / [`net::udp::Ipv6Udp`]; datagrams for
//! our port go to the device. Datagrams the device sends are built with
//! [`net::udp::encode_ipv4`] / [`net::udp::encode_ipv6`], proved to produce
//! packets those decoders accept, and sent whole through raw IP sockets (the
//! kernel still routes them and resolves neighbours).
//!
//! This program is not verified and contains no protocol logic: it moves
//! bytes between the operating system (packet and raw sockets, a TUN device,
//! the clocks and the kernel's randomness) and the device. The interface's
//! addresses, MTU and routes are set outside, with `ip`.

#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]
// Under test, the entry point is compiled out, and much of what it uses.
#![cfg_attr(test, allow(dead_code))]

mod config;
mod sys;

use config::{to_base64, Config};
use core::fmt::Write;
use core::net::SocketAddr;
use net::ipv4::Ipv4Addr;
use net::ipv6::Ipv6Addr;
use net::udp::{encode_ipv4, encode_ipv6, Ipv4Udp, Ipv6Udp};
use sys::{Fd, OsError, RawSockets, Stderr};
use untrusted::{Untrusted, Validate, ValidationError};
use wireguard::crypto::Crypto;
use wireguard::device::{Action, Device, Endpoint, Env, MAX_PACKET_LEN, MAX_PEERS};
use wireguard_libcrux::Libcrux;

/// Room for the largest packet, padded, plus the transport header and tag.
const BUF_LEN: usize = MAX_PACKET_LEN + 64;
/// Room for that, in an IPv6 packet with a UDP header.
const PKT_LEN: usize = BUF_LEN + 48;
const ETHER_TYPE_IPV4: u16 = 0x0800;
const ETHER_TYPE_IPV6: u16 = 0x86DD;

/// The bytes of a UDP payload, as they are: the device validates them.
struct Raw<'a>(&'a [u8]);

impl<'a> Validate<&'a [u8]> for Raw<'a> {
    type Err = ValidationError;
    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        Ok(Raw(input))
    }
}

/// The device's endpoint for a configured socket address.
fn endpoint(addr: SocketAddr) -> Endpoint {
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

/// Everything the main loop works with.
struct Runner {
    port: u16,
    raw: RawSockets,
    tun: Fd,
    sources: Sources,
    pkt: [u8; PKT_LEN],
}

impl Runner {
    /// Carries out what the device asked for.
    fn act(&mut self, a: Action, out: &[u8]) {
        match a {
            Action::None => {}
            Action::Send(e, n) => {
                if let Err(err) = self.send(&e, &out[..n]) {
                    let _ = writeln!(Stderr, "wg-userspace: send: {err}");
                }
            }
            Action::Deliver(n) => {
                if let Err(err) = self.tun.write(&out[..n]) {
                    let _ = writeln!(Stderr, "wg-userspace: deliver: {err}");
                }
            }
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
fn datagram_for(port: u16, ether_type: u16, packet: &[u8]) -> Option<(Endpoint, &[u8])> {
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

fn run(interface: &[u8], config: &Config) -> Result<(), OsError> {
    let c = Libcrux;
    let mut dev = Device::new(&c, &config.private);
    for p in &config.peers[..config.peer_count] {
        let Some(i) = dev.add_peer(
            &c,
            &p.public,
            &p.psk,
            p.persistent_keepalive * 1_000_000_000,
        ) else {
            let _ = writeln!(Stderr, "wg-userspace: a peer is configured twice");
            continue;
        };
        if let Some(e) = p.endpoint {
            dev.set_endpoint(i, &endpoint(e));
        }
        for &(v6, addr, len) in &p.allowed_ips[..p.allowed_count] {
            if !dev.allow(i, v6, addr, len) {
                let _ = writeln!(
                    Stderr,
                    "wg-userspace: allowed IP not accepted: {addr:x}/{len}"
                );
            }
        }
    }
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
    };
    let mut text = [0u8; 64];
    let _ = writeln!(
        Stderr,
        "wg-userspace: listening on port {}, public key {}",
        config.listen_port,
        to_base64(&dev.public, &mut text)
    );

    let mut buf = [0u8; PKT_LEN];
    let mut work = [0u8; BUF_LEN];
    let mut out = [0u8; BUF_LEN];
    loop {
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
                    runner.act(a, &out);
                }
            }
        }
        if local {
            let n = runner.tun.read(&mut buf)?;
            let a = dev.handle_packet(&c, &env()?, &buf[..n], &mut work, &mut out);
            runner.act(a, &out);
        }
        // The timers: until they have nothing more to do.
        loop {
            let a = dev.tick(&c, &env()?, &mut out);
            if a == Action::None {
                break;
            }
            runner.act(a, &out);
        }
    }
}

/// `genkey`: a new private key.
fn genkey() -> Result<(), OsError> {
    let mut k = [0u8; 32];
    sys::random(&mut k)?;
    let mut text = [0u8; 64];
    sys::write_stdout(to_base64(&k, &mut text).as_bytes());
    sys::write_stdout(b"\n");
    Ok(())
}

/// `pubkey`: the public key of the private key on standard input.
fn pubkey() -> Result<(), &'static str> {
    let mut input = [0u8; 256];
    let n = sys::read_stdin(&mut input).map_err(|e| e.what)?;
    let s = core::str::from_utf8(&input[..n]).map_err(|_| "not text")?;
    let k = config::key(s)?;
    let mut p = [0u8; 32];
    Libcrux.x25519_public(&k, &mut p);
    let mut text = [0u8; 64];
    sys::write_stdout(to_base64(&p, &mut text).as_bytes());
    sys::write_stdout(b"\n");
    Ok(())
}

/// The program, given its arguments.
fn main_with(args: &[&[u8]]) -> i32 {
    match args {
        [_, b"genkey"] => match genkey() {
            Ok(()) => 0,
            Err(e) => {
                let _ = writeln!(Stderr, "wg-userspace: {e}");
                1
            }
        },
        [_, b"pubkey"] => match pubkey() {
            Ok(()) => 0,
            Err(e) => {
                let _ = writeln!(Stderr, "wg-userspace: {e}");
                1
            }
        },
        [_, interface, path] => {
            let mut text = [0u8; 16384];
            let n = match sys::read_file(path, &mut text) {
                Ok(n) => n,
                Err(e) => {
                    let _ = writeln!(Stderr, "wg-userspace: reading the configuration: {e}");
                    return 1;
                }
            };
            let Ok(text) = core::str::from_utf8(&text[..n]) else {
                let _ = writeln!(Stderr, "wg-userspace: the configuration is not text");
                return 1;
            };
            let config = match Config::parse(text) {
                Ok(c) => c,
                Err(e) => {
                    let _ = writeln!(
                        Stderr,
                        "wg-userspace: configuration line {}: {}",
                        e.line, e.message
                    );
                    return 1;
                }
            };
            match run(interface, &config) {
                Ok(()) => 0,
                Err(e) => {
                    let _ = writeln!(Stderr, "wg-userspace: {e}");
                    1
                }
            }
        }
        _ => {
            let _ = writeln!(
                Stderr,
                "usage: wg-userspace <interface> <config> | genkey | pubkey"
            );
            2
        }
    }
}

/// The C entry point.
///
/// # Safety
///
/// `argv` must hold `argc` NUL-terminated strings, as the C runtime passes.
#[cfg(not(test))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn main(argc: i32, argv: *const *const core::ffi::c_char) -> i32 {
    let mut args: [&[u8]; 4] = [b""; 4];
    let n = (argc.max(0) as usize).min(args.len());
    for (i, arg) in args.iter_mut().enumerate().take(n) {
        // SAFETY: `argv` holds `argc` NUL-terminated strings.
        *arg = unsafe { core::ffi::CStr::from_ptr(*argv.add(i)) }.to_bytes();
    }
    if argc as usize > args.len() {
        return main_with(&[]);
    }
    main_with(&args[..n])
}

#[cfg(not(test))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    let _ = writeln!(Stderr, "wg-userspace: {info}");
    // SAFETY: ends the process.
    unsafe { libc::abort() }
}

/// The unwinding personality the precompiled `core` refers to. Panics abort
/// (see the workspace profiles), so nothing ever calls it.
#[cfg(not(test))]
#[unsafe(no_mangle)]
extern "C" fn rust_eh_personality() {}

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
}
