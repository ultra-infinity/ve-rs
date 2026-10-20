//! Two devices talking through their datagrams, with the libcrux primitives:
//! handshakes, data both ways, timers, cookies, and what is dropped.

use wireguard::crypto::Crypto;
use wireguard::device::*;
use wireguard_libcrux::Libcrux;

const SECOND: u64 = 1_000_000_000;

/// An IPv4 packet from `src` to `dst` with `payload_len` bytes of payload.
fn ipv4(src: [u8; 4], dst: [u8; 4], payload_len: usize) -> Vec<u8> {
    let mut p = vec![0u8; 20 + payload_len];
    p[0] = 0x45;
    p[2..4].copy_from_slice(&((20 + payload_len) as u16).to_be_bytes());
    p[8] = 64;
    p[9] = 17;
    p[12..16].copy_from_slice(&src);
    p[16..20].copy_from_slice(&dst);
    for (i, b) in p[20..].iter_mut().enumerate() {
        *b = i as u8;
    }
    let c = !net::inet::sum(0, &p[..20]);
    p[10..12].copy_from_slice(&c.to_be_bytes());
    p
}

fn v4(a: [u8; 4]) -> u128 {
    u32::from_be_bytes(a) as u128
}

fn endpoint(last: u8) -> Endpoint {
    let mut addr = [0u8; 16];
    addr[..4].copy_from_slice(&[192, 168, 0, last]);
    Endpoint {
        v6: false,
        addr,
        port: 51820,
    }
}

/// A device, its address, and a counter for fresh randomness.
struct Node {
    dev: Box<Device>,
    at: Endpoint,
    seed: u8,
    time: u64,
}

impl Node {
    fn env(&mut self) -> Env {
        self.seed = self.seed.wrapping_add(1);
        let s = self.seed;
        // TAI64N: seconds, then nanoseconds, big-endian.
        let mut timestamp = [0u8; 12];
        timestamp[..8].copy_from_slice(&(0x4000_0000_0000_0000u64 + self.time / SECOND).to_be_bytes());
        timestamp[8..].copy_from_slice(&((self.time % SECOND) as u32).to_be_bytes());
        Env {
            now: self.time,
            timestamp,
            ephemeral: [s; 32],
            index: 1000 * self.at.addr[3] as u32 + s as u32,
            nonce: [s; 24],
            secret: [s ^ 0x55; 32],
        }
    }

    fn send_packet(&mut self, packet: &[u8]) -> (Action, Vec<u8>) {
        let env = self.env();
        let mut work = vec![0u8; 2048];
        let mut out = vec![0u8; 2048];
        let a = self.dev.handle_packet(&Libcrux, &env, packet, &mut work, &mut out);
        (a, out)
    }

    fn receive(&mut self, from: &Endpoint, bytes: &[u8], under_load: bool) -> (Action, Vec<u8>) {
        let env = self.env();
        let mut out = vec![0u8; 2048];
        let a = self
            .dev
            .handle_datagram(&Libcrux, &env, from, under_load, bytes, &mut out);
        (a, out)
    }

    fn tick(&mut self) -> (Action, Vec<u8>) {
        let env = self.env();
        let mut out = vec![0u8; 2048];
        let a = self.dev.tick(&Libcrux, &env, &mut out);
        (a, out)
    }
}

/// Alice (10.0.0.1, at .1) and Bob (10.0.0.2, at .2), each allowing the
/// other's /32; Alice knows Bob's endpoint.
fn pair() -> (Node, Node) {
    let c = Libcrux;
    let (ka, kb) = ([1u8; 32], [2u8; 32]);
    let mut pa = [0u8; 32];
    let mut pb = [0u8; 32];
    c.x25519_public(&ka, &mut pa);
    c.x25519_public(&kb, &mut pb);
    let psk = [9u8; 32];
    let mut a = Box::new(Device::new(&c, &ka));
    let mut b = Box::new(Device::new(&c, &kb));
    let ia = a.add_peer(&c, &pb, &psk, 0).unwrap();
    let ib = b.add_peer(&c, &pa, &psk, 0).unwrap();
    assert!(a.allow(ia, false, v4([10, 0, 0, 2]), 32));
    assert!(b.allow(ib, false, v4([10, 0, 0, 1]), 32));
    a.set_endpoint(ia, &endpoint(2));
    (
        Node {
            dev: a,
            at: endpoint(1),
            seed: 0,
            time: 1000 * SECOND,
        },
        Node {
            dev: b,
            at: endpoint(2),
            seed: 100,
            time: 1000 * SECOND,
        },
    )
}

fn sent(a: Action, to: &Endpoint) -> usize {
    match a {
        Action::Send(e, n) => {
            assert_eq!(&e, to);
            n
        }
        other => panic!("expected a datagram, got {other:?}"),
    }
}

/// Runs a handshake initiated by Alice's first packet; returns the
/// keepalive Alice sends to confirm it.
fn handshake(a: &mut Node, b: &mut Node) {
    let packet = ipv4([10, 0, 0, 1], [10, 0, 0, 2], 10);
    let (act, init) = a.send_packet(&packet);
    let n = sent(act, &b.at);
    assert_eq!(n, 148);
    let (act, resp) = b.receive(&a.at.clone(), &init[..n], false);
    let n = sent(act, &a.at);
    assert_eq!(n, 92);
    let (act, ka) = a.receive(&b.at.clone(), &resp[..n], false);
    let n = sent(act, &b.at);
    assert_eq!(n, 32);
    let (act, _) = b.receive(&a.at.clone(), &ka[..n], false);
    assert_eq!(act, Action::None);
}

/// Sends `packet` from `x` to `y`, and returns what `y` does with it.
fn data(x: &mut Node, y: &mut Node, packet: &[u8]) -> (Action, Vec<u8>) {
    let (act, msg) = x.send_packet(packet);
    let n = sent(act, &y.at);
    let from = x.at;
    y.receive(&from, &msg[..n], false)
}

#[test]
fn handshake_then_data_both_ways() {
    let (mut a, mut b) = pair();
    handshake(&mut a, &mut b);
    let p = ipv4([10, 0, 0, 1], [10, 0, 0, 2], 100);
    let (act, out) = data(&mut a, &mut b, &p);
    assert_eq!(act, Action::Deliver(p.len()));
    assert_eq!(&out[..p.len()], &p[..]);
    // Bob confirmed the session on Alice's keepalive, so he can send.
    let q = ipv4([10, 0, 0, 2], [10, 0, 0, 1], 33);
    let (act, out) = data(&mut b, &mut a, &q);
    assert_eq!(act, Action::Deliver(q.len()));
    assert_eq!(&out[..q.len()], &q[..]);
}

#[test]
fn drops_replays_and_spoofed_sources() {
    let (mut a, mut b) = pair();
    handshake(&mut a, &mut b);
    let p = ipv4([10, 0, 0, 1], [10, 0, 0, 2], 20);
    let (act, msg) = a.send_packet(&p);
    let n = sent(act, &b.at);
    let from = a.at;
    assert_eq!(b.receive(&from, &msg[..n], false).0, Action::Deliver(p.len()));
    assert_eq!(b.receive(&from, &msg[..n], false).0, Action::None);
    // Alice may send to 10.0.0.2, but Bob only accepts 10.0.0.1 from her.
    a.dev.allow(0, false, v4([10, 0, 0, 0]), 24);
    let spoofed = ipv4([10, 0, 0, 7], [10, 0, 0, 2], 20);
    assert_eq!(data(&mut a, &mut b, &spoofed).0, Action::None);
    // Packets to nowhere are not sent.
    let lost = ipv4([10, 0, 0, 1], [10, 9, 9, 9], 20);
    assert_eq!(a.send_packet(&lost).0, Action::None);
}

#[test]
fn initiations_are_rate_limited_and_retried() {
    let (mut a, b) = pair();
    let p = ipv4([10, 0, 0, 1], [10, 0, 0, 2], 10);
    assert_eq!(sent(a.send_packet(&p).0, &b.at), 148);
    // No response: no new initiation before REKEY_TIMEOUT...
    a.time += REKEY_TIMEOUT - 1;
    assert_eq!(a.send_packet(&p).0, Action::None);
    assert_eq!(a.tick().0, Action::None);
    // ...then the timer retries.
    a.time += 1;
    assert_eq!(sent(a.tick().0, &b.at), 148);
    assert_eq!(a.tick().0, Action::None);
    // Attempts stop after REKEY_ATTEMPT_TIME.
    a.time += REKEY_ATTEMPT_TIME;
    assert_eq!(a.tick().0, Action::None);
    a.time += REKEY_TIMEOUT;
    assert_eq!(a.tick().0, Action::None);
}

#[test]
fn keys_expire_and_rekey() {
    let (mut a, mut b) = pair();
    handshake(&mut a, &mut b);
    // After REKEY_AFTER_TIME, the initiator still sends but asks for a
    // handshake at the next tick.
    a.time += REKEY_AFTER_TIME;
    b.time += REKEY_AFTER_TIME;
    let p = ipv4([10, 0, 0, 1], [10, 0, 0, 2], 10);
    assert_eq!(data(&mut a, &mut b, &p).0, Action::Deliver(p.len()));
    let (act, init) = a.tick();
    assert_eq!(sent(act, &b.at), 148);
    let from = a.at;
    let (act, resp) = b.receive(&from, &init[..148], false);
    assert_eq!(sent(act, &a.at), 92);
    let from = b.at;
    let (act, ka) = a.receive(&from, &resp[..92], false);
    let n = sent(act, &b.at);
    let from = a.at;
    assert_eq!(b.receive(&from, &ka[..n], false).0, Action::None);
    assert_eq!(data(&mut a, &mut b, &p).0, Action::Deliver(p.len()));
    // After REJECT_AFTER_TIME without a handshake, nothing is sent under
    // the old keys: a packet starts a handshake instead.
    a.time += REJECT_AFTER_TIME;
    assert_eq!(sent(a.send_packet(&p).0, &b.at), 148);
}

#[test]
fn keepalives() {
    let (mut a, mut b) = pair();
    handshake(&mut a, &mut b);
    let p = ipv4([10, 0, 0, 1], [10, 0, 0, 2], 10);
    assert_eq!(data(&mut a, &mut b, &p).0, Action::Deliver(p.len()));
    // Bob received data and sent nothing: after KEEPALIVE_TIMEOUT he sends a
    // keepalive, once.
    b.time += KEEPALIVE_TIMEOUT - 1;
    assert_eq!(b.tick().0, Action::None);
    b.time += 1;
    let (act, ka) = b.tick();
    let n = sent(act, &a.at);
    assert_eq!(n, 32);
    assert_eq!(b.tick().0, Action::None);
    let from = b.at;
    assert_eq!(a.receive(&from, &ka[..n], false).0, Action::None);
}

#[test]
fn cookies_under_load() {
    let (mut a, mut b) = pair();
    let p = ipv4([10, 0, 0, 1], [10, 0, 0, 2], 10);
    let (act, init) = a.send_packet(&p);
    assert_eq!(sent(act, &b.at), 148);
    // Bob is under load: the initiation has no mac2, so he answers with a
    // cookie reply.
    let from = a.at;
    let (act, reply) = b.receive(&from, &init[..148], true);
    assert_eq!(sent(act, &a.at), 64);
    let from = b.at;
    assert_eq!(a.receive(&from, &reply[..64], false).0, Action::None);
    // Alice's next initiation carries the cookie, and gets through.
    a.time += REKEY_TIMEOUT;
    let (act, init) = a.tick();
    assert_eq!(sent(act, &b.at), 148);
    let from = a.at;
    let (act, _) = b.receive(&from, &init[..148], true);
    assert_eq!(sent(act, &a.at), 92);
    // From another address the cookie is wrong.
    let elsewhere = endpoint(9);
    let (act, _) = b.receive(&elsewhere, &init[..148], true);
    assert_eq!(sent(act, &elsewhere), 64);
}

#[test]
fn rejects_bad_handshakes() {
    let (mut a, mut b) = pair();
    let p = ipv4([10, 0, 0, 1], [10, 0, 0, 2], 10);
    let (act, init) = a.send_packet(&p);
    assert_eq!(sent(act, &b.at), 148);
    let from = a.at;
    let mut bad = init[..148].to_vec();
    bad[20] ^= 1;
    assert_eq!(b.receive(&from, &bad, false).0, Action::None);
    // A replayed initiation (same timestamp) is answered only once.
    assert_eq!(sent(b.receive(&from, &init[..148], false).0, &a.at), 92);
    assert_eq!(b.receive(&from, &init[..148], false).0, Action::None);
    // Garbage is ignored.
    assert_eq!(b.receive(&from, &[1, 2, 3], false).0, Action::None);
    assert_eq!(b.receive(&from, &[4, 0, 0, 0, 1], false).0, Action::None);
}
