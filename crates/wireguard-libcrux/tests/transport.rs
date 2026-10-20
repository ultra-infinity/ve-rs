//! Transport data, with the libcrux primitives: encryption, decoding as a
//! message, and the receive checks.

use untrusted::Untrusted;
use wireguard::allowed_ips::AllowedIps;
use wireguard::message::Message;
use wireguard::replay::Replay;
use wireguard::transport::*;
use wireguard_libcrux::Libcrux;

/// An IPv4 packet from `src` with `payload_len` bytes of payload.
fn ipv4(src: [u8; 4], payload_len: usize) -> Vec<u8> {
    let mut p = vec![0u8; 20 + payload_len];
    p[0] = 0x45;
    p[2..4].copy_from_slice(&((20 + payload_len) as u16).to_be_bytes());
    p[8] = 64;
    p[9] = 17;
    p[12..16].copy_from_slice(&src);
    p[16..20].copy_from_slice(&[10, 0, 0, 2]);
    for (i, b) in p[20..].iter_mut().enumerate() {
        *b = i as u8;
    }
    let c = !net::inet::sum(0, &p[..20]);
    p[10..12].copy_from_slice(&c.to_be_bytes());
    p
}

struct Setup {
    key: [u8; 32],
    replay: Replay,
    table: AllowedIps,
}

fn setup() -> Setup {
    let mut table = AllowedIps::new();
    assert!(table.insert(false, u32::from_be_bytes([10, 0, 0, 0]) as u128, 24, 1));
    assert!(table.insert(true, 0xfd00 << 112, 16, 1));
    Setup {
        key: [7; 32],
        replay: Replay::new(),
        table,
    }
}

/// Encrypts `packet` with `counter`, decodes the message, and receives it.
fn round_trip(
    s: &mut Setup,
    counter: u64,
    packet: &[u8],
    tamper: Option<usize>,
) -> (Received, Vec<u8>) {
    let mut work = [0u8; 2048];
    let mut msg = [0u8; 2048];
    let n = encrypt(&Libcrux, &s.key, 99, counter, packet, &mut work, &mut msg).unwrap();
    assert_eq!(n, 32 + padded_len(packet.len()));
    if let Some(i) = tamper {
        msg[i] ^= 1;
    }
    let Ok(Message::Transport(t)) = Untrusted::new(&msg[..n]).validate::<Message>() else {
        panic!("not a transport message")
    };
    if tamper.is_none() {
        assert_eq!((t.header.receiver.0, t.header.counter.0), (99, counter));
    }
    // The counter as the message says, as a receiver would take it.
    let got = t.header.counter.0;
    let mut out = [0u8; 2048];
    let r = receive(
        &Libcrux,
        &s.key,
        &mut s.replay,
        &s.table,
        1,
        got,
        &msg[16..n],
        &mut out,
    );
    (r, out.to_vec())
}

#[test]
fn packets_round_trip_without_padding() {
    let mut s = setup();
    for (counter, len) in [(0, 0), (1, 5), (2, 12), (3, 1380)] {
        let p = ipv4([10, 0, 0, 9], len);
        let (r, out) = round_trip(&mut s, counter, &p, None);
        assert_eq!(r, Received::Packet(p.len()));
        assert_eq!(&out[..p.len()], &p[..]);
    }
}

#[test]
fn drops_replays_forgeries_and_strangers() {
    let mut s = setup();
    let p = ipv4([10, 0, 0, 9], 10);
    assert_eq!(round_trip(&mut s, 5, &p, None).0, Received::Packet(30));
    // The same counter again.
    assert_eq!(round_trip(&mut s, 5, &p, None).0, Received::Drop);
    // Any bit flipped in the encrypted part or the counter.
    for i in [8, 16, 40, 63] {
        assert_eq!(
            round_trip(&mut s, 6, &p, Some(i)).0,
            Received::Drop,
            "byte {i}"
        );
    }
    // ...which did not consume counter 6.
    assert_eq!(round_trip(&mut s, 6, &p, None).0, Received::Packet(30));
    // A source the peer is not allowed.
    let q = ipv4([192, 168, 0, 9], 10);
    assert_eq!(round_trip(&mut s, 7, &q, None).0, Received::Drop);
    // Not an IP packet.
    assert_eq!(round_trip(&mut s, 8, &[0x10; 20], None).0, Received::Drop);
}

#[test]
fn keepalives_and_ipv6() {
    let mut s = setup();
    assert_eq!(round_trip(&mut s, 0, &[], None).0, Received::Keepalive);
    let mut p = vec![0u8; 48];
    p[0] = 0x60;
    p[5] = 8;
    p[6] = 17;
    p[8] = 0xfd;
    p[24] = 0xfd;
    let (r, out) = round_trip(&mut s, 1, &p, None);
    assert_eq!(r, Received::Packet(48));
    assert_eq!(&out[..48], &p[..]);
    assert_eq!(
        inner(&p),
        Some(Inner {
            v6: true,
            src: 0xfd << 120,
            dst: 0xfd << 120,
            len: 48
        })
    );
}
