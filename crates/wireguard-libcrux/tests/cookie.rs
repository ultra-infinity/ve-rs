//! MACs and cookie replies, with the libcrux primitives.

use wireguard::cookie::*;
use wireguard::crypto::Crypto;
use wireguard::message::{Initiation, INITIATION_LEN};
use wireguard_libcrux::Libcrux;

fn public(seed: u8) -> [u8; 32] {
    let mut p = [0u8; 32];
    Libcrux.x25519_public(&[seed; 32], &mut p);
    p
}

fn message() -> [u8; INITIATION_LEN] {
    Initiation {
        sender: untrusted::LittleEndian(7),
        ephemeral: [1; 32],
        encrypted_static: [2; 48],
        encrypted_timestamp: [3; 28],
        mac1: [0; 16],
        mac2: [0; 16],
    }
    .encode()
}

#[test]
fn macs_check_out() {
    let c = Libcrux;
    let key = mac1_key(&c, &public(2));
    let mut msg = message();
    let mac1 = add_macs(&c, &mut msg, &key, None);
    assert_eq!(&msg[116..132], &mac1);
    assert_eq!(&msg[132..], &[0; 16]);
    assert!(check_mac1(&c, &msg, &key));
    assert!(!check_mac1(&c, &msg, &mac1_key(&c, &public(3))));
    // Any change before mac1 invalidates it.
    for i in [0, 4, 50, 115] {
        let mut bad = msg;
        bad[i] ^= 1;
        assert!(!check_mac1(&c, &bad, &key), "byte {i}");
    }
    // With a cookie, mac2 covers mac1 too.
    let cookie = [9u8; 16];
    let mut msg = message();
    add_macs(&c, &mut msg, &key, Some(cookie));
    assert!(check_mac1(&c, &msg, &key));
    assert!(check_mac2(&c, &msg, &cookie));
    assert!(!check_mac2(&c, &msg, &[8; 16]));
    let mut bad = msg;
    bad[120] ^= 1;
    assert!(!check_mac2(&c, &bad, &cookie));
    assert!(!check_mac1(&c, &msg[..31], &key));
}

#[test]
fn cookie_replies() {
    let c = Libcrux;
    let responder = public(2);
    let cookie = make_cookie(&c, &[5; 32], &[192, 168, 0, 1, 0xca, 0x6c]);
    assert_ne!(
        cookie,
        make_cookie(&c, &[5; 32], &[192, 168, 0, 2, 0xca, 0x6c])
    );
    assert_ne!(
        cookie,
        make_cookie(&c, &[6; 32], &[192, 168, 0, 1, 0xca, 0x6c])
    );
    let mac1 = [4u8; 16];
    let key = cookie_key(&c, &responder);
    let reply = create_cookie_reply(&c, &key, 7, &[1; 24], &cookie, &mac1);
    assert_eq!(consume_cookie_reply(&c, &key, &reply, &mac1), Some(cookie));
    // Only for the message it answers, and only from that responder.
    assert_eq!(consume_cookie_reply(&c, &key, &reply, &[5; 16]), None);
    assert_eq!(
        consume_cookie_reply(&c, &cookie_key(&c, &public(3)), &reply, &mac1),
        None
    );
}
