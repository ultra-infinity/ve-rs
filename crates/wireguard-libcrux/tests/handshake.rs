//! A full WireGuard handshake between two parties, with the libcrux
//! primitives, through message encoding and decoding.

use untrusted::{Untrusted, ValidationError};
use wireguard::crypto::Crypto;
use wireguard::message::Message;
use wireguard::noise::*;
use wireguard_libcrux::Libcrux;

struct Party {
    private: [u8; 32],
    public: [u8; 32],
}

fn party(seed: u8) -> Party {
    let private = [seed; 32];
    let mut public = [0u8; 32];
    Libcrux.x25519_public(&private, &mut public);
    Party { private, public }
}

fn decode(bytes: &[u8]) -> Result<Message<'_>, ValidationError> {
    Untrusted::new(bytes).validate::<Message>()
}

#[test]
fn initiator_and_responder_agree_on_keys() {
    let c = Libcrux;
    let (alice, bob) = (party(1), party(2));
    let psk = [9u8; 32];
    let ts = [0, 0, 0, 0, 0x60, 0, 0, 0, 0, 0, 0, 1];

    // Alice initiates; the message goes on the wire and is decoded by Bob.
    let (init, alice_state) = create_initiation(
        &c,
        &alice.private,
        &alice.public,
        &bob.public,
        &[3; 32],
        0x1111,
        &ts,
    )
    .unwrap();
    let bytes = init.encode();
    let Ok(Message::Initiation(init)) = decode(&bytes) else {
        panic!()
    };
    let st = consume_initiation_static(&c, &bob.private, &bob.public, &init).unwrap();
    assert_eq!(st.initiator_static, alice.public);
    let (bob_chain, got_ts) = consume_initiation_timestamp(&c, &bob.private, &st, &init).unwrap();
    assert_eq!(got_ts, ts);

    // Bob responds; Alice decodes and consumes the response.
    let (resp, bob_final) = create_response(
        &c,
        &bob_chain,
        &init.ephemeral,
        &st.initiator_static,
        &psk,
        &[4; 32],
        0x2222,
        0x1111,
    )
    .unwrap();
    let bytes = resp.encode();
    let Ok(Message::Response(resp)) = decode(&bytes) else {
        panic!()
    };
    assert_eq!((resp.sender.0, resp.receiver.0), (0x2222, 0x1111));
    let alice_final = consume_response(&c, &alice_state, &alice.private, &psk, &resp).unwrap();

    assert_eq!(alice_final, bob_final);
    let (a_send, a_recv) = transport_keys(&c, &alice_final);
    let (b_recv, b_send) = transport_keys(&c, &bob_final);
    assert_eq!((a_send, a_recv), (b_recv, b_send));
    assert_ne!(a_send, a_recv);
}

#[test]
fn rejects_tampering_and_wrong_keys() {
    let c = Libcrux;
    let (alice, bob, eve) = (party(1), party(2), party(5));
    let ts = [1; 12];
    let (init, alice_state) = create_initiation(
        &c,
        &alice.private,
        &alice.public,
        &bob.public,
        &[3; 32],
        1,
        &ts,
    )
    .unwrap();

    // Any change to the encrypted static key, or the ephemeral, is detected.
    let mut bad = init;
    bad.encrypted_static[0] ^= 1;
    assert!(consume_initiation_static(&c, &bob.private, &bob.public, &bad).is_none());
    let mut bad = init;
    bad.ephemeral[5] ^= 1;
    assert!(consume_initiation_static(&c, &bob.private, &bob.public, &bad).is_none());
    // Only Bob can open an initiation to Bob.
    assert!(consume_initiation_static(&c, &eve.private, &eve.public, &init).is_none());
    // A changed timestamp is detected too.
    let st = consume_initiation_static(&c, &bob.private, &bob.public, &init).unwrap();
    let mut bad = init;
    bad.encrypted_timestamp[3] ^= 1;
    assert!(consume_initiation_timestamp(&c, &bob.private, &st, &bad).is_none());

    // A response under another pre-shared key is rejected.
    let (chain, _) = consume_initiation_timestamp(&c, &bob.private, &st, &init).unwrap();
    let (resp, _) = create_response(
        &c,
        &chain,
        &init.ephemeral,
        &alice.public,
        &[1; 32],
        &[4; 32],
        2,
        1,
    )
    .unwrap();
    assert!(consume_response(&c, &alice_state, &alice.private, &[2; 32], &resp).is_none());
    assert!(consume_response(&c, &alice_state, &alice.private, &[1; 32], &resp).is_some());

    // A low-order ephemeral key is refused.
    let mut bad = init;
    bad.ephemeral = [0; 32];
    assert!(consume_initiation_static(&c, &bob.private, &bob.public, &bad).is_none());
}

#[test]
fn timestamps_compare_as_big_endian() {
    let a = [0, 0, 0, 0, 0x60, 0, 0, 0, 0, 0, 0, 2];
    let mut b = a;
    b[11] = 1;
    assert!(timestamp_after(&a, &b));
    assert!(!timestamp_after(&b, &a));
    assert!(!timestamp_after(&a, &a));
    b[0] = 1;
    assert!(timestamp_after(&b, &a));
}
