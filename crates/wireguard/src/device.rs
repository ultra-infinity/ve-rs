//! The sans-IO WireGuard device: peers, sessions and timers (whitepaper
//! sections 5 and 6).
//!
//! The device does no I/O. The caller hands it the current time, fresh
//! randomness ([`Env`]) and the bytes that arrived, and it returns an
//! [`Action`]: a datagram to send, an IP packet to deliver, or nothing. Each
//! call produces at most one action; [`Device::tick`] is called periodically,
//! and repeatedly until it returns [`Action::None`], to run the timers.
//!
//! Each peer has up to three sessions (keypairs): `current`, used to send;
//! `previous`, kept to receive packets still in flight after a new handshake;
//! and `next`, a session the peer initiated, which becomes `current` when the
//! first data arrives under it (the responder may not send first). A
//! keypair is used, to send or to receive, only while it is younger than
//! [`REJECT_AFTER_TIME`]; it sends at most [`REJECT_AFTER_MESSAGES`] messages
//! and asks for a new handshake after [`REKEY_AFTER_TIME`] or
//! [`REKEY_AFTER_MESSAGES`]. Initiations to a peer are at least
//! [`REKEY_TIMEOUT`] apart and stop after [`REKEY_ATTEMPT_TIME`].
//!
//! Under load the device answers handshake messages without a valid `mac2`
//! with a cookie reply instead of processing them (whitepaper section 5.3).
//!
//! What is proved about it is in `proofs/Wireguard/DeviceTop.lean`.

use crate::allowed_ips::AllowedIps;
use crate::cookie::{
    add_macs, check_mac1, check_mac2, consume_cookie_reply, cookie_key, create_cookie_reply,
    mac1_key, make_cookie, COOKIE_LEN,
};
use crate::crypto::{Crypto, KEY_LEN, MAC_LEN, XNONCE_LEN};
use crate::message::{
    CookieReply, Initiation, Message, Response, COOKIE_REPLY_LEN, INITIATION_LEN, RESPONSE_LEN,
    TRANSPORT_HEADER_LEN,
};
use crate::noise::{
    consume_initiation_static, consume_initiation_timestamp, consume_response, create_initiation,
    create_response, timestamp_after, transport_keys, Chain, InitiatorState, TIMESTAMP_LEN,
};
use crate::replay::{Replay, REJECT_AFTER_MESSAGES};
use crate::transport::{self, Received};
use untrusted::Untrusted;

/// The number of peers a device can have.
pub const MAX_PEERS: usize = 16;
/// The largest IP packet the device sends.
pub const MAX_PACKET_LEN: usize = 65535;

// Times are in nanoseconds.
/// A new handshake is wanted after this many messages under a keypair.
pub const REKEY_AFTER_MESSAGES: u64 = 1_152_921_504_606_846_976;
/// The initiator of a session wants a new handshake when sending under a
/// keypair this old.
pub const REKEY_AFTER_TIME: u64 = 120_000_000_000;
/// A keypair is not used once this old.
pub const REJECT_AFTER_TIME: u64 = 180_000_000_000;
/// A keypair is erased once this old (three times [`REJECT_AFTER_TIME`]).
pub const ERASE_AFTER_TIME: u64 = 540_000_000_000;
/// Handshake attempts stop after this long without a response.
pub const REKEY_ATTEMPT_TIME: u64 = 90_000_000_000;
/// The least time between two initiations to a peer.
pub const REKEY_TIMEOUT: u64 = 5_000_000_000;
/// A keepalive is sent if data was received and nothing sent for this long.
pub const KEEPALIVE_TIMEOUT: u64 = 10_000_000_000;
/// The cookie secret changes this often.
pub const COOKIE_SECRET_MAX_AGE: u64 = 120_000_000_000;
/// A received cookie is used for this long (the secret's age, less a margin
/// for latency).
pub const COOKIE_MAX_AGE: u64 = 115_000_000_000;

/// A UDP endpoint: an IP address (IPv4 in the first 4 bytes) and a port.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Endpoint {
    pub v6: bool,
    pub addr: [u8; 16],
    pub port: u16,
}

impl Endpoint {
    /// The bytes a cookie is computed over: the address, then the port,
    /// big-endian.
    fn cookie_bytes(&self) -> [u8; 19] {
        let mut out = [0u8; 19];
        out[0] = if self.v6 { 6 } else { 4 };
        let mut i = 0;
        while i < 16 {
            out[1 + i] = self.addr[i];
            i += 1;
        }
        out[17] = (self.port / 256) as u8;
        out[18] = (self.port % 256) as u8;
        out
    }

    fn unset() -> Endpoint {
        Endpoint {
            v6: false,
            addr: [0; 16],
            port: 0,
        }
    }
}

/// The inputs of one call besides its bytes: the time, and randomness that
/// the call may use.
#[derive(Debug, Clone, Copy)]
pub struct Env {
    /// Monotonic time, in nanoseconds.
    pub now: u64,
    /// The wall-clock time, as TAI64N, for a new initiation.
    pub timestamp: [u8; TIMESTAMP_LEN],
    /// The ephemeral private key of a new handshake message.
    pub ephemeral: [u8; KEY_LEN],
    /// The sender index of a new handshake message.
    pub index: u32,
    /// The nonce of a cookie reply.
    pub nonce: [u8; XNONCE_LEN],
    /// A new cookie secret.
    pub secret: [u8; KEY_LEN],
}

/// What the caller should do after a call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    None,
    /// Send `out[..len]` as a UDP datagram to the endpoint.
    Send(Endpoint, usize),
    /// Deliver the IP packet `out[..len]`.
    Deliver(usize),
}

/// The keys and counters of one session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Keypair {
    pub valid: bool,
    /// Whether this side initiated the handshake.
    pub initiator: bool,
    pub send: [u8; KEY_LEN],
    pub recv: [u8; KEY_LEN],
    /// The index the peer puts in messages to us.
    pub local_index: u32,
    /// The index we put in messages to the peer.
    pub remote_index: u32,
    /// The counter of the next message sent.
    pub counter: u64,
    pub replay: Replay,
    /// When the handshake completed.
    pub created: u64,
}

impl Keypair {
    fn empty() -> Keypair {
        Keypair {
            valid: false,
            initiator: false,
            send: [0; KEY_LEN],
            recv: [0; KEY_LEN],
            local_index: 0,
            remote_index: 0,
            counter: 0,
            replay: Replay::new(),
            created: 0,
        }
    }
}

/// Our initiation in flight, waiting for the response.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Handshake {
    pub active: bool,
    pub local_index: u32,
    pub state: InitiatorState,
}

/// A peer, and our sessions with it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Peer {
    pub public: [u8; KEY_LEN],
    pub psk: [u8; KEY_LEN],
    /// The key of the `mac1` of our messages to the peer.
    pub mac1_key: [u8; KEY_LEN],
    /// The key of the peer's cookie replies.
    pub cookie_key: [u8; KEY_LEN],
    pub endpoint: Endpoint,
    pub has_endpoint: bool,
    /// The persistent keepalive interval; 0 if off.
    pub persistent_keepalive: u64,
    /// The greatest timestamp of the peer's initiations.
    pub last_timestamp: [u8; TIMESTAMP_LEN],
    pub handshake: Handshake,
    /// The `mac1` of our last handshake message, which a cookie reply
    /// authenticates.
    pub last_mac1: [u8; MAC_LEN],
    /// The last cookie the peer sent us, and when.
    pub cookie: [u8; COOKIE_LEN],
    pub has_cookie: bool,
    pub cookie_at: u64,
    pub current: Keypair,
    pub previous: Keypair,
    pub next: Keypair,
    /// When we last sent an initiation.
    pub initiation_at: u64,
    pub has_initiation: bool,
    /// When the current series of handshake attempts started.
    pub attempt_started: u64,
    /// Whether to start a handshake at the next tick.
    pub rekey_wanted: bool,
    /// When we last sent anything to the peer.
    pub last_sent: u64,
    /// When we last received data from the peer.
    pub last_received: u64,
    /// Whether data was received and nothing sent since.
    pub keepalive_due: bool,
}

impl Peer {
    fn empty() -> Peer {
        Peer {
            public: [0; KEY_LEN],
            psk: [0; KEY_LEN],
            mac1_key: [0; KEY_LEN],
            cookie_key: [0; KEY_LEN],
            endpoint: Endpoint::unset(),
            has_endpoint: false,
            persistent_keepalive: 0,
            last_timestamp: [0; TIMESTAMP_LEN],
            handshake: Handshake {
                active: false,
                local_index: 0,
                state: InitiatorState {
                    chain: Chain {
                        key: [0; KEY_LEN],
                        hash: [0; KEY_LEN],
                    },
                    ephemeral_private: [0; KEY_LEN],
                },
            },
            last_mac1: [0; MAC_LEN],
            cookie: [0; COOKIE_LEN],
            has_cookie: false,
            cookie_at: 0,
            current: Keypair::empty(),
            previous: Keypair::empty(),
            next: Keypair::empty(),
            initiation_at: 0,
            has_initiation: false,
            attempt_started: 0,
            rekey_wanted: false,
            last_sent: 0,
            last_received: 0,
            keepalive_due: false,
        }
    }
}

/// The device.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Device {
    pub private: [u8; KEY_LEN],
    pub public: [u8; KEY_LEN],
    /// The key of the `mac1` of messages to us.
    pub mac1_key: [u8; KEY_LEN],
    /// The key of our cookie replies.
    pub cookie_key: [u8; KEY_LEN],
    pub peers: [Peer; MAX_PEERS],
    pub peer_count: usize,
    pub allowed_ips: AllowedIps,
    pub cookie_secret: [u8; KEY_LEN],
    pub has_cookie_secret: bool,
    pub cookie_secret_at: u64,
    /// The latest time seen, so that time never goes back.
    pub now: u64,
}

/// `now - since`, or 0 if `since` is later.
// Not `saturating_sub`, which the Lean model of `core` may not cover.
#[allow(clippy::implicit_saturating_sub)]
fn elapsed(since: u64, now: u64) -> u64 {
    if now >= since {
        now - since
    } else {
        0
    }
}

/// Whether `a` and `b` are equal.
fn keys_equal(a: &[u8; KEY_LEN], b: &[u8; KEY_LEN]) -> bool {
    let mut equal = true;
    let mut i = 0;
    while i < KEY_LEN {
        if a[i] != b[i] {
            equal = false;
        }
        i += 1;
    }
    equal
}

/// Whether `kp` may receive at `now`: valid and younger than
/// [`REJECT_AFTER_TIME`].
fn can_receive(kp: &Keypair, now: u64) -> bool {
    kp.valid && kp.created <= now && now - kp.created < REJECT_AFTER_TIME
}

/// Whether `kp` may send at `now`: it may receive, and its counter is below
/// [`REJECT_AFTER_MESSAGES`].
fn can_send(kp: &Keypair, now: u64) -> bool {
    can_receive(kp, now) && kp.counter < REJECT_AFTER_MESSAGES
}

/// Whether the session of `p` with local index `index`, if any, is its
/// current (0), previous (1) or next (2) keypair; 3 if none.
fn session_slot(p: &Peer, index: u32) -> u8 {
    if p.current.valid && p.current.local_index == index {
        0
    } else if p.previous.valid && p.previous.local_index == index {
        1
    } else if p.next.valid && p.next.local_index == index {
        2
    } else {
        3
    }
}

/// The keypair of `p` in `slot` (0 to 2).
fn keypair(p: &Peer, slot: u8) -> Keypair {
    if slot == 0 {
        p.current
    } else if slot == 1 {
        p.previous
    } else {
        p.next
    }
}

/// `p` with `kp` in `slot` (0 to 2).
fn set_keypair(p: &mut Peer, slot: u8, kp: Keypair) {
    if slot == 0 {
        p.current = kp;
    } else if slot == 1 {
        p.previous = kp;
    } else {
        p.next = kp;
    }
}

/// Whether `index` is the local index of one of `p`'s sessions or its
/// handshake in flight.
fn uses_index(p: &Peer, index: u32) -> bool {
    session_slot(p, index) != 3 || (p.handshake.active && p.handshake.local_index == index)
}

/// Whether `kp` is valid and [`ERASE_AFTER_TIME`] old.
fn expired(kp: &Keypair, now: u64) -> bool {
    kp.valid && elapsed(kp.created, now) >= ERASE_AFTER_TIME
}

/// Moves the keypairs of `p` on, when the session it initiated is confirmed:
/// the next keypair becomes current, and the current one previous.
fn rotate(p: &mut Peer) {
    p.previous = p.current;
    p.current = p.next;
    p.next = Keypair::empty();
}

/// Erases the keypairs of `p` that are [`ERASE_AFTER_TIME`] old.
fn erase_old(p: &mut Peer, now: u64) {
    if expired(&p.current, now) {
        p.current = Keypair::empty();
    }
    if expired(&p.previous, now) {
        p.previous = Keypair::empty();
    }
    if expired(&p.next, now) {
        p.next = Keypair::empty();
    }
}

/// Whether an initiation was sent to `p` less than [`REKEY_TIMEOUT`] ago.
fn initiation_too_soon(p: &Peer, now: u64) -> bool {
    p.has_initiation && elapsed(p.initiation_at, now) < REKEY_TIMEOUT
}

/// Whether, having sent under `kp` at `now`, a new handshake is wanted: after
/// [`REKEY_AFTER_MESSAGES`] messages, or, for the initiator, after
/// [`REKEY_AFTER_TIME`].
fn wants_rekey(kp: &Keypair, now: u64) -> bool {
    kp.counter >= REKEY_AFTER_MESSAGES
        || (kp.initiator && elapsed(kp.created, now) >= REKEY_AFTER_TIME)
}

/// Whether the handshake timers of `p` call for an initiation at `now`: a
/// retry of the handshake in flight [`REKEY_TIMEOUT`] after the last
/// initiation, or a new handshake that sending asked for. A handshake whose
/// attempts started [`REKEY_ATTEMPT_TIME`] ago is given up instead.
fn handshake_timer(p: &mut Peer, now: u64) -> bool {
    if !p.handshake.active {
        return p.rekey_wanted;
    }
    if elapsed(p.initiation_at, now) < REKEY_TIMEOUT {
        return false;
    }
    if elapsed(p.attempt_started, now) >= REKEY_ATTEMPT_TIME {
        p.handshake.active = false;
        p.rekey_wanted = false;
        return false;
    }
    true
}

/// Whether the keepalive timers of `p` call for a keepalive at `now`: data
/// was received [`KEEPALIVE_TIMEOUT`] ago with nothing sent since (this
/// keepalive is then no longer due), or the persistent keepalive interval has
/// passed since anything was sent.
fn keepalive_timer(p: &mut Peer, now: u64) -> bool {
    if p.keepalive_due && elapsed(p.last_received, now) >= KEEPALIVE_TIMEOUT {
        p.keepalive_due = false;
        if can_send(&p.current, now) {
            return true;
        }
    }
    p.persistent_keepalive > 0 && elapsed(p.last_sent, now) >= p.persistent_keepalive
}

/// What the timers of `p` call for at `now`: nothing (0), an initiation (1)
/// or a keepalive (2). Old keypairs are erased first.
fn timers(p: &mut Peer, now: u64) -> u8 {
    erase_old(p, now);
    if handshake_timer(p, now) {
        return 1;
    }
    if keepalive_timer(p, now) {
        return 2;
    }
    0
}

/// Copies `src` to the start of `out`, if it fits.
fn copy_out(out: &mut [u8], src: &[u8]) -> bool {
    if out.len() < src.len() {
        return false;
    }
    let mut i = 0;
    while i < src.len() {
        out[i] = src[i];
        i += 1;
    }
    true
}

/// Whether a handshake message is let through: 0 if it is, 1 if it is
/// dropped, 2 if a cookie reply to it was written to `out`.
type Admission = u8;

impl Device {
    /// A device with the private key `private` and no peers.
    pub fn new<C: Crypto>(c: &C, private: &[u8; KEY_LEN]) -> Device {
        let mut public = [0u8; KEY_LEN];
        c.x25519_public(private, &mut public);
        Device {
            private: *private,
            public,
            mac1_key: mac1_key(c, &public),
            cookie_key: cookie_key(c, &public),
            peers: [Peer::empty(); MAX_PEERS],
            peer_count: 0,
            allowed_ips: AllowedIps::new(),
            cookie_secret: [0; KEY_LEN],
            has_cookie_secret: false,
            cookie_secret_at: 0,
            now: 0,
        }
    }

    /// Adds the peer with static public key `public`; returns its number, or
    /// `None` if the device is full or already has it.
    pub fn add_peer<C: Crypto>(
        &mut self,
        c: &C,
        public: &[u8; KEY_LEN],
        psk: &[u8; KEY_LEN],
        persistent_keepalive: u64,
    ) -> Option<usize> {
        if self.peer_count == MAX_PEERS {
            return None;
        }
        if self.find_peer(public) < self.peer_count {
            return None;
        }
        let mut p = Peer::empty();
        p.public = *public;
        p.psk = *psk;
        p.mac1_key = mac1_key(c, public);
        p.cookie_key = cookie_key(c, public);
        p.persistent_keepalive = persistent_keepalive;
        let i = self.peer_count;
        self.peers[i] = p;
        self.peer_count += 1;
        Some(i)
    }

    /// Sets the endpoint of peer `peer`.
    pub fn set_endpoint(&mut self, peer: usize, endpoint: &Endpoint) {
        if peer < self.peer_count {
            let mut p = self.peers[peer];
            p.endpoint = *endpoint;
            p.has_endpoint = true;
            self.peers[peer] = p;
        }
    }

    /// Allows `addr/len` for peer `peer` (see [`AllowedIps::insert`]).
    pub fn allow(&mut self, peer: usize, v6: bool, addr: u128, len: u32) -> bool {
        if peer >= self.peer_count {
            return false;
        }
        self.allowed_ips.insert(v6, addr, len, peer as u16)
    }

    /// The time of a call: `now`, or the latest time seen if that is later.
    fn clock(&mut self, now: u64) -> u64 {
        if now > self.now {
            self.now = now;
        }
        self.now
    }

    /// The number of the peer with static public key `public`, or
    /// `peer_count` if none.
    fn find_peer(&self, public: &[u8; KEY_LEN]) -> usize {
        let mut i = 0;
        while i < self.peer_count && !keys_equal(&self.peers[i].public, public) {
            i += 1;
        }
        i
    }

    /// The number of the peer with a session with local index `index`, or
    /// `peer_count` if none.
    fn find_session(&self, index: u32) -> usize {
        let mut i = 0;
        while i < self.peer_count && session_slot(&self.peers[i], index) == 3 {
            i += 1;
        }
        i
    }

    /// The number of the peer with a handshake in flight with local index
    /// `index`, or `peer_count` if none.
    fn find_handshake(&self, index: u32) -> usize {
        let mut i = 0;
        while i < self.peer_count
            && !(self.peers[i].handshake.active && self.peers[i].handshake.local_index == index)
        {
            i += 1;
        }
        i
    }

    /// Whether `index` is in use as a local index.
    fn index_in_use(&self, index: u32) -> bool {
        let mut i = 0;
        while i < self.peer_count && !uses_index(&self.peers[i], index) {
            i += 1;
        }
        i < self.peer_count
    }

    /// The cookie to put in our next handshake message to `p`, if it is
    /// recent.
    fn has_fresh_cookie(p: &Peer, now: u64) -> bool {
        p.has_cookie && elapsed(p.cookie_at, now) < COOKIE_MAX_AGE
    }

    /// Writes the encoded handshake message `msg` to `out` with its MACs for
    /// peer `p`, and records its `mac1`.
    fn finish_handshake_message<C: Crypto>(
        c: &C,
        p: &mut Peer,
        now: u64,
        msg: &mut [u8],
        out: &mut [u8],
    ) -> bool {
        let tau = if Device::has_fresh_cookie(p, now) {
            Some(p.cookie)
        } else {
            None
        };
        let mac1 = add_macs(c, msg, &p.mac1_key, tau);
        p.last_mac1 = mac1;
        copy_out(out, msg)
    }

    /// Sends an initiation to peer `i`, unless one was sent less than
    /// [`REKEY_TIMEOUT`] ago.
    fn begin_handshake<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        now: u64,
        i: usize,
        out: &mut [u8],
    ) -> Action {
        let mut p = self.peers[i];
        if !p.has_endpoint {
            return Action::None;
        }
        if initiation_too_soon(&p, now) {
            return Action::None;
        }
        if self.index_in_use(env.index) {
            return Action::None;
        }
        let (msg, state) = match create_initiation(
            c,
            &self.private,
            &self.public,
            &p.public,
            &env.ephemeral,
            env.index,
            &env.timestamp,
        ) {
            Some(r) => r,
            None => return Action::None,
        };
        let mut bytes = msg.encode();
        if !Device::finish_handshake_message(c, &mut p, now, &mut bytes, out) {
            return Action::None;
        }
        if !p.handshake.active {
            p.attempt_started = now;
        }
        p.handshake = Handshake {
            active: true,
            local_index: env.index,
            state,
        };
        p.initiation_at = now;
        p.has_initiation = true;
        p.rekey_wanted = false;
        p.last_sent = now;
        let to = p.endpoint;
        self.peers[i] = p;
        Action::Send(to, INITIATION_LEN)
    }

    /// Sends `packet` (empty for a keepalive) to peer `i` under its current
    /// keypair, or starts a handshake if it has none it may send under.
    #[allow(clippy::too_many_arguments)]
    fn send_data<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        now: u64,
        i: usize,
        packet: &[u8],
        work: &mut [u8],
        out: &mut [u8],
    ) -> Action {
        let mut p = self.peers[i];
        if !p.has_endpoint {
            return Action::None;
        }
        if !can_send(&p.current, now) {
            return self.begin_handshake(c, env, now, i, out);
        }
        let mut kp = p.current;
        match transport::encrypt(c, &kp.send, kp.remote_index, kp.counter, packet, work, out) {
            Some(n) => {
                kp.counter += 1;
                if wants_rekey(&kp, now) {
                    p.rekey_wanted = true;
                }
                p.current = kp;
                p.last_sent = now;
                p.keepalive_due = false;
                let to = p.endpoint;
                self.peers[i] = p;
                Action::Send(to, n)
            }
            None => Action::None,
        }
    }

    /// Sends a keepalive (an empty packet) to peer `i`.
    fn send_keepalive<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        now: u64,
        i: usize,
        out: &mut [u8],
    ) -> Action {
        let empty = [0u8; 0];
        let mut work = [0u8; 0];
        self.send_data(c, env, now, i, &empty, &mut work, out)
    }

    /// Handles an IP packet to send: encrypts it for the peer its destination
    /// routes to, into `out` (using `work`, at least as long as the packet
    /// padded to 16 bytes); `out` must have room for the packet and 48 bytes.
    pub fn handle_packet<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        packet: &[u8],
        work: &mut [u8],
        out: &mut [u8],
    ) -> Action {
        let now = self.clock(env.now);
        if packet.len() > MAX_PACKET_LEN {
            return Action::None;
        }
        let ip = match transport::inner(packet) {
            Some(ip) => ip,
            None => return Action::None,
        };
        let i = match self.allowed_ips.lookup(ip.v6, ip.dst) {
            Some(q) => q as usize,
            None => return Action::None,
        };
        if i >= self.peer_count {
            return Action::None;
        }
        self.send_data(c, env, now, i, packet, work, out)
    }

    /// Whether the cookie secret is to be replaced: there is none, or it is
    /// [`COOKIE_SECRET_MAX_AGE`] old.
    fn secret_stale(&self, now: u64) -> bool {
        !self.has_cookie_secret || elapsed(self.cookie_secret_at, now) >= COOKIE_SECRET_MAX_AGE
    }

    /// Whether to let a handshake message `bytes` from `from` through: its
    /// `mac1` must be valid, and under load its `mac2` too, failing which a
    /// cookie reply to `sender` is written to `out`.
    #[allow(clippy::too_many_arguments)]
    fn admit<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        now: u64,
        from: &Endpoint,
        under_load: bool,
        bytes: &[u8],
        sender: u32,
        mac1: &[u8; MAC_LEN],
        out: &mut [u8],
    ) -> Admission {
        if !check_mac1(c, bytes, &self.mac1_key) {
            return 1;
        }
        if !under_load {
            return 0;
        }
        if self.secret_stale(now) {
            self.cookie_secret = env.secret;
            self.cookie_secret_at = now;
            self.has_cookie_secret = true;
        }
        let tau = make_cookie(c, &self.cookie_secret, &from.cookie_bytes());
        if check_mac2(c, bytes, &tau) {
            return 0;
        }
        let reply = create_cookie_reply(c, &self.cookie_key, sender, &env.nonce, &tau, mac1);
        if copy_out(out, &reply.encode()) {
            2
        } else {
            1
        }
    }

    /// Handles an initiation: answers it with a response if it comes from a
    /// peer, with a timestamp later than the peer's previous ones.
    #[allow(clippy::too_many_arguments)]
    fn on_initiation<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        now: u64,
        from: &Endpoint,
        under_load: bool,
        bytes: &[u8],
        msg: &Initiation,
        out: &mut [u8],
    ) -> Action {
        let a = self.admit(
            c,
            env,
            now,
            from,
            under_load,
            bytes,
            msg.sender.0,
            &msg.mac1,
            out,
        );
        if a == 2 {
            return Action::Send(*from, COOKIE_REPLY_LEN);
        }
        if a != 0 {
            return Action::None;
        }
        let st = match consume_initiation_static(c, &self.private, &self.public, msg) {
            Some(st) => st,
            None => return Action::None,
        };
        let i = self.find_peer(&st.initiator_static);
        if i >= self.peer_count {
            return Action::None;
        }
        if self.index_in_use(env.index) {
            return Action::None;
        }
        let mut p = self.peers[i];
        let (chain, timestamp) = match consume_initiation_timestamp(c, &self.private, &st, msg) {
            Some(r) => r,
            None => return Action::None,
        };
        if !timestamp_after(&timestamp, &p.last_timestamp) {
            return Action::None;
        }
        let (resp, chain) = match create_response(
            c,
            &chain,
            &msg.ephemeral,
            &st.initiator_static,
            &p.psk,
            &env.ephemeral,
            env.index,
            msg.sender.0,
        ) {
            Some(r) => r,
            None => return Action::None,
        };
        let mut bytes = resp.encode();
        if !Device::finish_handshake_message(c, &mut p, now, &mut bytes, out) {
            return Action::None;
        }
        let (recv, send) = transport_keys(c, &chain);
        p.last_timestamp = timestamp;
        p.next = Keypair {
            valid: true,
            initiator: false,
            send,
            recv,
            local_index: env.index,
            remote_index: msg.sender.0,
            counter: 0,
            replay: Replay::new(),
            created: now,
        };
        p.endpoint = *from;
        p.has_endpoint = true;
        p.last_sent = now;
        self.peers[i] = p;
        Action::Send(*from, RESPONSE_LEN)
    }

    /// Handles a response to our initiation: the session becomes current, and
    /// a keepalive confirms it to the peer.
    #[allow(clippy::too_many_arguments)]
    fn on_response<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        now: u64,
        from: &Endpoint,
        under_load: bool,
        bytes: &[u8],
        msg: &Response,
        out: &mut [u8],
    ) -> Action {
        let a = self.admit(
            c,
            env,
            now,
            from,
            under_load,
            bytes,
            msg.sender.0,
            &msg.mac1,
            out,
        );
        if a == 2 {
            return Action::Send(*from, COOKIE_REPLY_LEN);
        }
        if a != 0 {
            return Action::None;
        }
        let i = self.find_handshake(msg.receiver.0);
        if i >= self.peer_count {
            return Action::None;
        }
        let mut p = self.peers[i];
        let chain = match consume_response(c, &p.handshake.state, &self.private, &p.psk, msg) {
            Some(chain) => chain,
            None => return Action::None,
        };
        let (send, recv) = transport_keys(c, &chain);
        p.previous = p.current;
        p.current = Keypair {
            valid: true,
            initiator: true,
            send,
            recv,
            local_index: p.handshake.local_index,
            remote_index: msg.sender.0,
            counter: 0,
            replay: Replay::new(),
            created: now,
        };
        p.next = Keypair::empty();
        p.handshake.active = false;
        p.rekey_wanted = false;
        p.endpoint = *from;
        p.has_endpoint = true;
        self.peers[i] = p;
        self.send_keepalive(c, env, now, i, out)
    }

    /// Handles a cookie reply to our handshake message: keeps the cookie.
    fn on_cookie_reply<C: Crypto>(&mut self, c: &C, now: u64, msg: &CookieReply) -> Action {
        let mut i = self.find_handshake(msg.receiver.0);
        if i >= self.peer_count {
            i = self.find_session(msg.receiver.0);
        }
        if i >= self.peer_count {
            return Action::None;
        }
        let mut p = self.peers[i];
        if let Some(tau) = consume_cookie_reply(c, &p.cookie_key, msg, &p.last_mac1) {
            p.cookie = tau;
            p.has_cookie = true;
            p.cookie_at = now;
            self.peers[i] = p;
        }
        Action::None
    }

    /// Handles a transport message to the session with local index
    /// `receiver`: decrypts it into `out`, and delivers it if it is a packet
    /// from the peer.
    #[allow(clippy::too_many_arguments)]
    fn on_transport<C: Crypto>(
        &mut self,
        c: &C,
        now: u64,
        from: &Endpoint,
        receiver: u32,
        counter: u64,
        body: &[u8],
        out: &mut [u8],
    ) -> Action {
        let i = self.find_session(receiver);
        if i >= self.peer_count {
            return Action::None;
        }
        let mut p = self.peers[i];
        let slot = session_slot(&p, receiver);
        let mut kp = keypair(&p, slot);
        if !can_receive(&kp, now) {
            return Action::None;
        }
        let r = transport::receive(
            c,
            &kp.recv,
            &mut kp.replay,
            &self.allowed_ips,
            i as u16,
            counter,
            body,
            out,
        );
        set_keypair(&mut p, slot, kp);
        let action = match r {
            Received::Drop => {
                self.peers[i] = p;
                return Action::None;
            }
            Received::Keepalive => Action::None,
            Received::Packet(n) => {
                p.last_received = now;
                p.keepalive_due = true;
                Action::Deliver(n)
            }
        };
        if slot == 2 {
            rotate(&mut p);
        }
        p.endpoint = *from;
        p.has_endpoint = true;
        self.peers[i] = p;
        action
    }

    /// Handles a UDP datagram `bytes` from `from`. `under_load` says whether
    /// the caller is busy enough to want handshakes proved to come from their
    /// address (with cookies).
    pub fn handle_datagram<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        from: &Endpoint,
        under_load: bool,
        bytes: &[u8],
        out: &mut [u8],
    ) -> Action {
        let now = self.clock(env.now);
        match Untrusted::new(bytes).validate::<Message>() {
            Ok(Message::Initiation(msg)) => {
                self.on_initiation(c, env, now, from, under_load, bytes, &msg, out)
            }
            Ok(Message::Response(msg)) => {
                self.on_response(c, env, now, from, under_load, bytes, &msg, out)
            }
            Ok(Message::CookieReply(msg)) => self.on_cookie_reply(c, now, &msg),
            Ok(Message::Transport(t)) => self.on_transport(
                c,
                now,
                from,
                t.header.receiver.0,
                t.header.counter.0,
                &bytes[TRANSPORT_HEADER_LEN..],
                out,
            ),
            Err(_) => Action::None,
        }
    }

    /// Runs the timers of peer `i`.
    fn tick_peer<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        now: u64,
        i: usize,
        out: &mut [u8],
    ) -> Action {
        let mut p = self.peers[i];
        let t = timers(&mut p, now);
        self.peers[i] = p;
        if t == 1 {
            self.begin_handshake(c, env, now, i, out)
        } else if t == 2 {
            self.send_keepalive(c, env, now, i, out)
        } else {
            Action::None
        }
    }

    /// Runs the timers of peers `i` onwards, until one calls for something.
    // Recursion rather than a loop: Aeneas cannot return early from a loop,
    // and a loop that updates `self` is translated with every field apart.
    fn tick_from<C: Crypto>(
        &mut self,
        c: &C,
        env: &Env,
        now: u64,
        i: usize,
        out: &mut [u8],
    ) -> Action {
        if i >= self.peer_count {
            return Action::None;
        }
        let a = self.tick_peer(c, env, now, i, out);
        if !matches!(a, Action::None) {
            return a;
        }
        self.tick_from(c, env, now, i + 1, out)
    }

    /// Runs the timers: returns the first thing to do. Call it periodically,
    /// and again until it returns [`Action::None`].
    pub fn tick<C: Crypto>(&mut self, c: &C, env: &Env, out: &mut [u8]) -> Action {
        let now = self.clock(env.now);
        self.tick_from(c, env, now, 0, out)
    }
}
