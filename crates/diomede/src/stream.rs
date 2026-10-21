//! The start of TCP connections to port 443, reassembled, so that a
//! ClientHello spanning several segments is checked whole.
//!
//! [`Streams`] tracks up to [`MAX_FLOWS`] connections. For each, it collects
//! the client's bytes in order from the start of the connection (the byte
//! after the SYN, or the first data seen) until the first TLS record is
//! complete, up to [`MAX_RECORD`] bytes, and then decides:
//! - a ClientHello for a blocked name: the connection is blocked, and every
//!   segment of it from then on gets a reset;
//! - anything else (another record, or one too long to hold): the
//!   connection passes, and is no longer looked at.
//!
//! While collecting, a segment carrying bytes past a gap is dropped, so that
//! the client sends them again in order; segments carrying only bytes
//! already seen pass. A FIN or RST ends the tracking of a connection. When
//! the table is full, the connection seen least recently is forgotten.

use crate::blocklist::Blocklist;
use crate::filter::classify_stream;

/// The most connections tracked at once.
pub const MAX_FLOWS: usize = 256;
/// The longest first record collected; longer ones pass unchecked.
pub const MAX_RECORD: usize = 8192;

/// A slot not in use.
pub const FREE: u8 = 0;
/// Collecting the first record.
pub const COLLECTING: u8 = 1;
/// The first record was not a ClientHello for a blocked name.
pub const PASSED: u8 = 2;
/// The first record was a ClientHello for a blocked name.
pub const BLOCKED: u8 = 3;

/// A connection: its addresses (IPv4 ones in the low 32 bits) and ports, as
/// the client sends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Key {
    pub v6: bool,
    pub src: u128,
    pub dst: u128,
    pub src_port: u16,
    pub dst_port: u16,
}

/// A tracked connection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Flow {
    pub key: Key,
    pub state: u8,
    /// The sequence number of the next byte expected.
    pub next_seq: u32,
    /// The number of bytes collected.
    pub len: usize,
    /// When it was last seen.
    pub last: u64,
}

const NO_FLOW: Flow = Flow {
    key: Key {
        v6: false,
        src: 0,
        dst: 0,
        src_port: 0,
        dst_port: 0,
    },
    state: FREE,
    next_seq: 0,
    len: 0,
    last: 0,
};

/// What to do with a segment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    Pass,
    Drop,
    Reset,
}

/// The connections tracked, and the bytes collected for each.
pub struct Streams {
    pub flows: [Flow; MAX_FLOWS],
    pub data: [[u8; MAX_RECORD]; MAX_FLOWS],
}

/// No connection tracked. It is large: put it in a `static`, which a `const`
/// initializes.
#[allow(clippy::large_const_arrays)]
pub const EMPTY: Streams = Streams {
    flows: [NO_FLOW; MAX_FLOWS],
    data: [[0; MAX_RECORD]; MAX_FLOWS],
};

/// Whether `a` and `b` are the same connection.
fn same(a: Key, b: Key) -> bool {
    if a.v6 != b.v6 {
        return false;
    }
    if a.src != b.src {
        return false;
    }
    if a.dst != b.dst {
        return false;
    }
    if a.src_port != b.src_port {
        return false;
    }
    a.dst_port == b.dst_port
}

/// Whether `f` tracks the connection `k`.
fn tracks(f: Flow, k: Key) -> bool {
    if f.state == FREE {
        return false;
    }
    same(f.key, k)
}

/// The slot of the tracked connection `k`, or [`MAX_FLOWS`].
fn find(flows: &[Flow; MAX_FLOWS], k: Key) -> usize {
    let mut found = MAX_FLOWS;
    let mut i = 0;
    while i < MAX_FLOWS {
        let f = flows[i];
        if found == MAX_FLOWS && tracks(f, k) {
            found = i;
        }
        i += 1;
    }
    found
}

/// The first free slot, or [`MAX_FLOWS`].
fn first_free(flows: &[Flow; MAX_FLOWS]) -> usize {
    let mut free = MAX_FLOWS;
    let mut i = 0;
    while i < MAX_FLOWS {
        let f = flows[i];
        if free == MAX_FLOWS && f.state == FREE {
            free = i;
        }
        i += 1;
    }
    free
}

/// The slot seen least recently.
fn least_recent(flows: &[Flow; MAX_FLOWS]) -> usize {
    let mut oldest = 0;
    let mut i = 1;
    while i < MAX_FLOWS {
        if flows[i].last < flows[oldest].last {
            oldest = i;
        }
        i += 1;
    }
    oldest
}

/// A slot for a new connection: a free one, or else the one seen least
/// recently.
fn slot(flows: &[Flow; MAX_FLOWS]) -> usize {
    let free = first_free(flows);
    if free < MAX_FLOWS {
        free
    } else {
        least_recent(flows)
    }
}

/// Copies `data[from..]` to `buf[len..]`, as much as fits; returns the new
/// length.
fn append(buf: &mut [u8; MAX_RECORD], len: usize, data: &[u8], from: usize) -> usize {
    let mut n = len;
    let mut j = from;
    while j < data.len() && n < MAX_RECORD {
        buf[n] = data[j];
        n += 1;
        j += 1;
    }
    n
}

/// The state of a connection whose first `len` bytes are `buf[..len]`.
fn decide(buf: &[u8; MAX_RECORD], len: usize, list: &Blocklist) -> u8 {
    if len < 5 {
        return COLLECTING;
    }
    if buf[0] != 22 {
        return PASSED;
    }
    let need = 5 + buf[3] as usize * 256 + buf[4] as usize;
    if need > MAX_RECORD {
        return PASSED;
    }
    if len < need {
        return COLLECTING;
    }
    if classify_stream(&buf[..need], list) {
        BLOCKED
    } else {
        PASSED
    }
}

/// Whether a segment with `flags` ends its connection: FIN or RST.
fn ends(flags: u8) -> bool {
    if flags % 2 == 1 {
        return true;
    }
    flags / 4 % 2 == 1
}

/// The first sequence number of a segment's data: after its SYN, if any.
fn data_start(seq: u32, syn: bool) -> u32 {
    if syn {
        seq.wrapping_add(1)
    } else {
        seq
    }
}

impl Streams {
    /// Collects the data of a segment of the connection in `slot`, which
    /// starts at `first`; decides once the first record is complete.
    fn collect(&mut self, slot: usize, first: u32, data: &[u8], list: &Blocklist) -> Step {
        let flow = self.flows[slot];
        // The offset in `data` of the byte expected next.
        let offset = flow.next_seq.wrapping_sub(first);
        if offset as usize >= data.len() {
            // Nothing new, unless the data is past a gap.
            if data.is_empty() || offset < 0x8000_0000 {
                return Step::Pass;
            }
            return Step::Drop;
        }
        let len = append(&mut self.data[slot], flow.len, data, offset as usize);
        let state = decide(&self.data[slot], len, list);
        self.flows[slot] = Flow {
            key: flow.key,
            state,
            next_seq: first.wrapping_add(data.len() as u32),
            len,
            last: flow.last,
        };
        if state == BLOCKED {
            Step::Reset
        } else {
            Step::Pass
        }
    }

    /// A segment of the connection tracked in `slot`.
    #[allow(clippy::too_many_arguments)]
    fn track(
        &mut self,
        slot: usize,
        first: u32,
        syn: bool,
        rst: bool,
        end: bool,
        data: &[u8],
        now: u64,
        list: &Blocklist,
    ) -> Step {
        let flow = self.flows[slot];
        let next = next_flow(flow, first, syn, end, now);
        self.flows[slot] = next;
        if flow.state == BLOCKED {
            if rst {
                return Step::Drop;
            }
            return Step::Reset;
        }
        if next.state != COLLECTING {
            return Step::Pass;
        }
        self.collect(slot, first, data, list)
    }

    /// What to do with a TCP segment of the connection `k` (to port 443),
    /// with sequence number `seq`, `flags` and `data`, seen at `now`.
    pub fn segment(
        &mut self,
        k: Key,
        seq: u32,
        flags: u8,
        data: &[u8],
        now: u64,
        list: &Blocklist,
    ) -> Step {
        let syn = flags / 2 % 2 == 1;
        let rst = flags / 4 % 2 == 1;
        let end = ends(flags);
        let first = data_start(seq, syn);
        let found = find(&self.flows, k);
        if found == MAX_FLOWS {
            // A new connection: tracked from its SYN or its first data.
            if end {
                return Step::Pass;
            }
            if !syn && data.is_empty() {
                return Step::Pass;
            }
        }
        let (i, f) = place(&self.flows, found, k, first, now);
        self.flows[i] = f;
        self.track(i, first, syn, rst, end, data, now, list)
    }
}

/// Where the segment of `k` goes: the slot `found` it is tracked in, or a new
/// one if [`MAX_FLOWS`]; and the flow there before the segment.
fn place(flows: &[Flow; MAX_FLOWS], found: usize, k: Key, first: u32, now: u64) -> (usize, Flow) {
    if found == MAX_FLOWS {
        return (slot(flows), fresh(k, first, now));
    }
    (found, flows[found])
}

/// The flow `f` after a segment starting at `first`, seen at `now`: freed
/// by a FIN or RST (`end`), started again by a SYN unless blocked.
fn next_flow(f: Flow, first: u32, syn: bool, end: bool, now: u64) -> Flow {
    if end {
        return touched(f, FREE, now);
    }
    if f.state == BLOCKED {
        return touched(f, BLOCKED, now);
    }
    if syn {
        return fresh(f.key, first, now);
    }
    touched(f, f.state, now)
}

/// A connection `k` starting to be collected at `first`.
fn fresh(k: Key, first: u32, now: u64) -> Flow {
    Flow {
        key: k,
        state: COLLECTING,
        next_seq: first,
        len: 0,
        last: now,
    }
}

/// `f` with `state`, seen at `now`.
fn touched(f: Flow, state: u8, now: u64) -> Flow {
    Flow {
        key: f.key,
        state,
        next_seq: f.next_seq,
        len: f.len,
        last: now,
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use std::boxed::Box;
    use std::vec::Vec;

    const SYN: u8 = 0x02;
    const ACK: u8 = 0x10;
    const FIN: u8 = 0x01;
    const RST: u8 = 0x04;

    fn key(port: u16) -> Key {
        Key { v6: false, src: 0x0a00_0002, dst: 0x0a00_0001, src_port: port, dst_port: 443 }
    }

    fn list<'a>(data: &'a mut Vec<u8>, ends: &'a mut Vec<u32>) -> Blocklist<'a> {
        data.extend_from_slice(b"tracker.io");
        ends.push(data.len() as u32);
        Blocklist::new(data, ends).unwrap()
    }

    /// A ClientHello record for `host`, padded by an extension of `pad`
    /// bytes.
    fn hello(host: &[u8], pad: usize) -> Vec<u8> {
        let mut exts = Vec::new();
        exts.extend_from_slice(&[0, 21]);
        exts.extend_from_slice(&(pad as u16).to_be_bytes());
        exts.resize(exts.len() + pad, 0);
        exts.extend_from_slice(&[0, 0]);
        exts.extend_from_slice(&((host.len() + 5) as u16).to_be_bytes());
        exts.extend_from_slice(&((host.len() + 3) as u16).to_be_bytes());
        exts.push(0);
        exts.extend_from_slice(&(host.len() as u16).to_be_bytes());
        exts.extend_from_slice(host);
        let mut body = std::vec![3, 3];
        body.extend_from_slice(&[7; 32]);
        body.extend_from_slice(&[0, 0, 2, 0x13, 0x01, 1, 0]);
        body.extend_from_slice(&(exts.len() as u16).to_be_bytes());
        body.extend_from_slice(&exts);
        let mut r = std::vec![22, 3, 1];
        r.extend_from_slice(&((body.len() + 4) as u16).to_be_bytes());
        r.extend_from_slice(&[1, 0]);
        r.extend_from_slice(&(body.len() as u16).to_be_bytes());
        r.extend_from_slice(&body);
        r
    }

    fn streams() -> Box<Streams> {
        // Built on the heap: it does not fit on a test thread's stack.
        let mut s: Box<Streams> = unsafe { Box::new_zeroed().assume_init() };
        s.flows = [NO_FLOW; MAX_FLOWS];
        s
    }

    #[test]
    fn checks_hellos_in_several_segments() {
        let (mut d, mut e) = (Vec::new(), Vec::new());
        let list = list(&mut d, &mut e);
        let mut s = streams();
        let k = key(40000);
        let h = hello(b"ads.tracker.io", 1500);
        assert_eq!(s.segment(k, 100, SYN, &[], 1, &list), Step::Pass);
        // The first segment, then a gap, then the rest.
        assert_eq!(s.segment(k, 101, ACK, &h[..1000], 2, &list), Step::Pass);
        assert_eq!(s.segment(k, 1101 + 100, ACK, &h[1100..], 3, &list), Step::Drop);
        // A retransmission of what was seen passes.
        assert_eq!(s.segment(k, 101, ACK, &h[..500], 4, &list), Step::Pass);
        // Overlapping the end of what was seen, and completing the record.
        assert_eq!(s.segment(k, 1001, ACK, &h[900..], 5, &list), Step::Reset);
        // The rest of the connection is reset, its RST dropped.
        assert_eq!(s.segment(k, 2000, ACK, b"x", 6, &list), Step::Reset);
        assert_eq!(s.segment(k, 2000, RST, &[], 7, &list), Step::Drop);
        assert_eq!(s.segment(k, 2000, ACK, b"x", 8, &list), Step::Pass);
    }

    #[test]
    fn passes_other_connections() {
        let (mut d, mut e) = (Vec::new(), Vec::new());
        let list = list(&mut d, &mut e);
        let mut s = streams();
        let k = key(40001);
        let h = hello(b"example.org", 1500);
        assert_eq!(s.segment(k, 7, SYN, &[], 1, &list), Step::Pass);
        assert_eq!(s.segment(k, 8, ACK, &h[..1200], 2, &list), Step::Pass);
        assert_eq!(s.segment(k, 1208, ACK, &h[1200..], 3, &list), Step::Pass);
        assert_eq!(s.flows[find(&s.flows, k)].state, PASSED);
        assert_eq!(s.segment(k, 9000, ACK, &[1; 3000], 4, &list), Step::Pass);
        assert_eq!(s.segment(k, 9000, FIN | ACK, &[], 5, &list), Step::Pass);
        assert_eq!(find(&s.flows, k), MAX_FLOWS);
        // Not TLS at all; a record too long to collect.
        let k2 = key(40002);
        assert_eq!(s.segment(k2, 5, ACK, b"GET / HTTP/1.1\r\n", 6, &list), Step::Pass);
        assert_eq!(s.flows[find(&s.flows, k2)].state, PASSED);
        let k3 = key(40003);
        assert_eq!(s.segment(k3, 5, ACK, &[22, 3, 1, 0x40, 0], 7, &list), Step::Pass);
        assert_eq!(s.flows[find(&s.flows, k3)].state, PASSED);
    }

    #[test]
    fn checks_hellos_in_one_segment() {
        let (mut d, mut e) = (Vec::new(), Vec::new());
        let list = list(&mut d, &mut e);
        let mut s = streams();
        let k = key(40004);
        // Without having seen the SYN.
        assert_eq!(s.segment(k, 1, ACK, &hello(b"tracker.io", 0), 1, &list), Step::Reset);
    }

    #[test]
    fn forgets_the_oldest_when_full() {
        let (mut d, mut e) = (Vec::new(), Vec::new());
        let list = list(&mut d, &mut e);
        let mut s = streams();
        for p in 0..MAX_FLOWS as u16 {
            s.segment(key(p), 0, SYN, &[], 10 + p as u64, &list);
        }
        s.segment(key(0), 1, ACK, &[22], 1000, &list);
        s.segment(key(9999), 0, SYN, &[], 1001, &list);
        assert_eq!(find(&s.flows, key(1)), MAX_FLOWS);
        assert!(find(&s.flows, key(0)) < MAX_FLOWS);
        assert!(find(&s.flows, key(9999)) < MAX_FLOWS);
    }
}
