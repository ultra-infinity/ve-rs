//! Cryptokey routing (whitepaper section 2): each peer is allowed a set of
//! IP prefixes. Outgoing packets go to the peer whose prefix is the longest
//! match for their destination; incoming packets are accepted only if their
//! source routes back to the peer they came from.
//!
//! The table is a fixed-capacity list of prefixes, IPv4 and IPv6 together;
//! addresses are `u128`s (an IPv4 address in the low 32 bits). Prefixes are
//! stored canonically (the bits after the prefix length cleared), and
//! inserting an existing prefix replaces its peer, so each prefix maps to one
//! peer. `proofs/Wireguard/AllowedIpsTop.lean` proves that [`AllowedIps::lookup`]
//! returns the peer of the longest matching prefix.

/// The capacity of the table.
pub const MAX_ALLOWED_IPS: usize = 1024;

/// One allowed prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllowedIp {
    pub v6: bool,
    /// The prefix, its bits after `len` cleared.
    pub addr: u128,
    /// The prefix length: at most 32 for IPv4, 128 for IPv6.
    pub len: u32,
    pub peer: u16,
}

/// The routing table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllowedIps {
    pub entries: [AllowedIp; MAX_ALLOWED_IPS],
    /// The number of entries in use, at the start of `entries`.
    pub count: usize,
}

/// The address width of a family.
fn width(v6: bool) -> u32 {
    if v6 {
        128
    } else {
        32
    }
}

/// `2^(width - len)`, the size of a prefix's block of addresses, or `None` if
/// it does not fit in a `u128` (`len == 0` for IPv6).
fn block(v6: bool, len: u32) -> Option<u128> {
    let host_bits = width(v6) - len;
    if host_bits >= 128 {
        return None;
    }
    Some(1u128 << host_bits)
}

/// Whether `addr/len` is a prefix of the family: the length within its width,
/// and an IPv4 address within 32 bits.
fn valid(v6: bool, addr: u128, len: u32) -> bool {
    if len > width(v6) {
        return false;
    }
    if v6 {
        return true;
    }
    addr <= u32::MAX as u128
}

/// `addr` with its bits after `len` cleared.
fn canonical(v6: bool, addr: u128, len: u32) -> u128 {
    match block(v6, len) {
        Some(b) => addr / b * b,
        None => 0,
    }
}

/// Whether `ip` is within the prefix `addr/len` (canonical).
fn matches(v6: bool, addr: u128, len: u32, ip: u128) -> bool {
    canonical(v6, ip, len) == addr
}

impl AllowedIps {
    /// An empty table.
    pub fn new() -> AllowedIps {
        AllowedIps {
            entries: [AllowedIp {
                v6: false,
                addr: 0,
                len: 0,
                peer: 0,
            }; MAX_ALLOWED_IPS],
            count: 0,
        }
    }

    /// Allows `addr/len` for `peer`, replacing the peer of that prefix if it
    /// is already in the table. Returns false, changing nothing, if the
    /// prefix is invalid (`len` beyond the family's width, or `addr` beyond
    /// it) or the table is full.
    pub fn insert(&mut self, v6: bool, addr: u128, len: u32, peer: u16) -> bool {
        if !valid(v6, addr, len) {
            return false;
        }
        let addr = canonical(v6, addr, len);
        let i = self.find(v6, addr, len);
        if i < self.count {
            self.entries[i].peer = peer;
            return true;
        }
        if self.count == MAX_ALLOWED_IPS {
            return false;
        }
        self.entries[self.count] = AllowedIp {
            v6,
            addr,
            len,
            peer,
        };
        self.count += 1;
        true
    }

    /// Removes every prefix of `peer`, keeping the others in order.
    pub fn remove_peer(&mut self, peer: u16) {
        let mut kept = 0;
        let mut i = 0;
        while i < self.count {
            let e = self.entries[i];
            if e.peer != peer {
                self.entries[kept] = e;
                kept += 1;
            }
            i += 1;
        }
        self.count = kept;
    }

    /// The index of the prefix `addr/len` (canonical), or `count` if it is not
    /// in the table.
    fn find(&self, v6: bool, addr: u128, len: u32) -> usize {
        let mut i = 0;
        while i < self.count
            && !(self.entries[i].v6 == v6
                && self.entries[i].len == len
                && self.entries[i].addr == addr)
        {
            i += 1;
        }
        i
    }

    /// The peer of the longest prefix matching `ip`, if any.
    pub fn lookup(&self, v6: bool, ip: u128) -> Option<u16> {
        let mut best: Option<AllowedIp> = None;
        let mut i = 0;
        while i < self.count {
            let e = self.entries[i];
            if e.v6 == v6 && matches(v6, e.addr, e.len, ip) {
                best = match best {
                    Some(b) if b.len >= e.len => Some(b),
                    _ => Some(e),
                };
            }
            i += 1;
        }
        // A `match` rather than `map`: closures are not translated to Lean.
        #[allow(clippy::manual_map)]
        match best {
            Some(b) => Some(b.peer),
            None => None,
        }
    }
}

impl Default for AllowedIps {
    fn default() -> Self {
        AllowedIps::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v4(a: u8, b: u8, c: u8, d: u8) -> u128 {
        u32::from_be_bytes([a, b, c, d]) as u128
    }

    #[test]
    fn longest_prefix_wins() {
        let mut t = AllowedIps::new();
        assert!(t.insert(false, v4(10, 0, 0, 0), 8, 1));
        assert!(t.insert(false, v4(10, 1, 0, 0), 16, 2));
        assert!(t.insert(false, v4(10, 1, 2, 3), 32, 3));
        assert!(t.insert(false, 0, 0, 4));
        assert_eq!(t.lookup(false, v4(10, 1, 2, 3)), Some(3));
        assert_eq!(t.lookup(false, v4(10, 1, 2, 4)), Some(2));
        assert_eq!(t.lookup(false, v4(10, 2, 0, 1)), Some(1));
        assert_eq!(t.lookup(false, v4(192, 168, 0, 1)), Some(4));
        // IPv6 is separate.
        assert_eq!(t.lookup(true, v4(10, 1, 2, 3)), None);
        assert!(t.insert(true, 0xfd00 << 112, 8, 5));
        assert!(t.insert(true, 0, 0, 6));
        assert_eq!(t.lookup(true, (0xfd00 << 112) | 1), Some(5));
        assert_eq!(t.lookup(true, 1), Some(6));
    }

    #[test]
    fn prefixes_are_canonical_and_unique() {
        let mut t = AllowedIps::new();
        // Host bits are dropped, so these are the same prefix.
        assert!(t.insert(false, v4(10, 0, 0, 5), 24, 1));
        assert!(t.insert(false, v4(10, 0, 0, 9), 24, 2));
        assert_eq!(t.count, 1);
        assert_eq!(t.entries[0].addr, v4(10, 0, 0, 0));
        assert_eq!(t.lookup(false, v4(10, 0, 0, 200)), Some(2));
    }

    #[test]
    fn rejects_invalid_prefixes_and_overflow() {
        let mut t = AllowedIps::new();
        assert!(!t.insert(false, 0, 33, 1));
        assert!(!t.insert(true, 0, 129, 1));
        assert!(!t.insert(false, 1 << 32, 8, 1));
        for i in 0..MAX_ALLOWED_IPS as u128 {
            assert!(t.insert(true, i << 64, 64, 1));
        }
        assert!(!t.insert(true, 1 << 127, 64, 1));
        // Replacing still works when full.
        assert!(t.insert(true, 3 << 64, 64, 9));
        assert_eq!(t.lookup(true, (3 << 64) | 77), Some(9));
    }

    #[test]
    fn removes_a_peers_prefixes() {
        let mut t = AllowedIps::new();
        assert!(t.insert(false, v4(10, 0, 0, 0), 8, 1));
        assert!(t.insert(false, v4(10, 1, 0, 0), 16, 2));
        assert!(t.insert(false, v4(10, 1, 2, 0), 24, 1));
        assert!(t.insert(true, 0, 0, 3));
        t.remove_peer(1);
        assert_eq!(t.count, 2);
        // The less specific prefix of another peer now matches.
        assert_eq!(t.lookup(false, v4(10, 1, 2, 3)), Some(2));
        assert_eq!(t.lookup(false, v4(10, 2, 0, 1)), None);
        assert_eq!(t.lookup(true, 7), Some(3));
        t.remove_peer(9);
        assert_eq!(t.count, 2);
    }
}
