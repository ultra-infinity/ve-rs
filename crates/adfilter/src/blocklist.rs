//! The list of blocked domains.
//!
//! A [`Blocklist`] is a view of caller-provided storage: the names
//! concatenated in `data`, and in `ends` where each one ends. They must be in
//! strictly increasing byte order; [`Blocklist::new`] checks this (and that
//! the storage is consistent), so the code that built the list, sorting it
//! for instance, need not be trusted. Lookups are then binary searches.
//!
//! Listing a domain blocks its subdomains too: [`Blocklist::blocked`] is true
//! of `name` exactly when `name`, or the part of it after one of its dots, is
//! listed. `proofs/Adfilter/BlocklistTop.lean` proves both lookups.

/// Compares `a` and `b` byte by byte: -1, 0 or 1 as `a` comes before, is
/// equal to, or comes after `b` (a prefix comes first).
pub fn compare(a: &[u8], b: &[u8]) -> i8 {
    let mut i = 0;
    while i < a.len() && i < b.len() && a[i] == b[i] {
        i += 1;
    }
    if i < a.len() && i < b.len() {
        if a[i] < b[i] {
            -1
        } else {
            1
        }
    } else if a.len() < b.len() {
        -1
    } else if a.len() > b.len() {
        1
    } else {
        0
    }
}

/// Where entry `i` starts: 0 for the first, else where the previous one ends.
fn start_of(ends: &[u32], i: usize) -> usize {
    if i == 0 {
        0
    } else {
        ends[i - 1] as usize
    }
}

/// Whether entry `i` (which `ends` has) is valid: non-empty, within `data`,
/// and after the previous entry, if any (which is then valid).
fn entry_ok(data: &[u8], ends: &[u32], i: usize) -> bool {
    let start = start_of(ends, i);
    let end = ends[i] as usize;
    if end <= start || end > data.len() {
        return false;
    }
    if i == 0 {
        return true;
    }
    compare(&data[start_of(ends, i - 1)..start], &data[start..end]) < 0
}

/// Whether `data` and `ends` lay out a valid list: every entry non-empty and
/// within `data`, the entries in strictly increasing order.
fn well_formed(data: &[u8], ends: &[u32]) -> bool {
    let mut i = 0;
    while i < ends.len() && entry_ok(data, ends, i) {
        i += 1;
    }
    i == ends.len()
}

/// Whether `name` is an entry of the well-formed list `data`, `ends`.
fn search(data: &[u8], ends: &[u32], name: &[u8]) -> bool {
    let mut lo = 0;
    let mut hi = ends.len();
    let mut found = false;
    while lo < hi && !found {
        let mid = lo + (hi - lo) / 2;
        let c = compare(&data[start_of(ends, mid)..ends[mid] as usize], name);
        if c == 0 {
            found = true;
        } else if c < 0 {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    found
}

/// Whether `name`, or the part of it after one of its dots, is an entry of
/// the well-formed list `data`, `ends`.
fn search_suffixes(data: &[u8], ends: &[u32], name: &[u8]) -> bool {
    let mut found = search(data, ends, name);
    let mut i = 0;
    while i < name.len() && !found {
        if name[i] == b'.' {
            found = search(data, ends, &name[i + 1..]);
        }
        i += 1;
    }
    found
}

/// A sorted list of blocked domains.
#[derive(Debug, Clone, Copy)]
pub struct Blocklist<'a> {
    data: &'a [u8],
    ends: &'a [u32],
}

impl<'a> Blocklist<'a> {
    /// The list whose `i`-th entry is `data[ends[i - 1]..ends[i]]` (from 0 for
    /// the first). `None` unless every entry is non-empty and within `data`,
    /// and the entries are in strictly increasing order.
    pub fn new(data: &'a [u8], ends: &'a [u32]) -> Option<Blocklist<'a>> {
        if well_formed(data, ends) {
            Some(Blocklist { data, ends })
        } else {
            None
        }
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    /// Whether the list is empty.
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    /// Whether `name` is an entry.
    pub fn contains(&self, name: &[u8]) -> bool {
        search(self.data, self.ends, name)
    }

    /// Whether `name` is blocked: it is an entry, or a subdomain of one.
    pub fn blocked(&self, name: &[u8]) -> bool {
        search_suffixes(self.data, self.ends, name)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use std::vec::Vec;

    /// Lays out sorted names as a list's storage.
    fn storage(names: &[&str]) -> (Vec<u8>, Vec<u32>) {
        let mut data = Vec::new();
        let mut ends = Vec::new();
        for n in names {
            data.extend_from_slice(n.as_bytes());
            ends.push(data.len() as u32);
        }
        (data, ends)
    }

    #[test]
    fn compares_bytewise() {
        assert_eq!(compare(b"a", b"b"), -1);
        assert_eq!(compare(b"b", b"a"), 1);
        assert_eq!(compare(b"ab", b"abc"), -1);
        assert_eq!(compare(b"abc", b"ab"), 1);
        assert_eq!(compare(b"abc", b"abc"), 0);
        assert_eq!(compare(b"", b""), 0);
    }

    #[test]
    fn checks_the_storage() {
        let (data, ends) = storage(&["ads.example", "doubleclick.net", "tracker.io"]);
        assert!(Blocklist::new(&data, &ends).is_some());
        // Out of order, duplicated, empty or out of bounds entries.
        let (data, ends) = storage(&["b.com", "a.com"]);
        assert!(Blocklist::new(&data, &ends).is_none());
        let (data, ends) = storage(&["a.com", "a.com"]);
        assert!(Blocklist::new(&data, &ends).is_none());
        assert!(Blocklist::new(b"a.com", &[5, 5]).is_none());
        assert!(Blocklist::new(b"a.com", &[6]).is_none());
        assert!(Blocklist::new(b"", &[]).unwrap().is_empty());
    }

    #[test]
    fn blocks_listed_domains_and_subdomains() {
        let (data, ends) = storage(&["ads.example", "doubleclick.net", "tracker.io"]);
        let l = Blocklist::new(&data, &ends).unwrap();
        for n in ["doubleclick.net", "ad.doubleclick.net", "x.y.ads.example", "tracker.io"] {
            assert!(l.blocked(n.as_bytes()), "{n}");
        }
        for n in ["example", "notdoubleclick.net", "doubleclick.net.evil", "io", "ads.example.org"] {
            assert!(!l.blocked(n.as_bytes()), "{n}");
        }
        assert!(l.contains(b"tracker.io"));
        assert!(!l.contains(b"a.tracker.io"));
    }

    #[test]
    fn binary_search_matches_a_scan() {
        let mut names: Vec<std::string::String> =
            (0..300).map(|i| std::format!("d{}.example", i * 7 % 1000)).collect();
        names.sort();
        names.dedup();
        let refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
        let (data, ends) = storage(&refs);
        let l = Blocklist::new(&data, &ends).unwrap();
        for i in 0..1000 {
            let n = std::format!("d{i}.example");
            assert_eq!(l.contains(n.as_bytes()), names.contains(&n), "{n}");
        }
    }
}
