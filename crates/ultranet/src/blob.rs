//! The compiled blocklist file: what `ultranet-admin compile-list` writes and
//! the server loads.
//!
//! ```text
//! | "ULTRANET" (8) | version 1 (4, LE) | entries n (4, LE) | data length d (4, LE) |
//! | data (d bytes): the domains, concatenated | ends (4n bytes, LE): where each ends |
//! ```
//!
//! The entries are sorted; the verified [`diomede::blocklist::Blocklist::new`]
//! checks that, so this format needs no trust.

/// The file's first bytes.
pub const MAGIC: &[u8; 8] = b"ULTRANET";
/// The format version.
pub const VERSION: u32 = 1;
/// The length of the header.
pub const HEADER_LEN: usize = 20;

fn le32(b: &[u8], at: usize) -> usize {
    u32::from_le_bytes([b[at], b[at + 1], b[at + 2], b[at + 3]]) as usize
}

/// The number of entries and the length of the data of the blob `b`, if its
/// header is right and its length matches.
pub fn header(b: &[u8]) -> Option<(usize, usize)> {
    if b.len() < HEADER_LEN || &b[..8] != MAGIC || le32(b, 8) != VERSION as usize {
        return None;
    }
    let (n, d) = (le32(b, 12), le32(b, 16));
    let len = HEADER_LEN.checked_add(d)?.checked_add(n.checked_mul(4)?)?;
    (len == b.len()).then_some((n, d))
}

/// The data of the blob `b` (whose header is right), with its ends copied
/// into `ends`; `None` if `ends` is too short.
pub fn split<'a, 'e>(b: &'a [u8], ends: &'e mut [u32]) -> Option<(&'a [u8], &'e [u32])> {
    let (n, d) = header(b)?;
    if n > ends.len() {
        return None;
    }
    let at = HEADER_LEN + d;
    for (i, e) in ends[..n].iter_mut().enumerate() {
        *e = le32(b, at + 4 * i) as u32;
    }
    Some((&b[HEADER_LEN..at], &ends[..n]))
}

/// The length of the blob of `n` entries with `d` bytes of data.
pub fn len(n: usize, d: usize) -> usize {
    HEADER_LEN + d + 4 * n
}

/// Writes the blob of `data` and `ends` to the start of `out`, which must
/// hold [`len`] bytes; returns its length.
pub fn encode(data: &[u8], ends: &[u32], out: &mut [u8]) -> usize {
    let n = len(ends.len(), data.len());
    out[..8].copy_from_slice(MAGIC);
    out[8..12].copy_from_slice(&VERSION.to_le_bytes());
    out[12..16].copy_from_slice(&(ends.len() as u32).to_le_bytes());
    out[16..20].copy_from_slice(&(data.len() as u32).to_le_bytes());
    out[HEADER_LEN..HEADER_LEN + data.len()].copy_from_slice(data);
    for (i, e) in ends.iter().enumerate() {
        let at = HEADER_LEN + data.len() + 4 * i;
        out[at..at + 4].copy_from_slice(&e.to_le_bytes());
    }
    n
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips() {
        let data = b"ads.exampletracker.io";
        let ends = [11u32, 21];
        let mut out = [0u8; 64];
        let n = encode(data, &ends, &mut out);
        assert_eq!(n, len(2, data.len()));
        let mut e = [0u32; 4];
        let (d, en) = split(&out[..n], &mut e).unwrap();
        assert_eq!((d, en), (&data[..], &ends[..]));
        // Wrong length, magic, version; too many entries for the room.
        assert!(header(&out[..n - 1]).is_none());
        let mut bad = out;
        bad[0] = b'X';
        assert!(header(&bad[..n]).is_none());
        bad = out;
        bad[8] = 2;
        assert!(header(&bad[..n]).is_none());
        assert!(split(&out[..n], &mut e[..1]).is_none());
    }
}
