//! Domain names, as the filter compares them: lowercase text with dots
//! between labels and no trailing dot (`ads.example.com`).
//!
//! DNS names are case-insensitive for ASCII letters (RFC 4343), so names are
//! lowercased; a trailing dot (the root) is dropped. Nothing else is
//! normalized: a name that is not a hostname simply matches no list entry.

/// The longest name: 253 characters (255 bytes in DNS wire format).
pub const MAX_NAME_LEN: usize = 253;

/// A domain name, lowercased, without a trailing dot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Name {
    bytes: [u8; MAX_NAME_LEN],
    len: usize,
}

/// `b`, with an ASCII capital letter made lowercase.
// Comparisons rather than `RangeInclusive::contains`, which the Lean model of
// `core` may not cover.
#[allow(clippy::manual_range_contains)]
pub fn lower(b: u8) -> u8 {
    if b >= b'A' && b <= b'Z' {
        b + 32
    } else {
        b
    }
}

impl Name {
    /// The name `text` (with or without a trailing dot), lowercased; `None`
    /// if it is empty or longer than [`MAX_NAME_LEN`].
    pub fn from_text(text: &[u8]) -> Option<Name> {
        let mut n = text.len();
        if n > 0 && text[n - 1] == b'.' {
            n -= 1;
        }
        if n == 0 || n > MAX_NAME_LEN {
            return None;
        }
        let mut bytes = [0u8; MAX_NAME_LEN];
        let mut i = 0;
        while i < n {
            bytes[i] = lower(text[i]);
            i += 1;
        }
        Some(Name { bytes, len: n })
    }

    /// The name's text.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalizes() {
        let n = Name::from_text(b"Ads.Example.COM.").unwrap();
        assert_eq!(n.as_bytes(), b"ads.example.com");
        assert_eq!(Name::from_text(b"x").unwrap().as_bytes(), b"x");
        assert!(Name::from_text(b"").is_none());
        assert!(Name::from_text(b".").is_none());
        assert!(Name::from_text(&[b'a'; 254]).is_none());
        assert!(Name::from_text(&[b'a'; 253]).is_some());
    }
}
