//! The server name of a TLS ClientHello (RFC 8446 §4.1.2, RFC 6066 §3).
//!
//! ```text
//! record:      | type 22 (1) | version 3.x (2) | length (2) | fragment |
//! handshake:   | type 1 (1) | length (3) | ClientHello |
//! ClientHello: | version (2) | random (32) | session_id <1> | cipher_suites <2> |
//!              | compression_methods <1> | [extensions <2>] |
//! extension:   | type (2) | data <2> |
//! server_name: | ServerNameList length (2) | name type 0 (1) | HostName <2> | ...
//! ```
//!
//! (`<n>`: a vector whose length takes `n` bytes.) [`ClientHello`] reads the
//! first record of a TLS stream, which must hold the whole ClientHello; bytes
//! after it are not read. The vector lengths must be consistent and the
//! extensions must fill their vector exactly. The server name is the first
//! entry of the first server_name extension, which must be a host name; it is
//! handed back as a [`Name`], lowercased.

use crate::name::Name;
use untrusted::{Validate, ValidationError};

/// The HTTPS port.
pub const PORT: u16 = 443;
/// The record content type of handshake messages.
pub const CONTENT_HANDSHAKE: u8 = 22;
/// The handshake message type of a ClientHello.
pub const CLIENT_HELLO: u8 = 1;
/// The extension type of server_name.
pub const EXT_SERVER_NAME: usize = 0;
/// The server name type of a host name.
pub const HOST_NAME: u8 = 0;
/// Length of a record header.
pub const RECORD_HEADER_LEN: usize = 5;
/// Length of a handshake message header.
pub const HANDSHAKE_HEADER_LEN: usize = 4;
/// Length of the legacy version and random of a ClientHello.
pub const VERSION_RANDOM_LEN: usize = 34;

/// A ClientHello, with the server name it asks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClientHello {
    pub server_name: Option<Name>,
}

/// The big-endian 16-bit number at `b[at..at + 2]`.
fn be16(b: &[u8], at: usize) -> usize {
    b[at] as usize * 256 + b[at + 1] as usize
}

/// The end of the vector with a 1-byte length at `b[pos..end]`, if it ends
/// by `end`.
fn skip_vector8(b: &[u8], pos: usize, end: usize) -> Option<usize> {
    if pos >= end {
        return None;
    }
    let n = b[pos] as usize;
    if n > end - pos - 1 {
        None
    } else {
        Some(pos + 1 + n)
    }
}

/// The end of the vector with a 2-byte length at `b[pos..end]`, if it ends
/// by `end`.
fn skip_vector16(b: &[u8], pos: usize, end: usize) -> Option<usize> {
    if end - pos < 2 {
        return None;
    }
    let n = be16(b, pos);
    if n > end - pos - 2 {
        None
    } else {
        Some(pos + 2 + n)
    }
}

/// Walks the extensions filling `b[pos..end]`: whether there is a
/// server_name extension and, for the first, the position and length of its
/// data; `None` if they do not fill `b[pos..end]` exactly.
// The nested `if` keeps the extracted model small: with `&&`, Aeneas
// duplicates the rest of the loop body.
#[allow(clippy::collapsible_if)]
fn find_server_name(b: &[u8], start: usize, end: usize) -> Option<(bool, usize, usize)> {
    let mut pos = start;
    let mut found = false;
    let mut at = 0;
    let mut len = 0;
    let mut bad = false;
    while pos < end && !bad {
        if end - pos < 4 {
            bad = true;
        } else {
            let ty = be16(b, pos);
            let n = be16(b, pos + 2);
            if n > end - pos - 4 {
                bad = true;
            } else {
                if !found {
                    if ty == EXT_SERVER_NAME {
                        found = true;
                        at = pos + 4;
                        len = n;
                    }
                }
                pos += 4 + n;
            }
        }
    }
    if bad {
        None
    } else {
        Some((found, at, len))
    }
}

/// The host name in the server_name extension data `b[at..at + len]`: the
/// first entry of the list, which must be a host name.
fn host_name(b: &[u8], at: usize, len: usize) -> Option<Name> {
    if len < 5 {
        return None;
    }
    if be16(b, at) != len - 2 {
        return None;
    }
    if b[at + 2] != HOST_NAME {
        return None;
    }
    let n = be16(b, at + 3);
    if n > len - 5 {
        return None;
    }
    Name::from_text(&b[at + 5..at + 5 + n])
}

impl Validate<&[u8]> for ClientHello {
    type Err = ValidationError;

    fn validate(r: &[u8]) -> Result<Self, ValidationError> {
        // The record header: a handshake record, versions 3.0 to 3.4.
        if r.len() < RECORD_HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        if r[0] != CONTENT_HANDSHAKE {
            return Err(ValidationError::OutOfRange);
        }
        if r[1] != 3 {
            return Err(ValidationError::OutOfRange);
        }
        if r[2] > 4 {
            return Err(ValidationError::OutOfRange);
        }
        let fragment_len = be16(r, 3);
        if fragment_len > r.len() - RECORD_HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let record_end = RECORD_HEADER_LEN + fragment_len;
        // The handshake header: a ClientHello, within the record.
        if fragment_len < HANDSHAKE_HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        if r[RECORD_HEADER_LEN] != CLIENT_HELLO {
            return Err(ValidationError::OutOfRange);
        }
        let body = RECORD_HEADER_LEN + HANDSHAKE_HEADER_LEN;
        let body_len = r[RECORD_HEADER_LEN + 1] as usize * 65536 + be16(r, RECORD_HEADER_LEN + 2);
        if body_len > record_end - body {
            return Err(ValidationError::EndOfInput);
        }
        let end = body + body_len;
        // The ClientHello.
        if body_len < VERSION_RANDOM_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let session_id = body + VERSION_RANDOM_LEN;
        let cipher_suites = match skip_vector8(r, session_id, end) {
            Some(p) => p,
            None => return Err(ValidationError::EndOfInput),
        };
        let compression_methods = match skip_vector16(r, cipher_suites, end) {
            Some(p) => p,
            None => return Err(ValidationError::EndOfInput),
        };
        let extensions = match skip_vector8(r, compression_methods, end) {
            Some(p) => p,
            None => return Err(ValidationError::EndOfInput),
        };
        if extensions == end {
            return Ok(ClientHello { server_name: None });
        }
        let extensions_end = match skip_vector16(r, extensions, end) {
            Some(p) => p,
            None => return Err(ValidationError::EndOfInput),
        };
        if extensions_end != end {
            return Err(ValidationError::TrailingData);
        }
        let (found, at, len) = match find_server_name(r, extensions + 2, end) {
            Some(f) => f,
            None => return Err(ValidationError::OutOfRange),
        };
        if !found {
            return Ok(ClientHello { server_name: None });
        }
        match host_name(r, at, len) {
            Some(name) => Ok(ClientHello { server_name: Some(name) }),
            None => Err(ValidationError::OutOfRange),
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use std::vec::Vec;
    use untrusted::Untrusted;

    fn vector16(out: &mut Vec<u8>, data: &[u8]) {
        out.extend_from_slice(&(data.len() as u16).to_be_bytes());
        out.extend_from_slice(data);
    }

    fn extension(ty: u16, data: &[u8]) -> Vec<u8> {
        let mut e = ty.to_be_bytes().to_vec();
        vector16(&mut e, data);
        e
    }

    fn sni(host: &[u8]) -> Vec<u8> {
        let mut entry = std::vec![HOST_NAME];
        vector16(&mut entry, host);
        let mut list = Vec::new();
        vector16(&mut list, &entry);
        extension(0, &list)
    }

    /// A ClientHello record with the extensions `exts` (none if `None`).
    fn hello(exts: Option<&[Vec<u8>]>) -> Vec<u8> {
        let mut body = std::vec![3, 3];
        body.extend_from_slice(&[7; 32]);
        body.push(32);
        body.extend_from_slice(&[9; 32]);
        vector16(&mut body, &[0x13, 0x01, 0x13, 0x02]);
        body.extend_from_slice(&[1, 0]);
        if let Some(exts) = exts {
            vector16(&mut body, &exts.concat());
        }
        let mut hs = std::vec![CLIENT_HELLO, 0];
        hs.extend_from_slice(&(body.len() as u16).to_be_bytes());
        hs.extend_from_slice(&body);
        let mut r = std::vec![CONTENT_HANDSHAKE, 3, 1];
        vector16(&mut r, &hs);
        r
    }

    fn validate(r: &[u8]) -> Result<ClientHello, ValidationError> {
        Untrusted::new(r).validate::<ClientHello>()
    }

    fn server_name(r: &[u8]) -> Option<Vec<u8>> {
        validate(r).unwrap().server_name.map(|n| n.as_bytes().to_vec())
    }

    #[test]
    fn finds_the_server_name() {
        // A large key share before the server name, as browsers send.
        let exts = [
            extension(43, &[2, 3, 4]),
            extension(51, &[0x11; 1300]),
            sni(b"Ads.Example.com"),
            extension(0, &[0; 9]),
        ];
        let mut r = hello(Some(&exts));
        assert_eq!(server_name(&r).as_deref(), Some(&b"ads.example.com"[..]));
        // Bytes after the record are not read.
        r.extend_from_slice(&[23, 3, 3, 0, 1, 0]);
        assert_eq!(server_name(&r).as_deref(), Some(&b"ads.example.com"[..]));
        assert_eq!(server_name(&hello(Some(&[extension(10, &[0, 2, 0, 29])]))), None);
        assert_eq!(server_name(&hello(None)), None);
    }

    #[test]
    fn rejects_other_data() {
        let r = hello(Some(&[sni(b"a.com")]));
        // Not a handshake record; not a ClientHello; truncated.
        let mut p = r.clone();
        p[0] = 23;
        assert!(validate(&p).is_err());
        let mut p = r.clone();
        p[5] = 2;
        assert!(validate(&p).is_err());
        assert!(validate(&r[..r.len() - 1]).is_err());
        assert!(validate(&r[..7]).is_err());
        // Extensions not filling their vector; a host name past the end of
        // its extension; a server name that is not a host name; an empty
        // host name.
        let n = r.len();
        let mut p = r.clone();
        p[n - 11] = 9;
        assert!(validate(&p).is_err());
        let mut p = r.clone();
        p[n - 6] = 0x40;
        assert!(validate(&p).is_err());
        let mut e = sni(b"a.com");
        e[6] = 1;
        assert!(validate(&hello(Some(&[e]))).is_err());
        assert!(validate(&hello(Some(&[sni(b"")]))).is_err());
    }
}
