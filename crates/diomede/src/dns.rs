//! DNS queries and the empty answers to them (RFC 1035 §4.1).
//!
//! ```text
//! header: | ID (2) | flags (2) | QDCOUNT (2) | ANCOUNT (2) | NSCOUNT (2) | ARCOUNT (2) |
//! question: | QNAME (length-prefixed labels, ending with 0) | QTYPE (2) | QCLASS (2) |
//! ```
//!
//! [`DnsQuery`] accepts a standard query (QR = 0, opcode 0) with exactly one
//! question and no answer or authority records; additional records (such as
//! the EDNS OPT record) may follow and are not read. The name must be plain
//! labels of 1 to 63 bytes (no compression pointers) forming a name of at
//! most 253 characters, not the root.
//!
//! [`answer`] writes an answer with no records: the same ID and question
//! (byte for byte, so resolvers that randomize letter case accept it),
//! QR = 1, RD copied, RA = 1, and a response code: NXDOMAIN (the name does
//! not exist) or NOERROR (no records of the type asked for).

use crate::name::{Name, MAX_NAME_LEN};
use untrusted::{BigEndian, Decode, Untrusted, Validate, ValidationError};

/// The DNS port.
pub const PORT: u16 = 53;
/// Length of the header.
pub const HEADER_LEN: usize = 12;
/// The longest label.
pub const MAX_LABEL_LEN: usize = 63;
/// The response code "name error": the name does not exist.
pub const NXDOMAIN: u8 = 3;
/// The response code "no error": with no records, there are none of the type
/// asked for.
pub const NOERROR: u8 = 0;
/// The query type of SVCB records.
pub const TYPE_SVCB: u16 = 64;
/// The query type of HTTPS records, which carry Encrypted ClientHello keys.
pub const TYPE_HTTPS: u16 = 65;

/// The header.
#[derive(Decode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct DnsHeader {
    pub id: BigEndian<u16>,
    /// QR, opcode (4 bits), AA, TC, RD; RA, Z (3 bits), RCODE (4 bits).
    pub flags: BigEndian<u16>,
    pub qdcount: BigEndian<u16>,
    pub ancount: BigEndian<u16>,
    pub nscount: BigEndian<u16>,
    pub arcount: BigEndian<u16>,
}

/// A standard query with one question.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DnsQuery {
    pub header: DnsHeader,
    /// The name asked about, lowercased, without the trailing dot.
    pub name: Name,
    pub qtype: u16,
    pub qclass: u16,
    /// The length of the question (QNAME, QTYPE and QCLASS), which starts
    /// right after the header.
    pub question_len: usize,
}

/// A [`DnsQuery`] with the message it was decoded from, which [`answer`]
/// copies the question from.
pub struct Query<'a> {
    pub msg: &'a [u8],
    pub query: DnsQuery,
}

impl<'a> Validate<&'a [u8]> for Query<'a> {
    type Err = ValidationError;

    fn validate(msg: &'a [u8]) -> Result<Self, ValidationError> {
        let query = DnsQuery::validate(msg)?;
        Ok(Query { msg, query })
    }
}

/// Copies `msg[from..from + len]` to `text[at..at + len]`, which must exist.
fn copy_label(text: &mut [u8; MAX_NAME_LEN], at: usize, msg: &[u8], from: usize, len: usize) {
    let mut j = 0;
    while j < len {
        text[at + j] = msg[from + j];
        j += 1;
    }
}

/// The name at `msg[HEADER_LEN..]` (labels, ending with a zero length) as
/// dotted text in `text`: its length and the position after the name, or
/// `None` if it is not a valid name.
fn read_name(msg: &[u8], text: &mut [u8; MAX_NAME_LEN]) -> Option<(usize, usize)> {
    let mut pos = HEADER_LEN;
    let mut n = 0;
    let mut done = false;
    let mut bad = false;
    while !done && !bad {
        if pos >= msg.len() {
            bad = true;
        } else {
            let l = msg[pos] as usize;
            let sep = if n > 0 { 1 } else { 0 };
            if l == 0 {
                done = true;
                pos += 1;
            } else if l > MAX_LABEL_LEN || l > msg.len() - pos - 1 || n + sep + l > MAX_NAME_LEN {
                bad = true;
            } else {
                if sep == 1 {
                    text[n] = b'.';
                }
                copy_label(text, n + sep, msg, pos + 1, l);
                n += sep + l;
                pos += 1 + l;
            }
        }
    }
    if bad || n == 0 {
        None
    } else {
        Some((n, pos))
    }
}

impl Validate<&[u8]> for DnsQuery {
    type Err = ValidationError;

    fn validate(msg: &[u8]) -> Result<Self, ValidationError> {
        if msg.len() < HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let header = Untrusted::new(&msg[..HEADER_LEN]).read_all::<DnsHeader>()?;
        // QR = 0 (a query) and opcode 0 (a standard query): the top 5 bits.
        if header.flags.0 / 2048 != 0 {
            return Err(ValidationError::OutOfRange);
        }
        if header.qdcount.0 != 1 || header.ancount.0 != 0 || header.nscount.0 != 0 {
            return Err(ValidationError::OutOfRange);
        }
        let mut text = [0u8; MAX_NAME_LEN];
        let (n, end) = match read_name(msg, &mut text) {
            Some(r) => r,
            None => return Err(ValidationError::OutOfRange),
        };
        if msg.len() - end < 4 {
            return Err(ValidationError::EndOfInput);
        }
        let name = match Name::from_text(&text[..n]) {
            Some(name) => name,
            None => return Err(ValidationError::OutOfRange),
        };
        Ok(DnsQuery {
            header,
            name,
            qtype: msg[end] as u16 * 256 + msg[end + 1] as u16,
            qclass: msg[end + 2] as u16 * 256 + msg[end + 3] as u16,
            question_len: end + 4 - HEADER_LEN,
        })
    }
}

/// Writes to the start of `out` the answer to the query `q`, which was
/// decoded from `msg`, with no records and the response code `rcode`
/// (modulo 16). Returns its length, or `None` if `out` is too short (or `q`
/// is not from `msg`).
pub fn answer(msg: &[u8], q: &DnsQuery, rcode: u8, out: &mut [u8]) -> Option<usize> {
    let n = HEADER_LEN + q.question_len;
    if n > msg.len() || n > out.len() {
        return None;
    }
    let id = q.header.id.0;
    // QR = 1, opcode 0, AA = 0, TC = 0, RD as asked; RA = 1, Z = 0, RCODE.
    let rd = (q.header.flags.0 / 256 % 2) as u8;
    let header = [
        (id / 256) as u8,
        (id % 256) as u8,
        0x80 + rd,
        0x80 + rcode % 16,
        0,
        1,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i = 0;
    while i < HEADER_LEN {
        out[i] = header[i];
        i += 1;
    }
    while i < n {
        out[i] = msg[i];
        i += 1;
    }
    Some(n)
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use std::vec::Vec;

    /// A query for `name` (dotted) with `flags`.
    fn query(name: &str, flags: u16) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(&0xBEEFu16.to_be_bytes());
        m.extend_from_slice(&flags.to_be_bytes());
        m.extend_from_slice(&[0, 1, 0, 0, 0, 0, 0, 1]);
        for label in name.split('.').filter(|l| !l.is_empty()) {
            m.push(label.len() as u8);
            m.extend_from_slice(label.as_bytes());
        }
        m.push(0);
        m.extend_from_slice(&[0, 1, 0, 1]);
        // An EDNS OPT record, not read.
        m.extend_from_slice(&[0, 0, 41, 4, 208, 0, 0, 0, 0, 0, 0]);
        m
    }

    fn validate(m: &[u8]) -> Result<DnsQuery, ValidationError> {
        Untrusted::new(m).validate::<DnsQuery>()
    }

    #[test]
    fn decodes_queries() {
        let m = query("Ads.Example.COM", 0x0100);
        let q = validate(&m).unwrap();
        assert_eq!(q.name.as_bytes(), b"ads.example.com");
        assert_eq!((q.qtype, q.qclass), (1, 1));
        assert_eq!(q.question_len, 1 + 3 + 1 + 7 + 1 + 3 + 1 + 4);
        assert_eq!(q.header.id, BigEndian(0xBEEF));
    }

    #[test]
    fn rejects_other_messages() {
        // A response, another opcode, two questions, an answer record.
        let mut m = query("a.com", 0x8100);
        assert!(validate(&m).is_err());
        m = query("a.com", 0x2800);
        assert!(validate(&m).is_err());
        m = query("a.com", 0x0100);
        m[5] = 2;
        assert!(validate(&m).is_err());
        m[5] = 1;
        m[7] = 1;
        assert!(validate(&m).is_err());
        // The root, a compression pointer, a label past the end, no QTYPE.
        assert!(validate(&query("", 0)).is_err());
        let mut p = query("a.com", 0);
        p[12] = 0xC0;
        assert!(validate(&p).is_err());
        let mut p = query("a.com", 0);
        p[12] = 60;
        assert!(validate(&p[..20]).is_err());
        assert!(validate(&query("a.com", 0)[..19]).is_err());
        // A 64-byte label, and a name over 253 characters.
        let long = std::format!("{}.com", "a".repeat(64));
        assert!(validate(&query(&long, 0)).is_err());
        let labels: Vec<std::string::String> = (0..5).map(|_| "b".repeat(63)).collect();
        assert!(validate(&query(&labels.join("."), 0)).is_err());
        let labels: Vec<std::string::String> = (0..4).map(|_| "b".repeat(62)).collect();
        assert!(validate(&query(&labels.join("."), 0)).is_ok());
    }

    #[test]
    fn answers_nxdomain() {
        let m = query("ads.example", 0x0100);
        let q = validate(&m).unwrap();
        let mut out = [0u8; 512];
        let n = answer(&m, &q, NXDOMAIN, &mut out).unwrap();
        assert_eq!(n, 12 + q.question_len);
        assert_eq!(&out[..12], &[0xBE, 0xEF, 0x81, 0x83, 0, 1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(&out[12..n], &m[12..n]);
        assert!(answer(&m, &q, NXDOMAIN, &mut out[..n - 1]).is_none());
        assert_eq!(answer(&m, &q, NOERROR, &mut out), Some(n));
        assert_eq!(&out[2..4], &[0x81, 0x80]);
    }
}
