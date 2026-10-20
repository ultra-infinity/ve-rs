//! The configuration file: a subset of the `wg-quick` format.
//!
//! ```text
//! [Interface]
//! PrivateKey = <base64>
//! ListenPort = 51820
//!
//! [Peer]
//! PublicKey = <base64>
//! PresharedKey = <base64>          # optional
//! Endpoint = 192.0.2.1:51820       # optional; [2001:db8::1]:51820 for IPv6
//! AllowedIPs = 10.0.0.2/32, fd00::2/128
//! PersistentKeepalive = 25         # optional, seconds
//! ```
//!
//! Addresses of the interface itself are set outside, with `ip`. Parsed into
//! fixed-size arrays: there is no allocator.

use core::net::{IpAddr, SocketAddr};
use wireguard::device::MAX_PEERS;

/// The most allowed IPs of one peer.
pub const MAX_ALLOWED: usize = 16;

/// A peer of the configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PeerConfig {
    pub public: [u8; 32],
    pub psk: [u8; 32],
    pub endpoint: Option<SocketAddr>,
    /// `(is IPv6, address, prefix length)`, with IPv4 addresses in the low 32
    /// bits.
    pub allowed_ips: [(bool, u128, u32); MAX_ALLOWED],
    pub allowed_count: usize,
    /// Seconds; 0 if off.
    pub persistent_keepalive: u64,
}

const NO_PEER: PeerConfig = PeerConfig {
    public: [0; 32],
    psk: [0; 32],
    endpoint: None,
    allowed_ips: [(false, 0, 0); MAX_ALLOWED],
    allowed_count: 0,
    persistent_keepalive: 0,
};

/// The whole configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
    pub private: [u8; 32],
    pub listen_port: u16,
    pub peers: [PeerConfig; MAX_PEERS],
    pub peer_count: usize,
}

/// Decodes standard base64 (with padding) into `out`; returns its length.
pub fn base64(s: &str, out: &mut [u8]) -> Result<usize, &'static str> {
    fn digit(c: u8) -> Result<u32, &'static str> {
        Ok(match c {
            b'A'..=b'Z' => c - b'A',
            b'a'..=b'z' => c - b'a' + 26,
            b'0'..=b'9' => c - b'0' + 52,
            b'+' => 62,
            b'/' => 63,
            _ => return Err("not base64"),
        } as u32)
    }
    let s = s.trim().as_bytes();
    if !s.len().is_multiple_of(4) {
        return Err("base64 length is not a multiple of 4");
    }
    let mut n = 0;
    for chunk in s.chunks(4) {
        let pad = chunk.iter().rev().take_while(|&&c| c == b'=').count();
        if pad > 2 {
            return Err("bad base64 padding");
        }
        let mut v = 0u32;
        for &c in &chunk[..4 - pad] {
            v = v << 6 | digit(c)?;
        }
        v <<= 6 * pad as u32;
        for &b in &[(v >> 16) as u8, (v >> 8) as u8, v as u8][..3 - pad] {
            *out.get_mut(n).ok_or("base64 too long")? = b;
            n += 1;
        }
    }
    Ok(n)
}

/// Encodes standard base64 (with padding) into `out`; returns it as text.
pub fn to_base64<'a>(bytes: &[u8], out: &'a mut [u8]) -> &'a str {
    const A: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut n = 0;
    for chunk in bytes.chunks(3) {
        let mut v = 0u32;
        for (i, &b) in chunk.iter().enumerate() {
            v |= (b as u32) << (16 - 8 * i);
        }
        for i in 0..4 {
            out[n] = if i <= chunk.len() {
                A[(v >> (18 - 6 * i) & 63) as usize]
            } else {
                b'='
            };
            n += 1;
        }
    }
    core::str::from_utf8(&out[..n]).unwrap_or("")
}

/// Decodes a base64 key.
pub fn key(value: &str) -> Result<[u8; 32], &'static str> {
    let mut k = [0u8; 33];
    if base64(value, &mut k)? != 32 {
        return Err("a key must be 32 bytes");
    }
    Ok(k[..32].try_into().unwrap())
}

/// Parses `addr/len`.
fn prefix(s: &str) -> Result<(bool, u128, u32), &'static str> {
    let (addr, len) = s
        .split_once('/')
        .ok_or("an allowed IP has no prefix length")?;
    let len: u32 = len.parse().map_err(|_| "bad prefix length")?;
    match addr.parse::<IpAddr>().map_err(|_| "bad address")? {
        IpAddr::V4(a) => Ok((false, u32::from(a) as u128, len)),
        IpAddr::V6(a) => Ok((true, u128::from(a), len)),
    }
}

/// A parse error, and the line it is on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Error {
    pub line: usize,
    pub message: &'static str,
}

impl Config {
    /// Parses a configuration file.
    pub fn parse(text: &str) -> Result<Config, Error> {
        let mut c = Config {
            private: [0; 32],
            listen_port: 51820,
            peers: [NO_PEER; MAX_PEERS],
            peer_count: 0,
        };
        let mut has_private = false;
        let mut in_peer = false;
        for (n, line) in text.lines().enumerate() {
            let err = |message| Error {
                line: n + 1,
                message,
            };
            let line = line.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            if line == "[Interface]" {
                in_peer = false;
                continue;
            }
            if line == "[Peer]" {
                if c.peer_count == MAX_PEERS {
                    return Err(err("too many peers"));
                }
                c.peer_count += 1;
                in_peer = true;
                continue;
            }
            let (name, value) = line.split_once('=').ok_or(err("expected `Name = value`"))?;
            let (name, value) = (name.trim(), value.trim());
            if in_peer {
                let p = &mut c.peers[c.peer_count - 1];
                match name {
                    "PublicKey" => p.public = key(value).map_err(err)?,
                    "PresharedKey" => p.psk = key(value).map_err(err)?,
                    "Endpoint" => {
                        p.endpoint = Some(value.parse().map_err(|_| err("bad endpoint"))?)
                    }
                    "AllowedIPs" => {
                        for s in value.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                            if p.allowed_count == MAX_ALLOWED {
                                return Err(err("too many allowed IPs"));
                            }
                            p.allowed_ips[p.allowed_count] = prefix(s).map_err(err)?;
                            p.allowed_count += 1;
                        }
                    }
                    "PersistentKeepalive" => {
                        p.persistent_keepalive =
                            value.parse().map_err(|_| err("bad keepalive interval"))?
                    }
                    _ => return Err(err("unknown peer setting")),
                }
            } else {
                match name {
                    "PrivateKey" => {
                        c.private = key(value).map_err(err)?;
                        has_private = true;
                    }
                    "ListenPort" => c.listen_port = value.parse().map_err(|_| err("bad port"))?,
                    _ => return Err(err("unknown interface setting")),
                }
            }
        }
        if !has_private {
            return Err(Error {
                line: 0,
                message: "no PrivateKey",
            });
        }
        Ok(c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base64_round_trips() {
        let mut text = [0u8; 64];
        let mut back = [0u8; 48];
        for n in 0..40u8 {
            let bytes: Vec<u8> = (0..n).map(|i| i.wrapping_mul(37)).collect();
            let s = to_base64(&bytes, &mut text);
            let m = base64(s, &mut back).unwrap();
            assert_eq!(&back[..m], &bytes[..]);
        }
        assert_eq!(to_base64(b"foobar", &mut text), "Zm9vYmFy");
        let m = base64("Zm9vYg==", &mut back).unwrap();
        assert_eq!(&back[..m], b"foob");
        assert!(base64("Zm9v*", &mut back).is_err());
    }

    #[test]
    fn parses_a_config() {
        let mut buf = [0u8; 64];
        let k = to_base64(&[7; 32], &mut buf).to_string();
        let text = format!(
            "[Interface]\nPrivateKey = {k}\nListenPort = 1234\n\n\
             [Peer] # a comment\nPublicKey = {k}\nEndpoint = [fd00::1]:51820\n\
             AllowedIPs = 10.0.0.0/24, fd00::/64\nPersistentKeepalive = 25\n"
        );
        let c = Config::parse(&text).unwrap();
        assert_eq!(c.private, [7; 32]);
        assert_eq!(c.listen_port, 1234);
        assert_eq!(c.peer_count, 1);
        let p = &c.peers[0];
        assert_eq!(p.endpoint, Some("[fd00::1]:51820".parse().unwrap()));
        assert_eq!(p.allowed_count, 2);
        assert_eq!(p.allowed_ips[0], (false, 0x0a00_0000, 24));
        assert_eq!(p.allowed_ips[1], (true, 0xfd00 << 112, 64));
        assert_eq!(p.persistent_keepalive, 25);
        assert_eq!(
            Config::parse("[Interface]\nListenPort = 1\n")
                .err()
                .map(|e| e.message),
            Some("no PrivateKey")
        );
        assert_eq!(
            Config::parse("[Interface]\nFoo = 1\n").err(),
            Some(Error {
                line: 2,
                message: "unknown interface setting"
            })
        );
    }
}
