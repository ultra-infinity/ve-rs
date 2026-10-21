//! `ultranet-admin`: administers an ultranet server.
//!
//! ```text
//! ultranet-admin genkey --out FILE
//!     a new private key in FILE (readable only by its owner); prints the public key
//! ultranet-admin compile-list --list FILE [--list FILE ...] --out FILE
//!     compiles hosts files or domain lists into a blocklist file for the server
//! ultranet-admin add-peer --peers FILE --name NAME --server-key FILE --endpoint HOST:PORT
//!         [--subnet4 10.77.0.0/16] [--subnet6 fd77::/64] [--qr] [--reload]
//!     adds a client; prints its WireGuard configuration (as a QR code with --qr)
//! ultranet-admin remove-peer --peers FILE --name NAME [--reload]
//! ultranet-admin list-peers --peers FILE
//! ultranet-admin stats --stats FILE
//! ```
//!
//! `--reload` asks the server to read its peers file again
//! (`systemctl reload ultranet`; `--service` names another unit).
//!
//! The peers file holds one block per client:
//! ```text
//! # peer: alice
//! [Peer]
//! PublicKey = ...
//! AllowedIPs = 10.77.0.2/32, fd77::2/128
//! ```
//!
//! This tool is not verified. The blocklist it writes is checked by the
//! verified `Blocklist::new`, here and when the server loads it.

use diomede::blocklist::Blocklist;
use diomede_lists::{domain, parse_list, storage};
use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, Ipv6Addr};
use std::process::{exit, Command, Stdio};
use wg_runtime::config::{key, to_base64};
use wireguard::crypto::Crypto;
use wireguard_libcrux::Libcrux;

/// Domains every blocklist gets: Firefox turns off DNS over HTTPS when this
/// name does not resolve, so its lookups come to the server's resolver.
const BUILT_IN: &[&str] = &["use-application-dns.net"];

fn fail(msg: impl std::fmt::Display) -> ! {
    eprintln!("ultranet-admin: {msg}");
    exit(1)
}

/// The command's options: each `--name value` (or `--flag`), the values of
/// options given several times kept in order.
struct Options(HashMap<String, Vec<String>>);

impl Options {
    fn parse(args: &[String], flags: &[&str]) -> Options {
        let mut m: HashMap<String, Vec<String>> = HashMap::new();
        let mut it = args.iter();
        while let Some(a) = it.next() {
            let Some(name) = a.strip_prefix("--") else { fail(format!("unexpected `{a}`")) };
            let value = if flags.contains(&name) {
                String::new()
            } else {
                it.next().cloned().unwrap_or_else(|| fail(format!("--{name} needs a value")))
            };
            m.entry(name.to_string()).or_default().push(value);
        }
        Options(m)
    }

    fn get(&self, name: &str) -> Option<&str> {
        self.0.get(name).and_then(|v| v.last()).map(String::as_str)
    }

    fn need(&self, name: &str) -> &str {
        self.get(name).unwrap_or_else(|| fail(format!("--{name} is needed")))
    }

    fn all(&self, name: &str) -> &[String] {
        self.0.get(name).map(Vec::as_slice).unwrap_or(&[])
    }

    fn has(&self, name: &str) -> bool {
        self.0.contains_key(name)
    }
}

/// 32 random bytes from the kernel.
fn random_key() -> [u8; 32] {
    let mut k = [0u8; 32];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut k))
        .unwrap_or_else(|e| fail(format!("/dev/urandom: {e}")));
    k
}

fn b64(bytes: &[u8]) -> String {
    let mut out = [0u8; 64];
    to_base64(bytes, &mut out).to_string()
}

fn public_of(private: &[u8; 32]) -> [u8; 32] {
    let mut p = [0u8; 32];
    Libcrux.x25519_public(private, &mut p);
    p
}

fn genkey(o: &Options) {
    use std::os::unix::fs::OpenOptionsExt;
    let path = o.need("out");
    let k = random_key();
    let mut f = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .unwrap_or_else(|e| fail(format!("{path}: {e}")));
    writeln!(f, "{}", b64(&k)).unwrap_or_else(|e| fail(format!("{path}: {e}")));
    println!("{}", b64(&public_of(&k)));
}

/// The blocklist file of `domains` (and the built-in ones).
fn compile(mut domains: Vec<Vec<u8>>) -> Vec<u8> {
    domains.extend(BUILT_IN.iter().filter_map(|d| domain(d)));
    let (data, ends) = storage(domains);
    if Blocklist::new(&data, &ends).is_none() {
        fail("the blocklist did not check out");
    }
    let mut out = vec![0u8; ultranet::blob::len(ends.len(), data.len())];
    ultranet::blob::encode(&data, &ends, &mut out);
    out
}

fn compile_list(o: &Options) {
    let mut domains = Vec::new();
    for path in o.all("list") {
        let text = std::fs::read_to_string(path).unwrap_or_else(|e| fail(format!("{path}: {e}")));
        domains.extend(parse_list(&text));
    }
    let out = o.need("out");
    let blob = compile(domains);
    let (n, _) = ultranet::blob::header(&blob).unwrap_or_else(|| fail("bad blocklist file"));
    let tmp = format!("{out}.tmp");
    std::fs::write(&tmp, &blob)
        .and_then(|_| std::fs::rename(&tmp, out))
        .unwrap_or_else(|e| fail(format!("{out}: {e}")));
    println!("{n} blocked domains");
}

/// A client in the peers file.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Peer {
    name: String,
    /// Its lines, from `# peer: NAME` on.
    text: String,
    public: Option<String>,
    allowed: Vec<String>,
}

/// The peers file: what comes before the first client, and the clients.
fn read_peers(text: &str) -> (String, Vec<Peer>) {
    let mut head = String::new();
    let mut peers: Vec<Peer> = Vec::new();
    for line in text.lines() {
        if let Some(name) = line.trim().strip_prefix("# peer:") {
            peers.push(Peer {
                name: name.trim().to_string(),
                text: String::new(),
                public: None,
                allowed: Vec::new(),
            });
        }
        let Some(p) = peers.last_mut() else {
            head.push_str(line);
            head.push('\n');
            continue;
        };
        p.text.push_str(line);
        p.text.push('\n');
        if let Some((k, v)) = line.split('#').next().unwrap_or("").split_once('=') {
            match k.trim() {
                "PublicKey" => p.public = Some(v.trim().to_string()),
                "AllowedIPs" => p.allowed.extend(v.split(',').map(|s| s.trim().to_string())),
                _ => {}
            }
        }
    }
    (head, peers)
}

fn write_peers(path: &str, head: &str, peers: &[Peer]) {
    let mut text = head.to_string();
    for p in peers {
        text.push_str(&p.text);
    }
    let tmp = format!("{path}.tmp");
    std::fs::write(&tmp, text)
        .and_then(|_| std::fs::rename(&tmp, path))
        .unwrap_or_else(|e| fail(format!("{path}: {e}")));
}

/// `addr/len`, parsed.
fn subnet<T: std::str::FromStr>(s: &str) -> (T, u32) {
    let (a, l) = s.split_once('/').unwrap_or_else(|| fail(format!("{s}: not a prefix")));
    let a = a.parse().unwrap_or_else(|_| fail(format!("{s}: bad address")));
    let l = l.parse().unwrap_or_else(|_| fail(format!("{s}: bad length")));
    (a, l)
}

/// The lowest host number of the subnets, from 2 (1 is the server), not
/// used by `peers`; `None` if they are full.
fn free_host(peers: &[Peer], base4: Ipv4Addr, len4: u32) -> Option<u32> {
    let used: Vec<u32> = peers
        .iter()
        .flat_map(|p| &p.allowed)
        .filter_map(|a| a.strip_suffix("/32"))
        .filter_map(|a| a.parse::<Ipv4Addr>().ok())
        .map(|a| u32::from(a).wrapping_sub(u32::from(base4)))
        .collect();
    let size = 1u64 << (32 - len4.min(32));
    (2..size.saturating_sub(1)).map(|h| h as u32).find(|h| !used.contains(h))
}

/// The client's WireGuard configuration.
fn client_config(
    private: &[u8; 32],
    addr4: Ipv4Addr,
    addr6: Ipv6Addr,
    dns4: Ipv4Addr,
    dns6: Ipv6Addr,
    server: &[u8; 32],
    endpoint: &str,
) -> String {
    format!(
        "[Interface]\nPrivateKey = {}\nAddress = {addr4}/32, {addr6}/128\nDNS = {dns4}, {dns6}\n\n\
         [Peer]\nPublicKey = {}\nEndpoint = {endpoint}\nAllowedIPs = 0.0.0.0/0, ::/0\n\
         PersistentKeepalive = 25\n",
        b64(private),
        b64(server)
    )
}

fn reload(o: &Options) {
    if !o.has("reload") {
        return;
    }
    let unit = o.get("service").unwrap_or("ultranet");
    match Command::new("systemctl").args(["reload", unit]).status() {
        Ok(s) if s.success() => {}
        Ok(s) => fail(format!("systemctl reload {unit}: {s}")),
        Err(e) => fail(format!("systemctl: {e}")),
    }
}

fn add_peer(o: &Options) {
    let path = o.need("peers");
    let name = o.need("name");
    if name.is_empty() || name.contains(char::is_whitespace) {
        fail("a name is one word");
    }
    let text = std::fs::read_to_string(path).unwrap_or_default();
    let (head, mut peers) = read_peers(&text);
    if peers.iter().any(|p| p.name == name) {
        fail(format!("there is a peer named {name} already"));
    }
    let server_text = std::fs::read_to_string(o.need("server-key"))
        .unwrap_or_else(|e| fail(format!("{}: {e}", o.need("server-key"))));
    let server = public_of(&key(&server_text).unwrap_or_else(|e| fail(e)));
    let (base4, len4) = subnet::<Ipv4Addr>(o.get("subnet4").unwrap_or("10.77.0.0/16"));
    let (base6, _) = subnet::<Ipv6Addr>(o.get("subnet6").unwrap_or("fd77::/64"));
    let host = free_host(&peers, base4, len4).unwrap_or_else(|| fail("the subnet is full"));
    let addr4 = Ipv4Addr::from(u32::from(base4) + host);
    let addr6 = Ipv6Addr::from(u128::from(base6) + host as u128);
    let dns4 = Ipv4Addr::from(u32::from(base4) + 1);
    let dns6 = Ipv6Addr::from(u128::from(base6) + 1);
    let private = random_key();
    let public = b64(&public_of(&private));
    peers.push(Peer {
        name: name.to_string(),
        text: format!(
            "# peer: {name}\n[Peer]\nPublicKey = {public}\nAllowedIPs = {addr4}/32, {addr6}/128\n"
        ),
        public: Some(public),
        allowed: vec![format!("{addr4}/32"), format!("{addr6}/128")],
    });
    write_peers(path, &head, &peers);
    reload(o);
    let conf = client_config(&private, addr4, addr6, dns4, dns6, &server, o.need("endpoint"));
    if o.has("qr") {
        let mut child = Command::new("qrencode")
            .args(["-t", "ansiutf8"])
            .stdin(Stdio::piped())
            .spawn()
            .unwrap_or_else(|e| fail(format!("qrencode: {e}")));
        let _ = child.stdin.take().map(|mut s| s.write_all(conf.as_bytes()));
        let _ = child.wait();
    } else {
        print!("{conf}");
    }
}

fn remove_peer(o: &Options) {
    let path = o.need("peers");
    let name = o.need("name");
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| fail(format!("{path}: {e}")));
    let (head, mut peers) = read_peers(&text);
    let before = peers.len();
    peers.retain(|p| p.name != name);
    if peers.len() == before {
        fail(format!("there is no peer named {name}"));
    }
    write_peers(path, &head, &peers);
    reload(o);
}

fn list_peers(o: &Options) {
    let path = o.need("peers");
    let text = std::fs::read_to_string(path).unwrap_or_default();
    for p in read_peers(&text).1 {
        println!(
            "{:<20} {:<45} {}",
            p.name,
            p.public.as_deref().unwrap_or("?"),
            p.allowed.join(", ")
        );
    }
}

fn stats(o: &Options) {
    let path = o.need("stats");
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| fail(format!("{path}: {e}")));
    print!("{text}");
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some((cmd, rest)) = args.split_first() else {
        eprintln!("usage: ultranet-admin genkey|compile-list|add-peer|remove-peer|list-peers|stats ...");
        exit(2)
    };
    let o = Options::parse(rest, &["qr", "reload"]);
    match cmd.as_str() {
        "genkey" => genkey(&o),
        "compile-list" => compile_list(&o),
        "add-peer" => add_peer(&o),
        "remove-peer" => remove_peer(&o),
        "list-peers" => list_peers(&o),
        "stats" => stats(&o),
        _ => fail(format!("unknown command `{cmd}`")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wg_runtime::config::Config;

    #[test]
    fn compiles_lists_with_the_built_ins() {
        let blob = compile(parse_list("0.0.0.0 ads.example\ntracker.io\n"));
        let mut ends = [0u32; 8];
        let (data, ends) = ultranet::blob::split(&blob, &mut ends).unwrap();
        let list = Blocklist::new(data, ends).unwrap();
        assert_eq!(list.len(), 3);
        assert!(list.blocked(b"use-application-dns.net"));
        assert!(list.blocked(b"x.ads.example"));
    }

    #[test]
    fn manages_peers() {
        let text = "# clients\n\
                    # peer: alice\n[Peer]\nPublicKey = AAAA\nAllowedIPs = 10.77.0.2/32, fd77::2/128\n\
                    # peer: carol\n[Peer]\nPublicKey = CCCC\nAllowedIPs = 10.77.0.4/32, fd77::4/128\n";
        let (head, peers) = read_peers(text);
        assert_eq!(head, "# clients\n");
        assert_eq!(peers.len(), 2);
        assert_eq!(peers[1].public.as_deref(), Some("CCCC"));
        let base: Ipv4Addr = "10.77.0.0".parse().unwrap();
        assert_eq!(free_host(&peers, base, 16), Some(3));
        assert_eq!(free_host(&peers, base, 30), None);
    }

    #[test]
    fn writes_client_configs_and_peers_the_server_reads() {
        let k = [5u8; 32];
        let conf = client_config(
            &k,
            "10.77.0.2".parse().unwrap(),
            "fd77::2".parse().unwrap(),
            "10.77.0.1".parse().unwrap(),
            "fd77::1".parse().unwrap(),
            &public_of(&[6; 32]),
            "vpn.example:51820",
        );
        assert!(conf.contains("DNS = 10.77.0.1, fd77::1"));
        assert!(conf.contains("AllowedIPs = 0.0.0.0/0, ::/0"));
        let block = format!(
            "# peer: bob\n[Peer]\nPublicKey = {}\nAllowedIPs = 10.77.0.2/32, fd77::2/128\n",
            b64(&public_of(&k))
        );
        let c = Config::parse_peers(&block).unwrap();
        assert_eq!(c.peer_count, 1);
        assert_eq!(c.peers[0].public, public_of(&k));
    }
}
