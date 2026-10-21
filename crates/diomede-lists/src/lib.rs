//! Blocklists as people publish them: hosts files (`0.0.0.0 ads.example`)
//! or one domain per line, `#` starting a comment, and `localhost` and the
//! like skipped. [`storage`] lays them out for the verified
//! `diomede::blocklist::Blocklist::new`, which checks the result, so this
//! parsing needs no trust.

use std::net::IpAddr;

/// Names that hosts files map to themselves rather than block.
pub const NOT_BLOCKED: &[&str] = &[
    "localhost",
    "localhost.localdomain",
    "local",
    "broadcasthost",
    "ip6-localhost",
    "ip6-loopback",
    "ip6-localnet",
    "ip6-mcastprefix",
    "ip6-allnodes",
    "ip6-allrouters",
    "ip6-allhosts",
];

/// `h` as a listed domain: lowercase, without a trailing dot, made of labels
/// of 1 to 63 letters, digits, `-` and `_`.
pub fn domain(h: &str) -> Option<Vec<u8>> {
    let h = h.trim_end_matches('.').to_ascii_lowercase();
    if h.is_empty() || h.len() > 253 || NOT_BLOCKED.contains(&h.as_str()) {
        return None;
    }
    if h.parse::<IpAddr>().is_ok() {
        return None;
    }
    let ok = h.split('.').all(|l| {
        !l.is_empty()
            && l.len() <= 63
            && l.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'-' || c == b'_')
    });
    ok.then(|| h.into_bytes())
}

/// The domains of a hosts file or domain list.
pub fn parse_list(text: &str) -> Vec<Vec<u8>> {
    let mut domains = Vec::new();
    for line in text.lines() {
        let line = line.split('#').next().unwrap_or("");
        let mut words = line.split_whitespace().peekable();
        // A hosts file line starts with an address.
        if words.peek().is_some_and(|w| w.parse::<IpAddr>().is_ok()) {
            words.next();
        }
        domains.extend(words.filter_map(domain));
    }
    domains
}

/// The storage of a blocklist: the domains sorted, without duplicates.
pub fn storage(mut domains: Vec<Vec<u8>>) -> (Vec<u8>, Vec<u32>) {
    domains.sort();
    domains.dedup();
    let mut data = Vec::new();
    let mut ends = Vec::new();
    for d in domains {
        data.extend_from_slice(&d);
        ends.push(data.len() as u32);
    }
    (data, ends)
}

#[cfg(test)]
mod tests {
    use super::*;
    use diomede::blocklist::Blocklist;

    #[test]
    fn parses_hosts_files_and_domain_lists() {
        let text = "# A list\n\
                    127.0.0.1 localhost\n\
                    0.0.0.0 Ads.Example.  # trailing comment\n\
                    0.0.0.0 tracker.io metrics.tracker.io\n\
                    :: ip6-localhost\n\
                    doubleclick.net\n\
                    bad..name\n\
                    1.2.3.4\n";
        let got: Vec<String> =
            parse_list(text).into_iter().map(|d| String::from_utf8(d).unwrap()).collect();
        assert_eq!(got, ["ads.example", "tracker.io", "metrics.tracker.io", "doubleclick.net"]);
    }

    #[test]
    fn builds_a_valid_list() {
        let domains = parse_list("b.com\na.com\nb.com\nab.com\n");
        let (data, ends) = storage(domains);
        let list = Blocklist::new(&data, &ends).unwrap();
        assert_eq!(list.len(), 3);
        assert!(list.blocked(b"x.ab.com"));
    }
}
