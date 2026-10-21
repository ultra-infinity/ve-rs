//! `ultranet [options] <interface> <config> <blocklist>`: the ultranet VPN
//! server, without the Rust standard library.
//!
//! ```text
//! --stats PATH           write statistics to PATH every minute
//! --allow-quic           let QUIC through (its server names are not seen)
//! --allow-dot            let DNS over TLS and QUIC through
//! --keep-https-records   answer HTTPS and SVCB queries (they carry ECH keys)
//! ```
//!
//! `<config>` is a WireGuard configuration (see `wg_runtime::config`), whose
//! `PeersFile` holds the clients; `<blocklist>` is a file written by
//! `ultranet-admin compile-list`. SIGHUP reloads both: a blocklist that does
//! not load (or is not sorted, as the verified `Blocklist::new` checks) is
//! reported and the previous one kept.
//!
//! The interface's addresses, forwarding and NAT are set outside (the NixOS
//! module does it). Every packet a client sends goes through the verified
//! `diomede` filter before it reaches the interface.

#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]
#![cfg_attr(test, allow(dead_code))]

use core::fmt::{self, Write};
use core::ptr::addr_of_mut;
use diomede::blocklist::Blocklist;
use diomede::filter::{Policy, STRICT};
use diomede::stream::{self, Streams};
use ultranet::{blob, Filter};
use wg_runtime::config::Config;
use wg_runtime::sys::{self, Stderr};
use wg_runtime::{Hook, Inner};

/// The largest blocklist file.
const MAX_BLOB: usize = 64 << 20;
/// The most entries of a blocklist.
const MAX_ENTRIES: usize = 4 << 20;
/// How often statistics are written, in nanoseconds.
const REPORT_EVERY: u64 = 60_000_000_000;

/// A blocklist file and its ends, loaded.
struct ListSet {
    bytes: [u8; MAX_BLOB],
    ends: [u32; MAX_ENTRIES],
}

/// Two sets: the one in use, and one to load a new list into.
static mut LISTS: [ListSet; 2] = [const {
    ListSet {
        bytes: [0; MAX_BLOB],
        ends: [0; MAX_ENTRIES],
    }
}; 2];
/// The table of TLS connections being checked.
static mut STREAMS: Streams = stream::EMPTY;

/// Loads the blocklist file at `path` into set `i`.
///
/// # Safety
///
/// Nothing may borrow set `i`: the list loaded before into it must be out
/// of use. (The server is single-threaded; it keeps the list it uses in the
/// other set.)
unsafe fn load(i: usize, path: &[u8]) -> Result<Blocklist<'static>, &'static str> {
    // SAFETY: the caller guarantees set `i` is not borrowed.
    let set: &'static mut ListSet = unsafe { &mut *addr_of_mut!(LISTS[i]) };
    let n = sys::read_file(path, &mut set.bytes).map_err(|e| e.what)?;
    let (data, ends) = blob::split(&set.bytes[..n], &mut set.ends).ok_or("not a blocklist file")?;
    Blocklist::new(data, ends).ok_or("the blocklist is not sorted")
}

/// A path from the command line.
#[derive(Clone, Copy)]
struct Path {
    bytes: [u8; 256],
    len: usize,
}

impl Path {
    fn new(p: &[u8]) -> Option<Path> {
        let mut bytes = [0u8; 256];
        bytes.get_mut(..p.len())?.copy_from_slice(p);
        Some(Path { bytes, len: p.len() })
    }

    fn get(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

/// Text built in a fixed buffer.
struct Text {
    b: [u8; 512],
    n: usize,
}

impl fmt::Write for Text {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let s = s.as_bytes();
        let end = self.n + s.len();
        self.b.get_mut(self.n..end).ok_or(fmt::Error)?.copy_from_slice(s);
        self.n = end;
        Ok(())
    }
}

/// The server's hook: the filter, and the blocklist and statistics files.
struct Server {
    filter: Filter<'static>,
    /// The set the list in use is in.
    active: usize,
    list_path: Path,
    stats_path: Option<Path>,
    last_report: u64,
}

impl Server {
    fn report(&self) {
        let s = self.filter.stats;
        let mut t = Text { b: [0; 512], n: 0 };
        let _ = write!(
            t,
            "passed={}\nnxdomain={}\nnodata={}\nreset={}\ndropped={}\nentries={}\n",
            s.passed,
            s.nxdomain,
            s.nodata,
            s.reset,
            s.dropped,
            self.filter.list.len()
        );
        if let Some(p) = self.stats_path {
            if let Err(e) = sys::write_file(p.get(), &t.b[..t.n]) {
                let _ = writeln!(Stderr, "ultranet: writing statistics: {e}");
            }
        }
        let _ = writeln!(
            Stderr,
            "ultranet: {} passed, {} NXDOMAIN, {} without HTTPS records, {} reset, {} dropped",
            s.passed, s.nxdomain, s.nodata, s.reset, s.dropped
        );
    }
}

impl Inner for Server {
    fn delivered(&mut self, packet: &[u8], now: u64, reply: &mut [u8]) -> Hook {
        self.filter.decide(packet, now, reply)
    }

    fn reload(&mut self) {
        let spare = 1 - self.active;
        // SAFETY: the list in use is in the other set.
        match unsafe { load(spare, self.list_path.get()) } {
            Ok(list) => {
                self.filter.list = list;
                self.active = spare;
                let _ = writeln!(Stderr, "ultranet: blocklist reloaded, {} domains", list.len());
            }
            Err(e) => {
                let _ = writeln!(Stderr, "ultranet: blocklist not reloaded, keeping the old one: {e}");
            }
        }
    }

    fn tick(&mut self, now: u64) {
        if now.saturating_sub(self.last_report) >= REPORT_EVERY {
            self.last_report = now;
            self.report();
        }
    }
}

/// Reads and parses the configuration at `path`.
fn load_config(path: &[u8]) -> Result<Config, ()> {
    let mut text = [0u8; 16384];
    let n = match sys::read_file(path, &mut text) {
        Ok(n) => n,
        Err(e) => {
            let _ = writeln!(Stderr, "ultranet: reading the configuration: {e}");
            return Err(());
        }
    };
    let Ok(text) = core::str::from_utf8(&text[..n]) else {
        let _ = writeln!(Stderr, "ultranet: the configuration is not text");
        return Err(());
    };
    Config::parse(text).map_err(|e| {
        let _ = writeln!(Stderr, "ultranet: configuration line {}: {}", e.line, e.message);
    })
}

fn usage() -> i32 {
    let _ = writeln!(
        Stderr,
        "usage: ultranet [--stats PATH] [--allow-quic] [--allow-dot] [--keep-https-records] \
         <interface> <config> <blocklist>"
    );
    2
}

/// The program, given its arguments.
fn main_with(args: &[&[u8]]) -> i32 {
    let mut policy: Policy = STRICT;
    let mut stats_path = None;
    let mut rest: [&[u8]; 3] = [b""; 3];
    let mut n = 0;
    let mut i = 1;
    while i < args.len() {
        match args[i] {
            b"--stats" if i + 1 < args.len() => {
                i += 1;
                let Some(p) = Path::new(args[i]) else { return usage() };
                stats_path = Some(p);
            }
            b"--allow-quic" => policy.block_quic = false,
            b"--allow-dot" => policy.block_dot = false,
            b"--keep-https-records" => policy.strip_https_rr = false,
            a if !a.starts_with(b"-") && n < rest.len() => {
                rest[n] = a;
                n += 1;
            }
            _ => return usage(),
        }
        i += 1;
    }
    if n != 3 {
        return usage();
    }
    let [interface, config_path, list_path] = rest;
    let Ok(config) = load_config(config_path) else { return 1 };
    let Some(list_path) = Path::new(list_path) else { return usage() };
    // SAFETY: nothing uses the sets yet.
    let list = match unsafe { load(0, list_path.get()) } {
        Ok(l) => l,
        Err(e) => {
            let _ = writeln!(Stderr, "ultranet: loading the blocklist: {e}");
            return 1;
        }
    };
    let _ = writeln!(Stderr, "ultranet: {} blocked domains", list.len());
    let mut server = Server {
        filter: Filter {
            list,
            // SAFETY: the only reference to the table, for the life of the
            // program.
            streams: unsafe { &mut *addr_of_mut!(STREAMS) },
            policy,
            stats: Default::default(),
        },
        active: 0,
        list_path,
        stats_path,
        last_report: sys::monotonic(),
    };
    match wg_runtime::run(interface, &config, &mut server) {
        Ok(()) => 0,
        Err(e) => {
            let _ = writeln!(Stderr, "ultranet: {e}");
            1
        }
    }
}

/// The C entry point.
///
/// # Safety
///
/// `argv` must hold `argc` NUL-terminated strings, as the C runtime passes.
#[cfg(not(test))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn main(argc: i32, argv: *const *const core::ffi::c_char) -> i32 {
    let mut args: [&[u8]; 12] = [b""; 12];
    let n = (argc.max(0) as usize).min(args.len());
    for (i, arg) in args.iter_mut().enumerate().take(n) {
        // SAFETY: `argv` holds `argc` NUL-terminated strings.
        *arg = unsafe { core::ffi::CStr::from_ptr(*argv.add(i)) }.to_bytes();
    }
    if argc as usize > args.len() {
        return usage();
    }
    main_with(&args[..n])
}

#[cfg(not(test))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    let _ = writeln!(Stderr, "ultranet: {info}");
    // SAFETY: ends the process.
    unsafe { libc::abort() }
}

/// The unwinding personality the precompiled `core` refers to. Panics abort
/// (see the workspace profiles), so nothing ever calls it.
#[cfg(not(test))]
#[unsafe(no_mangle)]
extern "C" fn rust_eh_personality() {}
