//! A userspace WireGuard interface around the verified sans-IO
//! [`wireguard::device::Device`], without the Rust standard library.
//!
//! ```text
//! wg-userspace <interface> <config file>   run the interface
//! wg-userspace genkey                      print a new private key
//! wg-userspace pubkey < private            print the public key
//! ```
//!
//! The work is done by [`wg_runtime`]: the configuration, the sockets (UDP
//! through the verified `net` crate), the TUN device and the event loop.
//! This program delivers every packet as it is. SIGHUP reloads the peers
//! file, if the configuration names one.

#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]
// Under test, the entry point is compiled out, and much of what it uses.
#![cfg_attr(test, allow(dead_code))]

use core::fmt::Write;
use wg_runtime::config::{self, to_base64, Config};
use wg_runtime::sys::{self, OsError, Stderr};
use wireguard::crypto::Crypto;
use wireguard_libcrux::Libcrux;

/// `genkey`: a new private key.
fn genkey() -> Result<(), OsError> {
    let mut k = [0u8; 32];
    sys::random(&mut k)?;
    let mut text = [0u8; 64];
    sys::write_stdout(to_base64(&k, &mut text).as_bytes());
    sys::write_stdout(b"\n");
    Ok(())
}

/// `pubkey`: the public key of the private key on standard input.
fn pubkey() -> Result<(), &'static str> {
    let mut input = [0u8; 256];
    let n = sys::read_stdin(&mut input).map_err(|e| e.what)?;
    let s = core::str::from_utf8(&input[..n]).map_err(|_| "not text")?;
    let k = config::key(s)?;
    let mut p = [0u8; 32];
    Libcrux.x25519_public(&k, &mut p);
    let mut text = [0u8; 64];
    sys::write_stdout(to_base64(&p, &mut text).as_bytes());
    sys::write_stdout(b"\n");
    Ok(())
}

/// Reads and parses the configuration at `path`.
fn load(path: &[u8]) -> Result<Config, ()> {
    let mut text = [0u8; 16384];
    let n = match sys::read_file(path, &mut text) {
        Ok(n) => n,
        Err(e) => {
            let _ = writeln!(Stderr, "wg-userspace: reading the configuration: {e}");
            return Err(());
        }
    };
    let Ok(text) = core::str::from_utf8(&text[..n]) else {
        let _ = writeln!(Stderr, "wg-userspace: the configuration is not text");
        return Err(());
    };
    Config::parse(text).map_err(|e| {
        let _ = writeln!(
            Stderr,
            "wg-userspace: configuration line {}: {}",
            e.line, e.message
        );
    })
}

/// The program, given its arguments.
fn main_with(args: &[&[u8]]) -> i32 {
    match args {
        [_, b"genkey"] => match genkey() {
            Ok(()) => 0,
            Err(e) => {
                let _ = writeln!(Stderr, "wg-userspace: {e}");
                1
            }
        },
        [_, b"pubkey"] => match pubkey() {
            Ok(()) => 0,
            Err(e) => {
                let _ = writeln!(Stderr, "wg-userspace: {e}");
                1
            }
        },
        [_, interface, path] => {
            let Ok(config) = load(path) else { return 1 };
            match wg_runtime::run(interface, &config, &mut wg_runtime::Plain) {
                Ok(()) => 0,
                Err(e) => {
                    let _ = writeln!(Stderr, "wg-userspace: {e}");
                    1
                }
            }
        }
        _ => {
            let _ = writeln!(
                Stderr,
                "usage: wg-userspace <interface> <config> | genkey | pubkey"
            );
            2
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
    let mut args: [&[u8]; 4] = [b""; 4];
    let n = (argc.max(0) as usize).min(args.len());
    for (i, arg) in args.iter_mut().enumerate().take(n) {
        // SAFETY: `argv` holds `argc` NUL-terminated strings.
        *arg = unsafe { core::ffi::CStr::from_ptr(*argv.add(i)) }.to_bytes();
    }
    if argc as usize > args.len() {
        return main_with(&[]);
    }
    main_with(&args[..n])
}

#[cfg(not(test))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    let _ = writeln!(Stderr, "wg-userspace: {info}");
    // SAFETY: ends the process.
    unsafe { libc::abort() }
}

/// The unwinding personality the precompiled `core` refers to. Panics abort
/// (see the workspace profiles), so nothing ever calls it.
#[cfg(not(test))]
#[unsafe(no_mangle)]
extern "C" fn rust_eh_personality() {}
