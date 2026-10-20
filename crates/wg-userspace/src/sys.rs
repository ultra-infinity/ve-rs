//! The operating system, through `libc`: standard error, clocks, randomness,
//! files, the TUN device and the raw sockets.

use core::fmt;
use core::mem::{size_of, zeroed};

/// The last error number.
pub fn errno() -> i32 {
    // SAFETY: `__errno_location` returns this thread's `errno`.
    unsafe { *libc::__errno_location() }
}

/// An OS error: what failed, and the error number.
#[derive(Debug, Clone, Copy)]
pub struct OsError {
    pub what: &'static str,
    pub errno: i32,
}

impl fmt::Display for OsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: error {}", self.what, self.errno)
    }
}

/// Fails with the current `errno` if `r` is negative.
fn check(r: isize, what: &'static str) -> Result<usize, OsError> {
    if r < 0 {
        Err(OsError {
            what,
            errno: errno(),
        })
    } else {
        Ok(r as usize)
    }
}

/// Standard error, unbuffered.
pub struct Stderr;

impl fmt::Write for Stderr {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let mut b = s.as_bytes();
        while !b.is_empty() {
            // SAFETY: writes at most `b.len()` bytes from `b`.
            let n = unsafe { libc::write(2, b.as_ptr().cast(), b.len()) };
            if n <= 0 {
                return Err(fmt::Error);
            }
            b = &b[n as usize..];
        }
        Ok(())
    }
}

/// Writes all of `b` to standard output.
pub fn write_stdout(b: &[u8]) {
    // SAFETY: writes at most `b.len()` bytes from `b`.
    unsafe { libc::write(1, b.as_ptr().cast(), b.len()) };
}

/// The time on `clock`, in nanoseconds.
fn clock_ns(clock: libc::clockid_t) -> u64 {
    // SAFETY: `ts` is a valid `timespec` to write into.
    let mut ts: libc::timespec = unsafe { zeroed() };
    unsafe { libc::clock_gettime(clock, &mut ts) };
    ts.tv_sec as u64 * 1_000_000_000 + ts.tv_nsec as u64
}

/// The monotonic clock, in nanoseconds.
pub fn monotonic() -> u64 {
    clock_ns(libc::CLOCK_MONOTONIC)
}

/// The wall-clock time as TAI64N, as WireGuard sends it in initiations: the
/// TAI64 label of the seconds, then the nanoseconds, big-endian.
pub fn tai64n() -> [u8; 12] {
    let t = clock_ns(libc::CLOCK_REALTIME);
    let mut out = [0u8; 12];
    out[..8].copy_from_slice(&(0x4000_0000_0000_000a + t / 1_000_000_000).to_be_bytes());
    out[8..].copy_from_slice(&((t % 1_000_000_000) as u32).to_be_bytes());
    out
}

/// Fills `buf` with random bytes from the kernel.
pub fn random(buf: &mut [u8]) -> Result<(), OsError> {
    let mut filled = 0;
    while filled < buf.len() {
        // SAFETY: writes at most `buf.len() - filled` bytes into `buf`.
        let n =
            unsafe { libc::getrandom(buf[filled..].as_mut_ptr().cast(), buf.len() - filled, 0) };
        if n < 0 && errno() == libc::EINTR {
            continue;
        }
        filled += check(n, "getrandom")?;
    }
    Ok(())
}

/// A file descriptor, closed when dropped.
pub struct Fd(pub i32);

impl Drop for Fd {
    fn drop(&mut self) {
        // SAFETY: closes a descriptor this value owns.
        unsafe { libc::close(self.0) };
    }
}

impl Fd {
    /// Reads into `buf`.
    pub fn read(&self, buf: &mut [u8]) -> Result<usize, OsError> {
        // SAFETY: reads at most `buf.len()` bytes into `buf`.
        check(
            unsafe { libc::read(self.0, buf.as_mut_ptr().cast(), buf.len()) },
            "read",
        )
    }

    /// Writes `buf`.
    pub fn write(&self, buf: &[u8]) -> Result<usize, OsError> {
        // SAFETY: writes at most `buf.len()` bytes from `buf`.
        check(
            unsafe { libc::write(self.0, buf.as_ptr().cast(), buf.len()) },
            "write",
        )
    }
}

/// A path as a NUL-terminated C string, in `buf`.
fn c_path<'a>(path: &[u8], buf: &'a mut [u8; 256]) -> Result<&'a [u8], OsError> {
    if path.len() >= buf.len() || path.contains(&0) {
        return Err(OsError {
            what: "path too long",
            errno: libc::ENAMETOOLONG,
        });
    }
    buf[..path.len()].copy_from_slice(path);
    buf[path.len()] = 0;
    Ok(&buf[..=path.len()])
}

/// Reads the file at `path` into `buf`; returns its length.
pub fn read_file(path: &[u8], buf: &mut [u8]) -> Result<usize, OsError> {
    let mut p = [0u8; 256];
    let p = c_path(path, &mut p)?;
    // SAFETY: `p` is NUL-terminated.
    let fd = Fd(check(
        unsafe { libc::open(p.as_ptr().cast(), libc::O_RDONLY) } as isize,
        "open",
    )? as i32);
    let mut n = 0;
    loop {
        let m = fd.read(&mut buf[n..])?;
        if m == 0 {
            return Ok(n);
        }
        n += m;
        if n == buf.len() {
            return Err(OsError {
                what: "file too large",
                errno: libc::EFBIG,
            });
        }
    }
}

/// Reads standard input into `buf`; returns its length.
pub fn read_stdin(buf: &mut [u8]) -> Result<usize, OsError> {
    let fd = Fd(0);
    let mut n = 0;
    loop {
        let m = fd.read(&mut buf[n..]);
        match m {
            Ok(0) => break,
            Ok(m) => n += m,
            Err(e) => {
                core::mem::forget(fd);
                return Err(e);
            }
        }
        if n == buf.len() {
            break;
        }
    }
    core::mem::forget(fd);
    Ok(n)
}

const IFF_TUN: libc::c_short = 0x0001;
const IFF_NO_PI: libc::c_short = 0x1000;
const TUNSETIFF: libc::c_ulong = 0x4004_54ca;

#[repr(C)]
struct IfReq {
    name: [u8; libc::IFNAMSIZ],
    flags: libc::c_short,
    _pad: [u8; 22],
}

/// Opens the TUN interface `name` (creating it if needed), without packet
/// information headers: each read or write is one IP packet. Returns it and
/// its interface index.
pub fn open_tun(name: &[u8]) -> Result<(Fd, i32), OsError> {
    if name.len() >= libc::IFNAMSIZ || name.contains(&0) {
        return Err(OsError {
            what: "interface name too long",
            errno: libc::EINVAL,
        });
    }
    // SAFETY: the path is NUL-terminated.
    let fd = Fd(check(
        unsafe { libc::open(c"/dev/net/tun".as_ptr(), libc::O_RDWR) } as isize,
        "open /dev/net/tun",
    )? as i32);
    let mut req = IfReq {
        name: [0; libc::IFNAMSIZ],
        flags: IFF_TUN | IFF_NO_PI,
        _pad: [0; 22],
    };
    req.name[..name.len()].copy_from_slice(name);
    // SAFETY: TUNSETIFF reads and writes a `struct ifreq`, which `IfReq`
    // lays out, on a descriptor we own.
    check(
        unsafe { libc::ioctl(fd.0, TUNSETIFF as _, &mut req) } as isize,
        "TUNSETIFF",
    )?;
    // SAFETY: `req.name` is NUL-terminated.
    let index = unsafe { libc::if_nametoindex(req.name.as_ptr().cast()) } as i32;
    Ok((fd, index))
}

/// Opens a socket.
fn socket(domain: i32, kind: i32, protocol: i32, what: &'static str) -> Result<Fd, OsError> {
    // SAFETY: plain system call.
    Ok(Fd(check(
        unsafe { libc::socket(domain, kind, protocol) } as isize,
        what,
    )? as i32))
}

/// A socket that receives every IP packet the host sees, without link-layer
/// header (`AF_PACKET`, `SOCK_DGRAM`).
pub fn packet_socket() -> Result<Fd, OsError> {
    socket(
        libc::AF_PACKET,
        libc::SOCK_DGRAM | libc::SOCK_NONBLOCK,
        (libc::ETH_P_ALL as u16).to_be() as i32,
        "packet socket",
    )
}

/// A received IP packet: its length, its EtherType, and the index of the
/// interface it came on; `None` if there was none waiting.
pub struct Received {
    pub len: usize,
    pub ether_type: u16,
    pub ifindex: i32,
    pub outgoing: bool,
}

/// Receives one IP packet from a packet socket into `buf`.
pub fn recv_packet(fd: &Fd, buf: &mut [u8]) -> Result<Option<Received>, OsError> {
    // SAFETY: `addr` is a valid `sockaddr_ll` to write into, of the given size.
    let mut addr: libc::sockaddr_ll = unsafe { zeroed() };
    let mut alen = size_of::<libc::sockaddr_ll>() as libc::socklen_t;
    let n = unsafe {
        libc::recvfrom(
            fd.0,
            buf.as_mut_ptr().cast(),
            buf.len(),
            libc::MSG_TRUNC,
            (&mut addr as *mut libc::sockaddr_ll).cast(),
            &mut alen,
        )
    };
    if n < 0 && (errno() == libc::EAGAIN || errno() == libc::EINTR) {
        return Ok(None);
    }
    let n = check(n, "recvfrom")?;
    Ok(Some(Received {
        // A truncated packet reports its full length; keep it so that it is
        // rejected as incomplete.
        len: n.min(buf.len()),
        ether_type: u16::from_be(addr.sll_protocol),
        ifindex: addr.sll_ifindex,
        outgoing: addr.sll_pkttype == libc::PACKET_OUTGOING,
    }))
}

/// Raw sockets to send whole IPv4 and IPv6 packets, headers included.
pub struct RawSockets {
    pub v4: Fd,
    pub v6: Option<Fd>,
}

impl RawSockets {
    pub fn open() -> Result<RawSockets, OsError> {
        Ok(RawSockets {
            v4: socket(
                libc::AF_INET,
                libc::SOCK_RAW,
                libc::IPPROTO_RAW,
                "raw IPv4 socket",
            )?,
            // IPv6 may be disabled; then only IPv4 endpoints can be reached.
            v6: socket(
                libc::AF_INET6,
                libc::SOCK_RAW,
                libc::IPPROTO_RAW,
                "raw IPv6 socket",
            )
            .ok(),
        })
    }

    /// Sends the IPv4 packet `packet` to `dst`.
    pub fn send_v4(&self, dst: [u8; 4], packet: &[u8]) -> Result<(), OsError> {
        // SAFETY: a zeroed `sockaddr_in` is valid; it is passed with its size.
        let mut sa: libc::sockaddr_in = unsafe { zeroed() };
        sa.sin_family = libc::AF_INET as libc::sa_family_t;
        sa.sin_addr.s_addr = u32::from_ne_bytes(dst);
        let r = unsafe {
            libc::sendto(
                self.v4.0,
                packet.as_ptr().cast(),
                packet.len(),
                0,
                (&sa as *const libc::sockaddr_in).cast(),
                size_of::<libc::sockaddr_in>() as libc::socklen_t,
            )
        };
        check(r, "sendto").map(|_| ())
    }

    /// Sends the IPv6 packet `packet` to `dst`.
    pub fn send_v6(&self, dst: [u8; 16], packet: &[u8]) -> Result<(), OsError> {
        let fd = self.v6.as_ref().ok_or(OsError {
            what: "no IPv6",
            errno: libc::EAFNOSUPPORT,
        })?;
        // SAFETY: a zeroed `sockaddr_in6` is valid; it is passed with its size.
        let mut sa: libc::sockaddr_in6 = unsafe { zeroed() };
        sa.sin6_family = libc::AF_INET6 as libc::sa_family_t;
        sa.sin6_addr.s6_addr = dst;
        let r = unsafe {
            libc::sendto(
                fd.0,
                packet.as_ptr().cast(),
                packet.len(),
                0,
                (&sa as *const libc::sockaddr_in6).cast(),
                size_of::<libc::sockaddr_in6>() as libc::socklen_t,
            )
        };
        check(r, "sendto").map(|_| ())
    }
}

/// The source address the kernel would use to reach `dst` (a routing
/// lookup: a UDP socket connected to it, never used to send).
pub fn source_v4(dst: [u8; 4]) -> Result<[u8; 4], OsError> {
    let s = socket(libc::AF_INET, libc::SOCK_DGRAM, 0, "UDP socket")?;
    // SAFETY: zeroed `sockaddr_in`s are valid; each is passed with its size.
    let mut sa: libc::sockaddr_in = unsafe { zeroed() };
    sa.sin_family = libc::AF_INET as libc::sa_family_t;
    sa.sin_port = 9u16.to_be();
    sa.sin_addr.s_addr = u32::from_ne_bytes(dst);
    let len = size_of::<libc::sockaddr_in>() as libc::socklen_t;
    check(
        unsafe { libc::connect(s.0, (&sa as *const libc::sockaddr_in).cast(), len) } as isize,
        "route lookup",
    )?;
    let mut local: libc::sockaddr_in = unsafe { zeroed() };
    let mut llen = len;
    check(
        unsafe {
            libc::getsockname(
                s.0,
                (&mut local as *mut libc::sockaddr_in).cast(),
                &mut llen,
            )
        } as isize,
        "getsockname",
    )?;
    Ok(local.sin_addr.s_addr.to_ne_bytes())
}

/// The source address the kernel would use to reach `dst`.
pub fn source_v6(dst: [u8; 16]) -> Result<[u8; 16], OsError> {
    let s = socket(libc::AF_INET6, libc::SOCK_DGRAM, 0, "UDP socket")?;
    // SAFETY: zeroed `sockaddr_in6`s are valid; each is passed with its size.
    let mut sa: libc::sockaddr_in6 = unsafe { zeroed() };
    sa.sin6_family = libc::AF_INET6 as libc::sa_family_t;
    sa.sin6_port = 9u16.to_be();
    sa.sin6_addr.s6_addr = dst;
    let len = size_of::<libc::sockaddr_in6>() as libc::socklen_t;
    check(
        unsafe { libc::connect(s.0, (&sa as *const libc::sockaddr_in6).cast(), len) } as isize,
        "route lookup",
    )?;
    let mut local: libc::sockaddr_in6 = unsafe { zeroed() };
    let mut llen = len;
    check(
        unsafe {
            libc::getsockname(
                s.0,
                (&mut local as *mut libc::sockaddr_in6).cast(),
                &mut llen,
            )
        } as isize,
        "getsockname",
    )?;
    Ok(local.sin6_addr.s6_addr)
}

/// Holds `port` with a UDP socket that is never read, so that the kernel does
/// not answer the datagrams we receive through the packet socket with ICMP
/// "port unreachable". (Its small queue just fills up and overflows.)
pub fn reserve_port(port: u16) -> Result<Fd, OsError> {
    let s = socket(libc::AF_INET6, libc::SOCK_DGRAM, 0, "UDP socket")?;
    let off: libc::c_int = 0;
    let small: libc::c_int = 1;
    // SAFETY: the options take a `c_int`, passed with its size; a zeroed
    // `sockaddr_in6` (the unspecified address) is valid.
    unsafe {
        libc::setsockopt(
            s.0,
            libc::IPPROTO_IPV6,
            libc::IPV6_V6ONLY,
            (&off as *const libc::c_int).cast(),
            size_of::<libc::c_int>() as libc::socklen_t,
        );
        libc::setsockopt(
            s.0,
            libc::SOL_SOCKET,
            libc::SO_RCVBUF,
            (&small as *const libc::c_int).cast(),
            size_of::<libc::c_int>() as libc::socklen_t,
        );
    }
    let mut sa: libc::sockaddr_in6 = unsafe { zeroed() };
    sa.sin6_family = libc::AF_INET6 as libc::sa_family_t;
    sa.sin6_port = port.to_be();
    check(
        unsafe {
            libc::bind(
                s.0,
                (&sa as *const libc::sockaddr_in6).cast(),
                size_of::<libc::sockaddr_in6>() as libc::socklen_t,
            )
        } as isize,
        "bind the listen port",
    )?;
    Ok(s)
}

/// Waits until `a` or `b` is readable, or `timeout_ms` passes; returns
/// whether each is readable.
pub fn poll2(a: &Fd, b: &Fd, timeout_ms: i32) -> Result<(bool, bool), OsError> {
    let mut fds = [
        libc::pollfd {
            fd: a.0,
            events: libc::POLLIN,
            revents: 0,
        },
        libc::pollfd {
            fd: b.0,
            events: libc::POLLIN,
            revents: 0,
        },
    ];
    // SAFETY: `fds` is a valid array of two `pollfd`s.
    let r = unsafe { libc::poll(fds.as_mut_ptr(), 2, timeout_ms) };
    if r < 0 && errno() == libc::EINTR {
        return Ok((false, false));
    }
    check(r as isize, "poll")?;
    Ok((
        fds[0].revents & libc::POLLIN != 0,
        fds[1].revents & libc::POLLIN != 0,
    ))
}
