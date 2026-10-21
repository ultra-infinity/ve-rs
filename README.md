# ve-rs: verified Rust for untrusted input

`untrusted` is a `no_std`, dependency-free Rust library for turning untrusted
bytes into typed values. Every function in it is **formally verified**: its Rust
code is translated to [Lean 4](https://lean-lang.org) with
[Charon and Aeneas](https://github.com/AeneasVerif/aeneas), and each function
is proved, for *all* inputs, to never panic, to always terminate, and to return
exactly what its specification says.

You can also `#[derive(Decode, Encode)]` on your own structs, and `cargo
untrusted verify` proves those derived decoders and encoders correct, and that
each decodes back what it encodes, without you writing any proofs.

The guarantees are strong, and so are the costs. Read [Cons](#cons) before
adopting this.

```rust
use untrusted::{BigEndian, Decode, LittleEndian, Untrusted, ValidationError};

#[derive(Decode, Debug, PartialEq)]
struct Header {
    version: BigEndian<u8>,
    len: BigEndian<u16>,
}

#[derive(Decode, Debug, PartialEq)]
struct Packet {
    header: Header,
    checksum: LittleEndian<u32>,
}

let bytes: &[u8] = &[1, 0, 2, 0xef, 0xbe, 0xad, 0xde];
let packet = Untrusted::new(bytes).read_all::<Packet>()?;

// Extra bytes are always an error; they can never be silently ignored.
let longer: &[u8] = &[1, 0, 2, 0xef, 0xbe, 0xad, 0xde, 0xff];
assert_eq!(
    Untrusted::new(longer).read_all::<Packet>(),
    Err(ValidationError::TrailingData)
);
```

## What is in the crate

- **`Untrusted<T>`:** wraps raw input. The only way to get at the value is to
  validate or decode it.
- **`Validate<Input>`:** fallible conversion from untrusted input. Implemented for:
  - **Byte strings to integers:** `BigEndian<T>` and `LittleEndian<T>` for
    `u8`–`u128` and `i8`–`i128`. The input must have exactly the right length.
  - **Integer to integer:** checked conversions between every pair of distinct
    integer types, including `usize` and `isize` (132 pairs). They succeed
    exactly when the value fits in the target type.
- **`Decode` and `Reader`:** sequential decoding with `decode`, `read`,
  `read_byte`, `read_bytes`, `skip` and `peek`.
  - The only entry point is `Untrusted::read_all`, which fails with
    `TrailingData` unless every byte was consumed.
  - Every reader method either succeeds and advances, or fails and leaves the
    reader unchanged.
  - Sub-slices are handed back as `Untrusted`, so they too must be validated
    before use.
- **Fixed-size byte arrays:** `[u8; N]` decodes as exactly the next `N` bytes,
  copied, e.g. a key or a MAC. It can be a field of a derived struct.
- **`#[derive(Decode)]`:** decodes a struct's fields one after another, in
  declaration order. Works for named, tuple and unit structs.
- **`Encode` and `Writer`:** the other direction: `write_byte`, `write_bytes` and
  `encode` on a `Writer`, reached through `encode_into(&value, out)`, which
  writes to the start of `out` and returns the length. Encoding is total: it
  only fails, with `EncodeError::NoRoom`, when `out` is too short. Implemented
  for the `BigEndian`/`LittleEndian` integers, `[u8; N]` and `&[u8]`.
- **`#[derive(Encode)]`:** writes a struct's fields in declaration order, the
  way `Decode` reads them. It also accepts lifetime parameters, so a field may
  borrow a payload (`&'a [u8]`).

## Example: a network stack up to UDP and TCP (`crates/net`)

The `net` crate is a verified decoder for network packets, from Ethernet II
frames up to UDP and TCP, built on `untrusted`. Each layer hands its payload back
still `Untrusted`, and the next layer validates it:

```rust
let frame = Untrusted::new(bytes_with_fcs).validate::<net::ethernet::FrameWithFcs>()?.frame;
// frame.header.dst, frame.header.src,
// frame.header.tagging.vlan (an optional 802.1Q tag), frame.header.tagging.ether_type

match frame.header.tagging.ether_type.0 {
    net::ipv4::ETHER_TYPE_IPV4 => {
        let udp = frame.payload.validate::<net::udp::Ipv4Udp>()?;
        // udp.ip.header (addresses, TTL, …), udp.header (ports, …), udp.payload
    }
    net::ipv6::ETHER_TYPE_IPV6 => {
        let udp = frame.payload.validate::<net::udp::Ipv6Udp>()?;
    }
    net::arp::ETHER_TYPE_ARP => {
        let arp = frame.payload.validate::<net::arp::Arp>()?;
    }
    _ => {}
}
```

Every `validate` is proved to accept **exactly** the well-formed inputs
described below, and to return their decoding. Variable-length parts
(payloads, IPv4 options, link-layer padding) are borrowed from the input
without copying. Padding is handed back explicitly rather than dropped.

- **`ethernet::Frame`:**
  - untagged: a 14-byte header and 46 to 1500 bytes of payload;
  - 802.1Q-tagged (bytes 12–13 are `0x8100`): an 18-byte header and 42 to
    1500 bytes of payload. The tag's VLAN ID is never the reserved `0xFFF`,
    and stacked tags (QinQ) are rejected;
  - an EtherType of at least `0x0600` (smaller values are 802.3 lengths).
- **`ethernet::FrameWithFcs`:** additionally, the last 4 bytes (least
  significant first) are the CRC-32 of the rest.
- **`arp::Arp`:** a 28-byte ARP packet for IPv4 over Ethernet (hardware type
  1, protocol type `0x0800`, address lengths 6 and 4), whose operation is a
  request (1) or a reply (2), followed by any padding.
- **`ipv4::Ipv4Packet`:**
  - version 4;
  - a header length `hl = 4 × IHL` and a total length `tl` with
    `20 ≤ hl ≤ tl ≤` the input length;
  - a valid header checksum;
  - the reserved flag bit clear.

  Options (`[20, hl)`) are not interpreted, and bytes after `tl` are padding.
  Fragments are accepted at this layer.
- **`ipv6::Ipv6Packet`:** version 6 and at least `40 +` payload length bytes.
  The next header is handed back as is, and bytes after the payload are
  padding.
- **`udp::Ipv4Udp`:**
  - an IPv4 packet with protocol 17 that is not a fragment;
  - a payload of at least 8 bytes whose UDP length equals the payload length;
  - a checksum that is either 0 (none) or valid over the RFC 768
    pseudo-header and the datagram.
- **`udp::Ipv6Udp`:**
  - an IPv6 packet with next header 17 (so no extension headers);
  - the same length condition as over IPv4;
  - a checksum that is non-zero (IPv6 makes it mandatory) and valid over the
    RFC 8200 pseudo-header and the datagram.
- **`tcp::Ipv4Tcp`, `tcp::Ipv6Tcp`:**
  - an IPv4 packet with protocol 6 that is not a fragment, or an IPv6 packet
    with next header 6;
  - a segment of at least 20 bytes whose data offset is at least 5 and whose
    header length (4 × data offset) fits in the segment;
  - a valid checksum over the pseudo-header and the segment.

  The options and the data are handed back; reassembling streams is left to
  the caller.
- **`icmp::Icmpv4`:** an IPv4 packet with protocol 1 that is not a fragment,
  whose payload is at least 8 bytes long with a valid checksum.
- **`icmp::Icmpv6`:** an IPv6 packet with next header 58, whose payload is at
  least 8 bytes long with a valid checksum over the pseudo-header and the
  payload.

Two checksums are proved equal to their textbook definitions, and each
definition is checked in Lean's kernel against a known value:
- CRC-32: the IEEE 802.3 CRC-32, checked against `"123456789"`, which gives
  `0xCBF43926`;
- the Internet checksum (RFC 1071): the one's-complement sum, checked against a
  worked IPv4 header that sums to `0xFFFF`.

UDP datagrams can also be built: `udp::encode_ipv4` and `udp::encode_ipv6`
write a whole IP packet (header, UDP header, data, checksums) into a buffer.
They are proved to round-trip: `Ipv4Udp` / `Ipv6Udp` accept what they write and
decode it back to the same addresses, ports and data
(`proofs/Net/UdpEncode.lean`). Likewise `tcp::encode_ipv4` and
`tcp::encode_ipv6` write a bare TCP segment (no options or data, such as a
reset), which `Ipv4Tcp` / `Ipv6Tcp` decode back to the same addresses,
ports, numbers and flags (`proofs/Net/TcpEncode.lean`).
The headers are written through their `Encode` impls (derived for the
headers, hand-written for the fields that pack bits, like `VersionIhl`), so
the headers' decoding in these proofs comes from their round trips; what
remains by hand is the checksums and the lengths.

Not covered: reassembling fragments or TCP streams, IPv6 extension headers,
interpreting IPv4 or TCP options, ICMP message types or NDP, and encoding
anything but UDP and bare TCP segments.

It also shows how hand-written and derived proofs combine:
- field decoders that check values have hand-written specs:
  - `proofs/Net/Fields.lean`: `MacAddr`, `EtherType`, `VlanTag`, `Tagging`;
  - `proofs/Net/Ipv4Fields.lean`: `VersionIhl`, `Fragment`, `Ipv4Addr` (their
    encoders and round trips too);
  - `proofs/Net/Ipv6Fields.lean`: `VersionClassFlow`, `Ipv6Addr` (likewise);
  - `proofs/Net/ArpFields.lean`: `Operation`;
- the checksums have hand-written specs too: `proofs/Net/Crc.lean` and
  `proofs/Net/Checksum.lean`;
- `EthernetHeader`, `Ipv4Header`, `Ipv6Header`, `UdpHeader`, `IcmpHeader` and
  `ArpPacket` are derived and proved automatically on top of them;
- each `validate` has a hand-written spec in `proofs/Net/*Top.lean` that uses
  the derived ones and the spec of the layer below.

## Example: WireGuard (`crates/wireguard`)

`wireguard` is a sans-IO WireGuard implementation (`no_std`, no allocation),
built on `untrusted` and `net`, and verified as a whole: every function of the
crate is extracted to Lean and has a proved spec (`make verify-wireguard`,
`proofs/Wireguard/`). The proofs cover:

- **Messages:** the four message formats decode exactly as the WireGuard paper
  lays them out, and every encoder round-trips through its decoder.
- **Handshake:** Noise IKpsk2 computes exactly the paper's messages and
  keys, transcribed in `NoiseSpec.lean`. An agreement theorem shows that an
  honest run gives both sides the same transport keys.
- **Cookies:** `mac1`/`mac2` and cookie replies.
- **Replay window:** a counter is accepted exactly when it is fresh, and never
  twice.
- **Cryptokey routing:** a lookup returns the peer of the longest matching
  prefix.
- **Transport:** a packet is delivered exactly when it is authentic, its
  counter is fresh, and it is an IP packet (per `net`'s decoders) whose source
  routes back to the sending peer.
- **Device:** every entry point (`handle_packet`, `handle_datagram`, `tick`)
  keeps the device's invariant and never fails. Data goes out only under a
  keypair that may still send (younger than `REJECT_AFTER_TIME`, counter
  below `REJECT_AFTER_MESSAGES`), and its counter then goes up by one.
  Initiations to a peer are at least `REKEY_TIMEOUT` apart, and the local
  indices of live sessions are distinct.
- **Peers:** a device holds up to 512 peers and 1024 allowed IPs. Peers can
  be added and removed while it runs. A removed peer's sessions, handshake
  and allowed IPs go; its key no longer completes a handshake; and its slot is
  reused by the next `add_peer`.

The cryptographic primitives (X25519, BLAKE2s, ChaCha20-Poly1305,
XChaCha20-Poly1305) come in through a `Crypto` trait. The proofs only assume
the laws stated in `proofs/Wireguard/Crypto.lean`, as hypotheses, never as
axioms. `crates/wireguard-libcrux` implements the trait with the formally
verified [libcrux](https://github.com/cryspen/libcrux), and is tested against
the RFC test vectors; that it satisfies the laws is the trust assumption.

`crates/wg-userspace` is a small, unverified `no_std` interface around the
device, on `crates/wg-runtime` (configuration, sockets, TUN, the event loop,
and peers reloaded from a peers file on SIGHUP). Its UDP is `net`'s, not the
kernel's:

- incoming IP packets come from a packet socket and are validated by
  `net::udp`;
- outgoing datagrams are built by the verified encoders and sent through raw
  IP sockets;
- a TUN device carries the tunnel's packets.

`make wg-vm-test` runs it in two VMs against the Linux kernel's WireGuard. Each
side initiates a handshake; IPv4 and IPv6 pings and TCP transfers go both ways;
a spoofed source is dropped; and every captured WireGuard datagram is accepted
by `net-pcap`. Then it runs both sides with `wg-userspace`.

## Example: an ad-blocking packet filter (`crates/diomede`)

Ads arrive encrypted, so `diomede` blocks traffic *to ad domains*, where the
domain shows in the clear, as DNS blockers and SNI firewalls do. It also
closes the usual ways around such a filter. It is a sans-IO, `no_std` filter
built on `untrusted` and `net`, verified as a whole (`make verify-diomede`,
`proofs/Diomede/`):

```rust
let list = Blocklist::new(&data, &ends)?; // sorted domains, checked
match diomede::filter::classify(ip_packet, &list, &filter::STRICT, &mut out) {
    Verdict::Pass => { /* forward it */ }
    Verdict::Drop => { /* drop it */ }
    Verdict::Reply(n) | Verdict::Reset(n) => { /* drop it, send out[..n] back */ }
}
```

- **Blocklist:** `Blocklist::new` accepts exactly the storage whose entries
  are non-empty, within the data, and in strictly increasing order.
  `blocked(name)` holds exactly when the name is an entry or a subdomain of
  one (binary search on each suffix after a dot).
- **DNS:** `dns::DnsQuery` accepts exactly the standard queries with one
  question, a name of plain labels of at most 253 characters (RFC 1035 §4.1),
  lowercased. `dns::answer` writes exactly the answer with no records: same ID
  and question, RD copied, RA set, and the response code given.
- **TLS:** `tls::ClientHello` reads the first record of a TCP stream. It
  accepts exactly the handshake records holding a whole ClientHello whose
  vector lengths are consistent (RFC 8446 §4.1.2), and returns the host name
  of the first server_name extension (RFC 6066 §3), if there is one.
- **Filter:** `classify` decodes the packet as UDP or TCP over IPv4 or IPv6,
  and decides under a `Policy` (`STRICT` turns everything on):
  - A DNS query for a blocked name gets `Reply` with NXDOMAIN. With
    `strip_https_rr`, a query for HTTPS or SVCB records of any other name
    gets `Reply` with no records, so browsers get no Encrypted ClientHello
    keys and show the server name in the clear. A reply is proved to decode,
    by `net`'s decoders, as a packet from the server back to the client
    (addresses and ports swapped) carrying exactly that answer.
  - A ClientHello to port 443 for a blocked name, and with `block_dot` any
    DNS over TLS (TCP port 853), gets `Reset`. The reset is proved to decode
    as a TCP RST and ACK from the server back to the client, numbered so that
    the client accepts it.
  - With `block_quic`, QUIC (UDP port 443) gets `Drop`, and browsers fall
    back to TCP. With `block_dot`, DNS over QUIC (UDP port 853) gets `Drop`.
  - A reply or reset that does not fit in `out` gets `Drop`. Everything else
    gets `Pass`.

- **Streams:** a ClientHello often spans several TCP segments. `filter`
  sends TCP to port 443 through `stream::Streams`, a fixed table of 256
  connections that collects the start of each in order (up to 8 KiB, segments
  past a gap dropped for the client to send again) and checks its first
  record once complete. The table keeps an invariant: every tracked
  connection's state is the decision on the bytes collected for it. So a
  reset (`Reset`, then for the rest of the connection) happens only for a
  connection whose first record is a ClientHello for a blocked name.
  Everything else goes to `classify`.

`crates/diomede-pcap` is an unverified harness around it. It loads hosts
files or domain lists and runs a capture through `filter`. It reports what would be
blocked, and `--out` writes the capture without the blocked packets and with
the replies and resets. `make diomede-vm-test` checks it in two VMs: `dig`,
`openssl s_client` and `socat` against dnsmasq and `openssl s_server`, for ad
domains, a normal one, HTTPS records, QUIC and DNS over TLS.

Not covered: DNS over HTTPS to servers reached by address, ads served from
the site's own domain, and apps that bring their own resolver.

## Example: an ad-blocking VPN (`crates/ultranet`)

`ultranet` puts the two together: a WireGuard VPN server whose clients'
traffic goes through `diomede` before it reaches the internet. Clients use
any WireGuard app; the server uses the verified device (on `wg-runtime`,
holding up to 512 clients) and the verified filter:

```
phone ──WireGuard──▶ ultranet: wireguard::Device ─▶ diomede::filter::filter ─▶ NAT ─▶ internet
                                          ◀── NXDOMAIN, resets, through the tunnel
```

What makes the blocking hold:
- the client's DNS server is the VPN (`DNS = 10.77.0.1` in its
  configuration), and DNS sent anywhere else is redirected there, so every
  lookup is seen;
- HTTPS records get no answer, so browsers get no Encrypted ClientHello keys
  and show server names in the clear;
- QUIC and DNS over TLS or QUIC are refused, so browsers fall back to TCP
  and plain DNS;
- Firefox's DNS-over-HTTPS canary does not resolve, so Firefox turns DNS over
  HTTPS off.

Every decision on a packet is made by verified code; what is unverified is
plumbing: sockets, the loop, the resolver (unbound, forwarding over DNS over
TLS), NAT (nftables) and the list downloads.
The tunnel's MTU is 1408, a multiple of 16: the verified device pads packets
to 16 bytes without knowing the MTU, so a full packet must still fit a
1500-byte path over IPv6. The module clamps TCP connections to it.

Deploying it on NixOS:

```nix
{
  imports = [ ve-rs.nixosModules.ultranet ];
  services.ultranet = {
    enable = true;
    endpoint = "vpn.example.org:51820";
    # lists = [ ... ];  # StevenBlack's hosts by default, fetched daily
  };
}
```

Then, on the server:

```sh
ultranet-ctl add alice --qr   # a new client; scan the code with the WireGuard app
ultranet-ctl list             # the clients
ultranet-ctl remove alice     # its tunnel stops at once
ultranet-ctl stats            # what was blocked
ultranet-ctl update-lists     # fetch the lists now
```

`make ultranet-vm-test` runs it in three VMs: a client with the kernel's
WireGuard, the server, and an "internet" with DNS and TLS servers. It checks
DNS (direct and redirected), HTTPS records, TLS resets (including a
ClientHello in two segments), QUIC, DNS over TLS, reloading the blocklist,
and adding and removing clients.

Not covered: ads served from the site's own domain (YouTube, Facebook,
search ads), apps that bring their own resolver or connect by address, and
traffic sent while the VPN is off.

## Pros

- **Proved for every input, not just tested.** For each function the proofs
  establish:
  - it never panics: no out-of-bounds index, no overflow, no failed check;
  - it always terminates;
  - its result matches its specification exactly. For example, a big-endian
    decoder returns precisely the number its bytes denote, and an integer
    conversion succeeds if and only if the value fits.
- **Same behaviour in debug and release builds.** The proofs show that
  arithmetic never overflows, so release mode's wrap-on-overflow never comes
  into play.
- **Trailing data can't be ignored by mistake.** A `Reader` only exists inside
  `read_all`, which rejects leftover bytes. Doc tests confirm the bypasses fail
  to compile.
- **Your own structs are verified automatically.** `cargo untrusted verify`
  extracts your crate's `Decode` and `Encode` impls and proves each one reads
  or writes exactly its fields, in order. For a type with both, it also proves
  the round trip: decoding what was encoded gives the value back, for every
  value the decoder accepts. Nested derived structs compose.
- **The derive macro doesn't need to be trusted.** Its *output* is proved after
  expansion, and the expected format comes from the struct as Aeneas extracted
  it, not from the macro. A macro bug produces a failed proof, never a false
  guarantee. This is tested: an impl that reads fields in the wrong order is
  rejected.
- **No proof holes.** `make verify` runs an audit that fails if any function
  lacks a spec, or if any proof uses `sorry` or an axiom beyond Lean's standard
  three. The one extra axiom allowed is the abstract `Formatter` type, used only
  by `Debug`.
- **Small footprint.** `no_std`, no runtime dependencies. The derive macro uses
  `syn` and `quote` at compile time only.

## Cons

Please read these carefully. They are real costs, not footnotes.

- **Mostly not zero-copy.** Decoded values must own their data: a `Decode` type
  can't borrow from the input, because tying a decoded value's lifetime to the
  input is beyond what Aeneas can currently translate. The exception is a
  hand-written `Validate` impl over `&[u8]`, which may hand back borrowed
  `Untrusted` sub-slices (as `net::ethernet::Frame` does with its payload); that
  costs a hand-written spec. If you need zero-copy parsing throughout and can do
  without formal verification, use a crate such as
  [`nom`](https://crates.io/crates/nom) or
  [`winnow`](https://crates.io/crates/winnow).
- **Limited ergonomics.** There are no closures (`read_all` takes a type, not a
  function), no combinators, no streaming input, and no `alloc` types such as
  `Vec` or `String`. Every decodable type is a struct with a `Decode` impl.
- **Narrow format support today:**
  - fixed-width integers in either byte order, and fixed-size byte arrays;
  - structs made of those or of other derived structs;
  - **no** enums or tagged unions, length-prefixed fields or value
    constraints.

  The derives reject enums and unions, and type parameters (`Encode` accepts
  lifetimes). A round trip holds only for values the decoder accepts: an
  encoder writes any value, so a hand-written impl states which with a
  `Valid` predicate (an IPv4 header length of at least 5, say).
- **Verification is heavy.** The Lean side needs the Lean toolchain and Mathlib,
  which is about 8 GB on disk, and a Nix-based toolchain. Running
  `cargo untrusted verify` on every developer machine is impractical; plan to
  run it in CI.
- **Pinned, nightly toolchain.** Charon is a rustc driver, so extraction uses
  the exact nightly Rust it was built for, pinned through the Nix flake.
  Upgrading Aeneas means re-extracting, and possibly fixing proofs.
- **Only `Decode` and `Encode` impls are verified in your crate.**
  `cargo untrusted verify` extracts nothing else. The rest of your code, including how you *use* decoded
  values, carries no guarantees.
- **Hand-written `Decode` and `Encode` impls aren't proved automatically.** If
  an impl doesn't have the derive's shape, the verifier reports it, and you must
  write its Lean spec by hand (`<Module>/Manual.lean`), with a `RoundTrip`
  instance if derived types that contain it should get theirs.
- **`Debug` output isn't verified.** Aeneas models `core::fmt::Formatter` as an
  abstract type that records no output. The proofs only show that formatting
  never fails.
- **Not constant-time.** Nothing is proved about timing. This is fine for
  parsing, but not if secret data flows through these functions.
- **Platform assumption.** `usize` and `isize` are assumed to be 32 or 64 bits;
  16-bit targets are not covered.
- **Young project.** The crates are not published on crates.io yet, and the API
  may change.

## What "verified" does and doesn't cover

The proofs show the Rust code matches its Lean specification. They rely on a
*trusted base* of tools that are assumed correct:

- **rustc**, which produces the MIR that Charon reads and compiles the binary
  you actually run, together with LLVM.
- **Charon and Aeneas**, which translate Rust to Lean. These are mature
  research tools, but they are not themselves verified, so they are the largest
  trusted component.
- **The Lean kernel**, which checks the proofs. It is small and well studied.
- **The specifications themselves.** A proof can only show the code does what
  the spec *says*. The specs are short and reviewable: see
  `proofs/Untrusted/Spec.lean`, `proofs/Untrusted/Proofs/DecodesAs.lean` and
  `proofs/Untrusted/Proofs/{Writer,EncodesAs}.lean`.

Not trusted: the `#[derive(Decode)]` and `#[derive(Encode)]` macros, the
`cargo untrusted` tool, the spec-generating scripts, and the proof automation.
Everything they produce is re-checked by Lean.

## Getting started

Everything runs inside the Nix dev shell, which provides the pinned Rust
nightly, Charon, Aeneas and Lean (through `elan`):

```sh
nix develop
make lean-deps            # one-time: download Mathlib's prebuilt cache (large)
make test                 # Rust tests
make extract verify       # translate the crate to Lean, check proofs, audit
make verify-demo          # verify the example user crate
make verify-net           # verify the `net` crate (Ethernet up to UDP)
make verify-wireguard     # verify the `wireguard` crate
make verify-diomede       # verify the `diomede` crate
nix flake check           # tests and clippy (crane), extraction up to date, Aeneas pin consistent
make vm-test              # real traffic through `net` in two VMs (needs KVM)
make wg-vm-test           # wg-userspace against the kernel's WireGuard (needs KVM)
make diomede-vm-test      # DNS and TLS to ad domains through diomede-pcap (needs KVM)
make ultranet-vm-test     # the ad-blocking VPN end to end, in three VMs (needs KVM)
```

To verify the `Decode` and `Encode` impls in your own crate:

```sh
cargo untrusted verify -p <your-crate> \
    --lean-dir proofs --untrusted-lean <path-to-this-repo>/proofs
```

The tool extracts only your `Decode` and `Encode` impls, links them against the
verified `Untrusted` Lean library, proves every derived impl and every round
trip, and runs the audit. It
exits with an error if anything is unproved.

## Repository layout

| Path | Contents |
|---|---|
| `crates/untrusted` | The library. |
| `crates/untrusted-derive` | `#[derive(Decode)]` and `#[derive(Encode)]` (untrusted generators). |
| `crates/cargo-untrusted` | `cargo untrusted verify` (untrusted orchestrator). |
| `crates/net` | Verified packet decoding from Ethernet (802.1Q, CRC-32 FCS) through ARP, IPv4, IPv6 and ICMP to UDP and TCP, and UDP and TCP encoding (headers through `Encode`), built on `untrusted`. |
| `crates/wireguard` | A verified, sans-IO WireGuard core, built on `untrusted` and `net`. |
| `crates/wireguard-libcrux` | Its cryptographic primitives, from libcrux (not extracted; tested against RFC vectors). |
| `crates/wg-runtime` | The `no_std` runtime of userspace interfaces around the core: configuration, sockets, TUN, event loop, a hook on delivered packets; unverified. |
| `crates/wg-userspace` | A `no_std` WireGuard interface on `wg-runtime`; unverified. |
| `crates/diomede` | A verified, sans-IO ad-blocking filter (DNS and TLS SNI), built on `untrusted` and `net`. |
| `crates/diomede-lists` | Hosts files and domain lists, parsed for the blocklist; unverified. |
| `crates/diomede-pcap` | Runs a capture through the filter with hosts-file lists; unverified. |
| `crates/ultranet` | The ad-blocking VPN server: `wireguard` on `wg-runtime`, every client packet through `diomede`. |
| `crates/ultranet-admin` | Compiles blocklists, manages clients and their configurations; unverified. |
| `flake.nix`, `nix/modules/` | The flake, as flake-parts modules in the dendritic pattern: one file per feature (packages, VM tests, checks, dev shell), all imported by `import-tree`; the crates are built with crane, on dependencies built once. |
| `nix/modules/ultranet/nixos.nix` | The NixOS module `services.ultranet` (`nixosModules.ultranet`, `modules.nixos.ultranet`): interface, NAT, DNS redirection, unbound, list updates, `ultranet-ctl`. |
| `examples/net-pcap` | Runs a pcap capture through the `net` decoders. |
| `proofs/Net/`, `proofs/Wireguard/`, `proofs/Diomede/` | The Lean models and proofs of `net`, `wireguard` and `diomede`. |
| `examples/derive-demo` | An example user crate, verified by `make verify-demo`. |
| `proofs/Untrusted/{Types,Funs}.lean` | The Lean model, generated by `make extract`. |
| `proofs/Untrusted/Spec.lean` | Specification vocabulary (`beNat`, ranges, …). |
| `proofs/Untrusted/Proofs/` | Specs and proofs, partly generated by `proofs/scripts/gen_specs.sh`. |
| `proofs/Untrusted/Derive.lean` | The `derive_decode_spec`, `derive_encode_spec` and `derive_roundtrip_spec` commands. |
| `proofs/Untrusted/Audit.lean` | The `untrusted_audit` coverage and axiom check. |

## License

Licensed under the [Apache License, Version 2.0](LICENSE).

Unless you explicitly state otherwise, any contribution you intentionally
submit for inclusion in this project is licensed under the Apache License,
Version 2.0, without any additional terms or conditions.
