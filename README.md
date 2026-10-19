# ve-rs: verified Rust for untrusted input

`untrusted` is a `no_std`, dependency-free Rust library for turning untrusted
bytes into typed values. Every function in it is **formally verified**: its Rust
code is translated to [Lean 4](https://lean-lang.org) with
[Charon and Aeneas](https://github.com/AeneasVerif/aeneas), and each function
is proved, for *all* inputs, to never panic, to always terminate, and to return
exactly what its specification says.

You can also `#[derive(Decode)]` on your own structs, and `cargo untrusted
verify` proves those derived decoders correct without you writing any proofs.

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
- **`#[derive(Decode)]`:** decodes a struct's fields one after another, in
  declaration order. Works for named, tuple and unit structs.

## Example: Ethernet II frames (`crates/net`)

The `net` crate is a verified decoder for Ethernet II frames, built on
`untrusted`:

```rust
let frame = Untrusted::new(bytes).validate::<net::ethernet::Frame>()?;
// frame.header.dst, frame.header.src,
// frame.header.tagging.vlan (an optional 802.1Q tag), frame.header.tagging.ether_type
// frame.payload is still `Untrusted`: the next layer (e.g. IPv4) validates it.

// With the trailing frame check sequence:
let checked = Untrusted::new(bytes_with_fcs).validate::<net::ethernet::FrameWithFcs>()?;
```

`Frame::validate` is proved to accept **exactly** the well-formed frames:
- untagged: a 14-byte header and 46 to 1500 bytes of payload;
- 802.1Q-tagged (bytes 12–13 are `0x8100`): an 18-byte header and 42 to 1500
  bytes of payload. The tag's VLAN ID is never the reserved `0xFFF`, and
  stacked tags (QinQ) are rejected;
- an EtherType of at least `0x0600` (smaller values are 802.3 lengths);
- the header fields decoded in order;
- the payload exactly the remaining bytes, borrowed from the input without
  copying.

`FrameWithFcs::validate` additionally accepts exactly the frames whose last 4
bytes (least significant first) are the CRC-32 of the rest. The Rust CRC is
proved equal to a Lean definition of the IEEE 802.3 CRC-32, and that
definition is checked in Lean's kernel against the standard check value
(`"123456789"` gives `0xCBF43926`).

It also shows how hand-written and derived proofs combine:
- `MacAddr`, `EtherType`, `VlanTag` and `Tagging` have hand-written specs
  (`proofs/Net/Fields.lean`), as does CRC-32 (`proofs/Net/Crc.lean`);
- `EthernetHeader` is derived and proved automatically on top of them;
- `Frame::validate` and `FrameWithFcs::validate` have hand-written specs
  (`proofs/Net/ManualTop.lean`) that use the derived one.

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
  extracts your crate's `Decode` impls and proves each one decodes exactly its
  fields, in order. Nested derived structs compose.
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
  - fixed-width integers in either byte order;
  - structs made of those or of other derived structs;
  - **no** enums or tagged unions, length-prefixed fields, value constraints,
    or encoding (writing bytes back).

  `#[derive(Decode)]` rejects enums, unions and generic structs.
- **Verification is heavy.** The Lean side needs the Lean toolchain and Mathlib,
  which is about 8 GB on disk, and a Nix-based toolchain. Running
  `cargo untrusted verify` on every developer machine is impractical; plan to
  run it in CI.
- **Pinned, nightly toolchain.** Charon is a rustc driver, so extraction uses
  the exact nightly Rust it was built for, pinned through the Nix flake.
  Upgrading Aeneas means re-extracting, and possibly fixing proofs.
- **Only `Decode` impls are verified in your crate.** `cargo untrusted verify`
  extracts nothing else. The rest of your code, including how you *use* decoded
  values, carries no guarantees.
- **Hand-written `Decode` impls aren't proved automatically.** If an impl
  doesn't have the derive's shape, the verifier reports it, and you must write
  its Lean spec by hand (`<Module>/Manual.lean`).
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
  `proofs/Untrusted/Spec.lean` and `proofs/Untrusted/Proofs/DecodesAs.lean`.

Not trusted: the `#[derive(Decode)]` macro, the `cargo untrusted` tool, the
spec-generating scripts, and the proof automation. Everything they produce is
re-checked by Lean.

## Getting started

Everything runs inside the Nix dev shell, which provides the pinned Rust
nightly, Charon, Aeneas and Lean (through `elan`):

```sh
nix develop
make lean-deps            # one-time: download Mathlib's prebuilt cache (large)
make test                 # Rust tests
make extract verify       # translate the crate to Lean, check proofs, audit
make verify-demo          # verify the example user crate
make verify-net           # verify the `net` crate
nix flake check           # extraction up to date, Aeneas pin consistent
```

To verify the `Decode` impls in your own crate:

```sh
cargo untrusted verify -p <your-crate> \
    --lean-dir proofs --untrusted-lean <path-to-this-repo>/proofs
```

The tool extracts only your `Decode` impls, links them against the verified
`Untrusted` Lean library, proves every derived impl, and runs the audit. It
exits with an error if anything is unproved.

## Repository layout

| Path | Contents |
|---|---|
| `crates/untrusted` | The library. |
| `crates/untrusted-derive` | `#[derive(Decode)]` (untrusted generator). |
| `crates/cargo-untrusted` | `cargo untrusted verify` (untrusted orchestrator). |
| `crates/net` | Verified Ethernet II decoding (802.1Q tags, CRC-32 FCS), built on `untrusted`. |
| `examples/derive-demo` | An example user crate, verified by `make verify-demo`. |
| `proofs/Untrusted/{Types,Funs}.lean` | The Lean model, generated by `make extract`. |
| `proofs/Untrusted/Spec.lean` | Specification vocabulary (`beNat`, ranges, …). |
| `proofs/Untrusted/Proofs/` | Specs and proofs, partly generated by `proofs/scripts/gen_specs.sh`. |
| `proofs/Untrusted/Derive.lean` | The `derive_decode_spec` command. |
| `proofs/Untrusted/Audit.lean` | The `untrusted_audit` coverage and axiom check. |

## License

Licensed under the [Apache License, Version 2.0](LICENSE).

Unless you explicitly state otherwise, any contribution you intentionally
submit for inclusion in this project is licensed under the Apache License,
Version 2.0, without any additional terms or conditions.
