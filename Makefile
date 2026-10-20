# Rust → Charon (LLBC) → Aeneas → Lean pipeline. Run inside `nix develop`.

CRATE  := untrusted
LLBC   := target/charon/$(CRATE).llbc
PROOFS := proofs
SUBDIR := Untrusted

.PHONY: all build test llbc extract specs lean-deps verify verify-demo verify-net verify-wireguard verify-adfilter vm-test wg-vm-test adfilter-vm-test aeneas-pin clean

all: extract verify verify-demo verify-net verify-wireguard verify-adfilter

build:
	cargo build --workspace

test:
	cargo test --workspace

# Everything in the crate is translated, including derived impls.
CHARON_FLAGS := --preset=aeneas

# Loops become structurally recursive functions, which the Aeneas proof
# tooling handles best.
AENEAS_FLAGS := -backend lean -split-files -loops-to-rec

# Translate the crate to LLBC with Charon.
llbc:
	charon cargo $(CHARON_FLAGS) --dest-file $(LLBC) -- -p $(CRATE)

# Generate the Lean model in $(PROOFS)/$(SUBDIR)/{Types,Funs}.lean.
extract: llbc
	aeneas $(AENEAS_FLAGS) -subdir $(SUBDIR) -dest $(PROOFS) $(LLBC)

# Regenerate the per-type spec files in $(PROOFS)/Untrusted/Proofs/.
specs:
	$(PROOFS)/scripts/gen_specs.sh

# Download prebuilt Mathlib oleans (Aeneas depends on Mathlib).
lean-deps:
	cd $(PROOFS) && lake exe cache get

# Formally verify the `Decode` impls of the example user crate.
verify-demo:
	cargo run -q -p cargo-untrusted -- untrusted verify -p derive-demo --lean-dir $(PROOFS)

# Formally verify the `net` crate: every item, decoders and encoders (its
# hand-written specs are in $(PROOFS)/Net/Manual*.lean).
NET_FLAGS := --extract-all
verify-net:
	cargo run -q -p cargo-untrusted -- untrusted verify -p net --lean-dir $(PROOFS) $(NET_FLAGS)

# Formally verify the `wireguard` crate: every item, not only its `Decode` impls,
# linked against the verified `net` model (hand-written specs in
# $(PROOFS)/Wireguard/).
WIREGUARD_FLAGS := --extract-all --link net=Net
verify-wireguard:
	cargo run -q -p cargo-untrusted -- untrusted verify -p wireguard --lean-dir $(PROOFS) $(WIREGUARD_FLAGS)

# Formally verify the `adfilter` crate: every item, linked against the
# verified `net` model (hand-written specs in $(PROOFS)/Adfilter/).
ADFILTER_FLAGS := --extract-all --link net=Net
verify-adfilter:
	cargo run -q -p cargo-untrusted -- untrusted verify -p adfilter --lean-dir $(PROOFS) $(ADFILTER_FLAGS)

# Run real traffic through the verified `net` decoders: two QEMU VMs exchange
# ARP, ICMP and UDP over IPv4 and IPv6 (needs KVM). The capture and the
# report end up in `result/`.
vm-test:
	nix build .#net-vm-test -L

wg-vm-test:
	nix build .#wg-vm-test -L

adfilter-vm-test:
	nix build .#adfilter-vm-test -L

# Check the generated model and the proofs, then audit that every model
# function has a spec and nothing relies on `sorry` or unexpected axioms.
verify:
	cd $(PROOFS) && lake build && lake env lean Audit.lean

# Point the Lean `aeneas` dependency and toolchain at the revision locked in
# flake.lock. Run after `nix flake update aeneas`.
aeneas-pin:
	rev=$$(nix eval --raw --impure --expr '(builtins.getFlake (toString ./.)).inputs.aeneas.rev') && \
	src=$$(nix eval --raw --impure --expr '(builtins.getFlake (toString ./.)).inputs.aeneas.outPath') && \
	sed -i "s/^rev = \".*\"/rev = \"$$rev\"/" $(PROOFS)/lakefile.toml && \
	cp $$src/backends/lean/lean-toolchain $(PROOFS)/lean-toolchain && \
	chmod u+w $(PROOFS)/lean-toolchain && \
	cd $(PROOFS) && lake update aeneas

clean:
	cargo clean
	rm -rf $(PROOFS)/.lake
