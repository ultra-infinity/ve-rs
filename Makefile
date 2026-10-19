# Rust → Charon (LLBC) → Aeneas → Lean pipeline. Run inside `nix develop`.

CRATE  := untrusted
LLBC   := target/charon/$(CRATE).llbc
PROOFS := proofs
SUBDIR := Untrusted

.PHONY: all build test llbc extract specs lean-deps verify aeneas-pin clean

all: extract verify

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
