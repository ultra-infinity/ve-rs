# Checks that the verification is reproducible: the Lean library is pinned
# to the Aeneas binary's commit, and the committed models are what the
# extraction produces from the Rust sources.
{
  perSystem =
    {
      pkgs,
      root,
      craneLib,
      aeneasPkg,
      rustToolchain,
      aeneasRev,
      ...
    }:
    {
      checks = {
        # The Lean `aeneas` library must come from the same commit as the
        # `aeneas` binary, otherwise the generated code may not typecheck.
        aeneas-pin = pkgs.runCommand "untrusted-check-aeneas-pin" { } ''
          if ! grep -q 'rev = "${aeneasRev}"' ${root + "/proofs/lakefile.toml"}; then
            echo 'ERROR: proofs/lakefile.toml does not require aeneas at ${aeneasRev}'
            echo '(the revision locked in flake.lock). Run `make aeneas-pin`.'
            exit 1
          fi
          touch $out
        '';

        # Re-run the extraction and make sure the committed Lean files are
        # up to date with the Rust sources.
        extraction = (craneLib.overrideToolchain rustToolchain).mkCargoDerivation {
          pname = "untrusted-check-extraction";
          version = "0.1.0";
          src = pkgs.lib.fileset.toSource {
            inherit root;
            fileset = pkgs.lib.fileset.unions [
              (root + "/Cargo.toml")
              (root + "/Cargo.lock")
              (root + "/Makefile")
              (root + "/crates")
              (root + "/examples")
              (root + "/proofs/Untrusted")
              (root + "/proofs/DeriveDemo")
              (root + "/proofs/Net")
              (root + "/proofs/Wireguard")
              (root + "/proofs/Diomede")
              (root + "/proofs/lakefile.toml")
            ];
          };
          # crane vendors the crates.io dependencies (the sandbox has no
          # network); nothing is built ahead of the extraction.
          cargoArtifacts = null;
          doInstallCargoArtifacts = false;
          nativeBuildInputs = [
            aeneasPkg
            pkgs.gnumake
          ];
          buildPhaseCargoCommand = ''
            export HOME=$TMPDIR
            cp -r proofs proofs-committed
            make extract
            diff -ru proofs-committed/Untrusted proofs/Untrusted || {
              echo 'ERROR: generated Lean files are stale. Run `make extract`.'
              exit 1
            }
            # The example user crate's model, linked against `Untrusted`.
            cargo run -q -p cargo-untrusted -- untrusted verify -p derive-demo \
              --lean-dir proofs --extract-only
            diff -ru proofs-committed/DeriveDemo proofs/DeriveDemo || {
              echo 'ERROR: the derive-demo model is stale. Run `make verify-demo`.'
              exit 1
            }
            cargo run -q -p cargo-untrusted -- untrusted verify -p net --extract-all \
              --lean-dir proofs --extract-only
            diff -ru proofs-committed/Net proofs/Net || {
              echo 'ERROR: the net model is stale. Run `make verify-net`.'
              exit 1
            }
            cargo run -q -p cargo-untrusted -- untrusted verify -p wireguard \
              --lean-dir proofs --extract-only --extract-all --link net=Net
            diff -ru proofs-committed/Wireguard proofs/Wireguard || {
              echo 'ERROR: the wireguard model is stale. Run `make verify-wireguard`.'
              exit 1
            }
            cargo run -q -p cargo-untrusted -- untrusted verify -p diomede \
              --lean-dir proofs --extract-only --extract-all --link net=Net
            diff -ru proofs-committed/Diomede proofs/Diomede || {
              echo 'ERROR: the diomede model is stale. Run `make verify-diomede`.'
              exit 1
            }
          '';
          installPhaseCommand = "touch $out";
        };
      };
    };
}
