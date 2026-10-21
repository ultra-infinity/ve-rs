# The Rust workspace, built with crane, as perSystem arguments the other
# modules share: `root` (the repository), `craneLib`, `buildCrate` (one
# binary crate of the workspace, on dependencies built once for all of
# them), and the toolchains of the verification. Also the workspace's
# clippy and test checks.
{ inputs, ... }:
{
  perSystem =
    {
      pkgs,
      inputs',
      root,
      craneLib,
      ...
    }:
    let
      # Only what Cargo reads: a change to a VM test's script rebuilds nothing.
      src = craneLib.cleanCargoSource root;
      common = {
        inherit src;
        pname = "ve-rs";
        version = "0.1.0";
        strictDeps = true;
      };
      # The workspace's crates.io dependencies, built once.
      cargoArtifacts = craneLib.buildDepsOnly common;
    in
    {
      _module.args = {
        root = ../..;
        craneLib = inputs.crane.mkLib pkgs;
        # `aeneas` also ships the matching `charon` binary in its `bin/`.
        aeneasPkg = inputs'.aeneas.packages.aeneas;
        # Charon is a rustc driver, so the crate must be built with the exact
        # nightly toolchain Charon was compiled against.
        rustToolchain = inputs'.charon.packages.rustToolchain;
        aeneasRev = inputs.aeneas.rev;
        buildCrate =
          name:
          craneLib.buildPackage (
            common
            // {
              inherit cargoArtifacts;
              pname = name;
              cargoExtraArgs = "--locked -p ${name}";
              doCheck = false;
            }
          );
      };

      checks = {
        clippy = craneLib.cargoClippy (
          common
          // {
            inherit cargoArtifacts;
            cargoClippyExtraArgs = "--workspace --all-targets -- --deny warnings";
          }
        );
        tests = craneLib.cargoTest (
          common
          // {
            inherit cargoArtifacts;
            cargoTestExtraArgs = "--workspace";
          }
        );
      };
    };
}
