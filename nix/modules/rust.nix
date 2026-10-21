# The Rust workspace, as perSystem arguments the other modules share:
# `root` (the repository), `buildCrate` (one binary crate of the workspace),
# and the toolchains of the verification.
{ inputs, ... }:
{
  perSystem =
    { pkgs, inputs', ... }:
    let
      root = ../..;
    in
    {
      _module.args = {
        inherit root;
        # `aeneas` also ships the matching `charon` binary in its `bin/`.
        aeneasPkg = inputs'.aeneas.packages.aeneas;
        # Charon is a rustc driver, so the crate must be built with the exact
        # nightly toolchain Charon was compiled against.
        rustToolchain = inputs'.charon.packages.rustToolchain;
        aeneasRev = inputs.aeneas.rev;
        buildCrate =
          name:
          pkgs.rustPlatform.buildRustPackage {
            pname = name;
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              inherit root;
              fileset = pkgs.lib.fileset.unions [
                (root + "/Cargo.toml")
                (root + "/Cargo.lock")
                (root + "/.cargo")
                (root + "/crates")
                (root + "/examples")
              ];
            };
            cargoLock.lockFile = root + "/Cargo.lock";
            cargoBuildFlags = [
              "-p"
              name
            ];
            doCheck = false;
          };
      };
    };
}
