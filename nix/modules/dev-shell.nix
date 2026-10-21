# The development shell: the pinned Rust nightly, Charon, Aeneas and Lean
# (through `elan`); and the formatter.
{
  perSystem =
    {
      pkgs,
      aeneasPkg,
      rustToolchain,
      ...
    }:
    {
      devShells.default = pkgs.mkShell {
        packages = [
          aeneasPkg
          rustToolchain
          pkgs.elan
          pkgs.gnumake
          pkgs.taplo
        ];
      };
      formatter = pkgs.nixfmt;
    };
}
