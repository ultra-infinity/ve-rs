{
  description = "untrusted: a no_std Rust library verified with Aeneas (Lean backend)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    flake-parts.url = "github:hercules-ci/flake-parts";
    flake-parts.inputs.nixpkgs-lib.follows = "nixpkgs";
    import-tree.url = "github:vic/import-tree";

    aeneas.url = "github:AeneasVerif/aeneas";
    # Charon is pinned by Aeneas; reuse it so the LLBC format always matches.
    charon.follows = "aeneas/charon";
  };

  # Every file under nix/modules is a flake-parts module (the dendritic
  # pattern); see nix/modules/flake-parts.nix.
  outputs =
    inputs: inputs.flake-parts.lib.mkFlake { inherit inputs; } (inputs.import-tree ./nix/modules);
}
