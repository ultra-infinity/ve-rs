# The flake is a set of flake-parts modules, one per file under nix/modules
# (the dendritic pattern): each file is named for what it provides and is
# imported by import-tree. `flake.modules.<class>.<name>` holds modules for
# other configurations, such as NixOS.
{ inputs, ... }:
{
  imports = [ inputs.flake-parts.flakeModules.modules ];
  systems = [
    "x86_64-linux"
    "aarch64-linux"
    "x86_64-darwin"
    "aarch64-darwin"
  ];
}
