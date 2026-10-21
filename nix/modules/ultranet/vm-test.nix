# The ultranet VPN end to end: a client with kernel WireGuard, the server
# (services.ultranet), and an "internet" with DNS and TLS servers; see
# crates/ultranet/vm-test.py. Run with `make ultranet-vm-test` (needs KVM).
{ config, ... }:
let
  inherit (config.flake.modules) nixos;
in
{
  perSystem =
    {
      pkgs,
      lib,
      root,
      ...
    }:
    {
      packages = lib.optionalAttrs pkgs.stdenv.hostPlatform.isLinux {
        ultranet-vm-test = pkgs.testers.runNixOSTest {
          name = "ultranet-vm-test";
          nodes = {
            # The client and the server share network 1; the server and the
            # "internet" network 2, so the client reaches it only through the
            # tunnel.
            internet =
              { config, ... }:
              {
                virtualisation.vlans = [ 2 ];
                networking.firewall.enable = false;
                environment.systemPackages = [
                  pkgs.openssl
                  pkgs.socat
                ];
                services.dnsmasq = {
                  enable = true;
                  resolveLocalQueries = false;
                  settings = {
                    no-resolv = true;
                    # Every name resolves here, so only the filter decides.
                    address = [ "/#/${config.networking.primaryIPAddress}" ];
                  };
                };
              };
            server =
              { nodes, ... }:
              {
                imports = [ nixos.ultranet ];
                virtualisation.vlans = [
                  1
                  2
                ];
                services.ultranet = {
                  enable = true;
                  endpoint = "server:51820";
                  lists = [ ];
                  extraLists = [
                    (pkgs.writeText "ads" "0.0.0.0 ads.example\n0.0.0.0 tracker.io\n")
                  ];
                  upstreamDns = [ nodes.internet.networking.primaryIPAddress ];
                  upstreamTls = false;
                };
                # The test's names are not signed.
                services.unbound.enableRootTrustAnchor = false;
              };
            client = {
              virtualisation.vlans = [ 1 ];
              networking.firewall.enable = false;
              environment.systemPackages = [
                pkgs.curl
                pkgs.dig
                pkgs.openssl
                pkgs.socat
                pkgs.wireguard-tools
              ];
            };
          };
          testScript = builtins.readFile (root + "/crates/ultranet/vm-test.py");
        };
      };
    };
}
