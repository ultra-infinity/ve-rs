# `diomede-pcap`, which runs a capture through the verified ad filter, and
# its VM test: the client looks up and connects to ad domains and a normal
# one; the server (dnsmasq, `openssl s_server`) captures it and runs
# `diomede-pcap`; see crates/diomede-pcap/vm-test.py. Run with
# `make diomede-vm-test` (needs KVM).
{
  perSystem =
    {
      config,
      pkgs,
      lib,
      root,
      buildCrate,
      ...
    }:
    {
      packages = {
        diomede-pcap = buildCrate "diomede-pcap";
      }
      // lib.optionalAttrs pkgs.stdenv.hostPlatform.isLinux {
        diomede-vm-test = pkgs.testers.runNixOSTest {
          name = "diomede-vm-test";
          nodes =
            let
              common = {
                networking.firewall.enable = false;
                environment.systemPackages = [
                  pkgs.dig
                  pkgs.ethtool
                  pkgs.openssl
                  pkgs.socat
                  pkgs.tcpdump
                ];
              };
            in
            {
              client = common;
              server = common // {
                environment.systemPackages = common.environment.systemPackages ++ [
                  config.packages.diomede-pcap
                ];
                services.dnsmasq = {
                  enable = true;
                  resolveLocalQueries = false;
                  settings = {
                    no-resolv = true;
                    # Every name resolves, so that only the filter decides.
                    address = [ "/#/192.0.2.1" ];
                  };
                };
              };
            };
          testScript = builtins.readFile (root + "/crates/diomede-pcap/vm-test.py");
        };
      };
    };
}
