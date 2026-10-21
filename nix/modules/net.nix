# `net-pcap`, which runs a pcap capture through the verified `net` decoders,
# and its VM test: two VMs on a virtual LAN, the client sending ARP, ICMP and
# UDP over IPv4 and IPv6, the server capturing what it receives and running
# it through `net-pcap`, failing if any frame is rejected or any layer saw no
# traffic. Run with `make vm-test` (needs KVM).
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
        net-pcap = buildCrate "net-pcap";
      }
      // lib.optionalAttrs pkgs.stdenv.hostPlatform.isLinux {
        net-vm-test = pkgs.testers.runNixOSTest {
          name = "net-vm-test";
          nodes =
            let
              common = {
                networking.firewall.enable = false;
                environment.systemPackages = [
                  pkgs.ethtool
                  pkgs.socat
                  pkgs.tcpdump
                ];
              };
            in
            {
              client = common;
              server = common // {
                environment.systemPackages = common.environment.systemPackages ++ [
                  config.packages.net-pcap
                ];
              };
            };
          testScript = builtins.readFile (root + "/examples/net-pcap/vm-test.py");
        };
      };
    };
}
