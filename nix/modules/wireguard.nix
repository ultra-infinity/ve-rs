# `wg-userspace`, a WireGuard interface around the verified device, and its
# VM test: `a` runs wg-userspace, `b` the kernel's WireGuard, then
# wg-userspace too; see crates/wg-userspace/vm-test.py. Run with
# `make wg-vm-test` (needs KVM).
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
        wg-userspace = buildCrate "wg-userspace";
      }
      // lib.optionalAttrs pkgs.stdenv.hostPlatform.isLinux {
        wg-vm-test = pkgs.testers.runNixOSTest {
          name = "wg-vm-test";
          nodes =
            let
              node = {
                networking.firewall.enable = false;
                boot.kernelModules = [
                  "wireguard"
                  "tun"
                ];
                environment.systemPackages = [
                  pkgs.ethtool
                  pkgs.socat
                  pkgs.tcpdump
                  pkgs.wireguard-tools
                  config.packages.wg-userspace
                  config.packages.net-pcap
                ];
              };
            in
            {
              a = node;
              b = node;
            };
          testScript = builtins.readFile (root + "/crates/wg-userspace/vm-test.py");
        };
      };
    };
}
