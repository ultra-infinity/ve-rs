{
  description = "untrusted: a no_std Rust library verified with Aeneas (Lean backend)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    aeneas.url = "github:AeneasVerif/aeneas";
    # Charon is pinned by Aeneas; reuse it so the LLBC format always matches.
    charon.follows = "aeneas/charon";
    flake-utils.follows = "aeneas/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      aeneas,
      charon,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # `aeneas` also ships the matching `charon` binary in its `bin/`.
        aeneasPkg = aeneas.packages.${system}.aeneas;
        # Charon is a rustc driver, so the crate must be built with the exact
        # nightly toolchain Charon was compiled against.
        rustToolchain = charon.packages.${system}.rustToolchain;

        aeneasRev = aeneas.rev;
      in
      {
        checks = {
          # The Lean `aeneas` library must come from the same commit as the
          # `aeneas` binary, otherwise the generated code may not typecheck.
          aeneas-pin = pkgs.runCommand "untrusted-check-aeneas-pin" { } ''
            if ! grep -q 'rev = "${aeneasRev}"' ${./proofs/lakefile.toml}; then
              echo 'ERROR: proofs/lakefile.toml does not require aeneas at ${aeneasRev}'
              echo '(the revision locked in flake.lock). Run `make aeneas-pin`.'
              exit 1
            fi
            touch $out
          '';

          # Re-run the extraction and make sure the committed Lean files are
          # up to date with the Rust sources.
          extraction = pkgs.stdenv.mkDerivation {
            name = "untrusted-check-extraction";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [
                ./Cargo.toml
                ./Cargo.lock
                ./Makefile
                ./crates
                ./examples
                ./proofs/Untrusted
                ./proofs/DeriveDemo
                ./proofs/Net
                ./proofs/Wireguard
                ./proofs/Diomede
                ./proofs/lakefile.toml
              ];
            };
            # The sandbox has no network access: vendor the crates.io deps.
            cargoDeps = pkgs.rustPlatform.importCargoLock { lockFile = ./Cargo.lock; };
            nativeBuildInputs = [
              aeneasPkg
              rustToolchain
              pkgs.gnumake
              pkgs.rustPlatform.cargoSetupHook
            ];
            buildPhase = ''
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
            installPhase = "touch $out";
          };
        };

        # `net-pcap`: runs a pcap capture through the verified `net` decoders.
        packages = {
          net-pcap = pkgs.rustPlatform.buildRustPackage {
            pname = "net-pcap";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [
                ./Cargo.toml
                ./Cargo.lock
                ./crates
                ./examples
              ];
            };
            cargoLock.lockFile = ./Cargo.lock;
            cargoBuildFlags = [
              "-p"
              "net-pcap"
            ];
            doCheck = false;
          };
          # `wg-userspace`: a WireGuard interface around the verified device.
          wg-userspace = pkgs.rustPlatform.buildRustPackage {
            pname = "wg-userspace";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [
                ./Cargo.toml
                ./Cargo.lock
                ./crates
                ./examples
              ];
            };
            cargoLock.lockFile = ./Cargo.lock;
            cargoBuildFlags = [
              "-p"
              "wg-userspace"
            ];
            doCheck = false;
          };
          # `diomede-pcap`: runs a capture through the verified ad filter.
          diomede-pcap = pkgs.rustPlatform.buildRustPackage {
            pname = "diomede-pcap";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [
                ./Cargo.toml
                ./Cargo.lock
                ./crates
                ./examples
              ];
            };
            cargoLock.lockFile = ./Cargo.lock;
            cargoBuildFlags = [
              "-p"
              "diomede-pcap"
            ];
            doCheck = false;
          };
        }

        # Two VMs on a virtual LAN: the client sends ARP, ICMP and UDP over
        # IPv4 and IPv6; the server captures what it receives and runs it
        # through `net-pcap`, failing if any frame is rejected or any layer saw
        # no traffic. Run with `make vm-test` (needs KVM).
        // pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {
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
                    self.packages.${system}.net-pcap
                  ];
                };
              };
            testScript = builtins.readFile ./examples/net-pcap/vm-test.py;
          };

          # Two VMs: `a` runs wg-userspace, `b` the kernel's WireGuard, then
          # wg-userspace too; see crates/wg-userspace/vm-test.py. Run with
          # `make wg-vm-test` (needs KVM).
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
                    self.packages.${system}.wg-userspace
                    self.packages.${system}.net-pcap
                  ];
                };
              in
              {
                a = node;
                b = node;
              };
            testScript = builtins.readFile ./crates/wg-userspace/vm-test.py;
          };

          # The client looks up and connects to ad domains and a normal one;
          # the server (dnsmasq, `openssl s_server`) captures it and runs
          # `diomede-pcap`; see crates/diomede-pcap/vm-test.py. Run with
          # `make diomede-vm-test` (needs KVM).
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
                    self.packages.${system}.diomede-pcap
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
            testScript = builtins.readFile ./crates/diomede-pcap/vm-test.py;
          };
        };

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
      }
    );
}
