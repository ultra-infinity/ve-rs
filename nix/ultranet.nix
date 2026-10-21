# The ultranet VPN server: `services.ultranet`.
#
# Clients connect with WireGuard; ultranet (the verified WireGuard device and
# the verified diomede filter) blocks ads and trackers by name; unbound
# resolves what passes, over DNS over TLS. This module sets up the tunnel
# interface, forwarding and NAT, the redirection of all DNS to the resolver,
# and the blocklist updates. Clients are managed with `ultranet-ctl`.
self:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.services.ultranet;
  inherit (lib) mkOption mkEnableOption mkIf types;
  ultranet = self.packages.${pkgs.stdenv.hostPlatform.system}.ultranet;
  admin = self.packages.${pkgs.stdenv.hostPlatform.system}.ultranet-admin;
  state = "/var/lib/ultranet";
  # The server's addresses, without the prefix length.
  addr4 = builtins.head (lib.splitString "/" cfg.address4);
  addr6 = builtins.head (lib.splitString "/" cfg.address6);
  # The networks of the subnets, for `ultranet-admin`.
  net4 = cfg.subnet4;
  net6 = cfg.subnet6;
  flags = lib.concatStringsSep " " (
    lib.optional cfg.policy.allowQuic "--allow-quic"
    ++ lib.optional cfg.policy.allowDnsOverTls "--allow-dot"
    ++ lib.optional cfg.policy.keepHttpsRecords "--keep-https-records"
  );
  # Downloads the lists (keeping the last copy of any that fails) and
  # compiles them with the local ones.
  updateLists = pkgs.writeShellScript "ultranet-update-lists" ''
    set -u
    mkdir -p ${state}/lists
    i=0
    for url in ${lib.escapeShellArgs cfg.lists}; do
      i=$((i + 1))
      if ${pkgs.curl}/bin/curl -fsSL --max-time 300 -o ${state}/lists/$i.tmp "$url"; then
        mv ${state}/lists/$i.tmp ${state}/lists/$i.txt
      else
        echo "ultranet: could not fetch $url; keeping the last copy" >&2
        rm -f ${state}/lists/$i.tmp
      fi
    done
    args=()
    for f in ${state}/lists/*.txt ${lib.escapeShellArgs cfg.extraLists}; do
      [ -e "$f" ] && args+=(--list "$f")
    done
    ${admin}/bin/ultranet-admin compile-list "''${args[@]}" --out ${state}/blocklist.bin
  '';
  ctl = pkgs.writeShellScriptBin "ultranet-ctl" ''
    set -eu
    admin=${admin}/bin/ultranet-admin
    case "''${1:-}" in
      add)
        [ $# -ge 2 ] || { echo "usage: ultranet-ctl add NAME [--qr]" >&2; exit 2; }
        shift; name=$1; shift
        exec $admin add-peer --peers ${state}/peers --name "$name" \
          --server-key ${state}/server.key --endpoint ${lib.escapeShellArg cfg.endpoint} \
          --subnet4 ${net4} --subnet6 ${net6} --reload "$@"
        ;;
      remove)
        [ $# -eq 2 ] || { echo "usage: ultranet-ctl remove NAME" >&2; exit 2; }
        exec $admin remove-peer --peers ${state}/peers --name "$2" --reload
        ;;
      list) exec $admin list-peers --peers ${state}/peers ;;
      stats) exec $admin stats --stats /run/ultranet/stats ;;
      update-lists) exec systemctl start ultranet-lists.service ;;
      *)
        echo "usage: ultranet-ctl add NAME [--qr] | remove NAME | list | stats | update-lists" >&2
        exit 2
        ;;
    esac
  '';
in
{
  options.services.ultranet = {
    enable = mkEnableOption "the ultranet ad-blocking VPN server";
    interface = mkOption {
      type = types.str;
      default = "ultranet0";
      description = "The tunnel interface.";
    };
    port = mkOption {
      type = types.port;
      default = 51820;
      description = "The UDP port clients connect to.";
    };
    endpoint = mkOption {
      type = types.str;
      example = "vpn.example.org:51820";
      description = "The host and port clients connect to, written into their configurations.";
    };
    subnet4 = mkOption {
      type = types.str;
      default = "10.77.0.0/16";
      description = "The clients' IPv4 subnet.";
    };
    subnet6 = mkOption {
      type = types.str;
      default = "fd77::/64";
      description = "The clients' IPv6 subnet.";
    };
    address4 = mkOption {
      type = types.str;
      default = "10.77.0.1/16";
      description = "The server's IPv4 address on the tunnel: the clients' DNS server.";
    };
    address6 = mkOption {
      type = types.str;
      default = "fd77::1/64";
      description = "The server's IPv6 address on the tunnel.";
    };
    mtu = mkOption {
      type = types.int;
      default = 1408;
      description = "The tunnel's MTU. A multiple of 16: the device pads packets to 16 bytes, so a full packet still fits a 1500-byte path over IPv6 (40 + 8 + 32 bytes of headers). Clients' TCP connections are clamped to it.";
    };
    lists = mkOption {
      type = types.listOf types.str;
      default = [ "https://raw.githubusercontent.com/StevenBlack/hosts/master/hosts" ];
      description = "URLs of hosts files or domain lists to block.";
    };
    extraLists = mkOption {
      type = types.listOf types.path;
      default = [ ];
      description = "Local hosts files or domain lists to block.";
    };
    updateInterval = mkOption {
      type = types.str;
      default = "daily";
      description = "How often the lists are fetched again (a systemd calendar expression).";
    };
    upstreamDns = mkOption {
      type = types.listOf types.str;
      default = [
        "9.9.9.9@853#dns.quad9.net"
        "149.112.112.112@853#dns.quad9.net"
      ];
      description = "The resolvers unbound forwards to (`address@port#name` for DNS over TLS).";
    };
    upstreamTls = mkOption {
      type = types.bool;
      default = true;
      description = "Whether to reach the upstream resolvers over TLS.";
    };
    policy = {
      allowQuic = mkOption {
        type = types.bool;
        default = false;
        description = "Let QUIC (HTTP/3) through; its server names are not checked.";
      };
      allowDnsOverTls = mkOption {
        type = types.bool;
        default = false;
        description = "Let DNS over TLS and over QUIC through; those lookups are not checked.";
      };
      keepHttpsRecords = mkOption {
        type = types.bool;
        default = false;
        description = "Answer HTTPS and SVCB queries, which carry Encrypted ClientHello keys.";
      };
    };
  };

  config = mkIf cfg.enable {
    environment.systemPackages = [
      admin
      ctl
      pkgs.qrencode
    ];

    boot.kernel.sysctl = {
      "net.ipv4.ip_forward" = 1;
      "net.ipv6.conf.all.forwarding" = 1;
    };

    networking.firewall.allowedUDPPorts = [ cfg.port ];
    networking.firewall.trustedInterfaces = [ cfg.interface ];
    networking.nftables.enable = true;
    networking.nftables.tables.ultranet = {
      family = "inet";
      content = ''
        chain prerouting {
          type nat hook prerouting priority dstnat;
          # All DNS from clients goes to the resolver, wherever it was sent.
          iifname "${cfg.interface}" meta nfproto ipv4 meta l4proto { tcp, udp } th dport 53 dnat ip to ${addr4}
          iifname "${cfg.interface}" meta nfproto ipv6 meta l4proto { tcp, udp } th dport 53 dnat ip6 to ${addr6}
        }
        chain postrouting {
          type nat hook postrouting priority srcnat;
          iifname "${cfg.interface}" oifname != "${cfg.interface}" masquerade
        }
        chain forward {
          type filter hook forward priority filter;
          # Segments the internet sends back must fit the tunnel.
          iifname "${cfg.interface}" meta nfproto ipv4 tcp flags syn / syn,rst tcp option maxseg size > ${toString (cfg.mtu - 40)} tcp option maxseg size set ${toString (cfg.mtu - 40)}
          iifname "${cfg.interface}" meta nfproto ipv6 tcp flags syn / syn,rst tcp option maxseg size > ${toString (cfg.mtu - 60)} tcp option maxseg size set ${toString (cfg.mtu - 60)}
          # DNS over TLS and QUIC, in case the filter lets it through.
          ${lib.optionalString (!cfg.policy.allowDnsOverTls) ''
            iifname "${cfg.interface}" meta l4proto { tcp, udp } th dport 853 reject
          ''}
        }
      '';
    };

    services.unbound = {
      enable = true;
      resolveLocalQueries = false;
      settings = {
        server = {
          interface = [
            addr4
            addr6
          ];
          ip-freebind = true;
          access-control = [
            "${net4} allow"
            "${net6} allow"
          ];
          hide-identity = true;
          hide-version = true;
        };
        forward-zone = [
          {
            name = ".";
            forward-tls-upstream = cfg.upstreamTls;
            forward-addr = cfg.upstreamDns;
          }
        ];
      };
    };

    systemd.services.ultranet = {
      description = "ultranet ad-blocking VPN server";
      wantedBy = [ "multi-user.target" ];
      after = [ "network.target" ];
      path = [
        pkgs.iproute2
        admin
      ];
      preStart = ''
        set -eu
        mkdir -p ${state} /run/ultranet
        [ -e ${state}/server.key ] || ultranet-admin genkey --out ${state}/server.key > /dev/null
        [ -e ${state}/peers ] || echo "# Clients: managed with ultranet-ctl." > ${state}/peers
        [ -e ${state}/blocklist.bin ] || ${updateLists} || true
        [ -e ${state}/blocklist.bin ] || ultranet-admin compile-list --out ${state}/blocklist.bin
        umask 077
        {
          echo "[Interface]"
          echo "PrivateKey = $(cat ${state}/server.key)"
          echo "ListenPort = ${toString cfg.port}"
          echo "PeersFile = ${state}/peers"
        } > /run/ultranet/wg.conf
        # A persistent TUN device, so its addresses are set before the server
        # attaches to it.
        ip tuntap add dev ${cfg.interface} mode tun 2>/dev/null || true
        ip addr replace ${cfg.address4} dev ${cfg.interface}
        ip -6 addr replace ${cfg.address6} dev ${cfg.interface}
        ip link set ${cfg.interface} mtu ${toString cfg.mtu} up
      '';
      serviceConfig = {
        ExecStart = "${ultranet}/bin/ultranet --stats /run/ultranet/stats ${flags} ${cfg.interface} /run/ultranet/wg.conf ${state}/blocklist.bin";
        ExecReload = "${pkgs.coreutils}/bin/kill -HUP $MAINPID";
        Restart = "on-failure";
        RestartSec = 2;
        CapabilityBoundingSet = [
          "CAP_NET_ADMIN"
          "CAP_NET_RAW"
          "CAP_NET_BIND_SERVICE"
          "CAP_DAC_OVERRIDE"
        ];
        NoNewPrivileges = true;
        ProtectSystem = "strict";
        ProtectHome = true;
        PrivateTmp = true;
        ReadWritePaths = [
          state
          "/run/ultranet"
        ];
        StateDirectory = "ultranet";
        RuntimeDirectory = "ultranet";
        RuntimeDirectoryPreserve = true;
      };
    };

    systemd.services.ultranet-lists = {
      description = "Fetch and compile ultranet's blocklists";
      after = [ "network-online.target" ];
      wants = [ "network-online.target" ];
      serviceConfig = {
        Type = "oneshot";
        ExecStart = updateLists;
        ExecStartPost = "-${pkgs.systemd}/bin/systemctl reload ultranet.service";
      };
    };
    systemd.timers.ultranet-lists = {
      wantedBy = [ "timers.target" ];
      timerConfig = {
        OnCalendar = cfg.updateInterval;
        Persistent = true;
        RandomizedDelaySec = "1h";
      };
    };
  };
}
