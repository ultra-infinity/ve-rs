# NixOS VM test of `wg-userspace`, the no_std runner whose UDP goes through
# the verified `net` encoders and decoders (see `wg-vm-test` in flake.nix).
#
# 1. Interop: `a` runs wg-userspace, `b` the Linux kernel's WireGuard. Each
#    side initiates a handshake; IPv4 and IPv6 pings and TCP transfers of a
#    few MB go both ways; a packet from an address `a` does not allow for `b`
#    is dropped. The WireGuard datagrams `b` receives are captured and run
#    through the verified `net` decoders (`net-pcap`).
# 2. Own-to-own: `b` switches to wg-userspace too, and the same traffic flows.

import shlex

start_all()
for m in (a, b):
    m.wait_for_unit("network.target")
    m.wait_until_succeeds("ip -4 addr show dev eth1 | grep -q 'inet '")
    m.execute("ethtool -K eth1 tx off rx off sg off tso off gso off gro off")


def lan_ip(m):
    return m.succeed("ip -4 -o addr show dev eth1 | awk '{print $4}' | cut -d/ -f1").strip()


ip = {a: lan_ip(a), b: lan_ip(b)}
tunnel4 = {a: "10.10.0.1", b: "10.10.0.2"}
tunnel6 = {a: "fd10::1", b: "fd10::2"}
other = {a: b, b: a}

# Keys from `wg`; our own derivation of the public key must agree with it.
priv, pub = {}, {}
for m in (a, b):
    priv[m] = m.succeed("wg genkey").strip()
    pub[m] = m.succeed(f"echo {priv[m]} | wg pubkey").strip()
    ours = m.succeed(f"echo {priv[m]} | wg-userspace pubkey").strip()
    assert ours == pub[m], f"public key {ours} differs from wg's {pub[m]}"
psk = a.succeed("wg genpsk").strip()


def write(m, path, text):
    m.succeed(f"printf '%s' {shlex.quote(text)} > {path}")


def addresses(m):
    m.succeed(
        "ip link set wg0 mtu 1420 up",
        f"ip addr add {tunnel4[m]}/24 dev wg0",
        f"ip -6 addr add {tunnel6[m]}/64 dev wg0 nodad",
    )


def start_userspace(m):
    o = other[m]
    write(m, "/etc/wg0.conf", f"""[Interface]
PrivateKey = {priv[m]}
ListenPort = 51820

[Peer]
PublicKey = {pub[o]}
PresharedKey = {psk}
Endpoint = {ip[o]}:51820
AllowedIPs = {tunnel4[o]}/32, {tunnel6[o]}/128
""")
    m.succeed("systemd-run --unit=wg-userspace wg-userspace wg0 /etc/wg0.conf")
    m.wait_until_succeeds("ip link show wg0")
    addresses(m)


def stop_userspace(m):
    m.succeed("systemctl stop wg-userspace")
    m.wait_until_fails("ip link show wg0")


def start_kernel(m):
    o = other[m]
    write(m, "/etc/wg.key", priv[m])
    write(m, "/etc/wg.psk", psk)
    m.succeed(
        "ip link add wg0 type wireguard",
        f"wg set wg0 listen-port 51820 private-key /etc/wg.key "
        f"peer {pub[o]} preshared-key /etc/wg.psk endpoint {ip[o]}:51820 "
        f"allowed-ips {tunnel4[o]}/32,{tunnel6[o]}/128",
    )
    addresses(m)


def traffic(x):
    """Pings and TCP transfers between `x`, which starts, and its peer."""
    y = other[x]
    x.succeed(f"ping -c 3 -W 5 {tunnel4[y]}")
    x.succeed(f"ping -6 -c 3 -W 5 {tunnel6[y]}")
    y.succeed(f"ping -c 3 -W 5 {tunnel4[x]}")
    y.succeed(f"ping -6 -c 3 -W 5 {tunnel6[x]}")
    for (src, dst, addr) in [(x, y, tunnel4[y]), (y, x, f"[{tunnel6[x]}]")]:
        src.succeed("head -c 4000000 /dev/urandom > /tmp/send")
        dst.succeed("rm -f /tmp/recv; systemd-run --unit=recv socat -u TCP6-LISTEN:7000,ipv6only=0 OPEN:/tmp/recv,creat")
        dst.wait_until_succeeds("ss -ltn | grep -q :7000")
        src.succeed(f"timeout 60 socat -u OPEN:/tmp/send TCP:{addr}:7000")
        dst.wait_until_fails("systemctl is-active recv")
        sent = src.succeed("sha256sum < /tmp/send")
        got = dst.succeed("sha256sum < /tmp/recv")
        assert sent == got, f"transfer {src.name} -> {dst.name} corrupted"


# --- 1. Interop with the kernel ---------------------------------------------

b.succeed("systemd-run --unit=capture tcpdump -i eth1 -Q in -U -w /tmp/in.pcap udp port 51820")
b.wait_until_succeeds("test -s /tmp/in.pcap")

start_userspace(a)
start_kernel(b)

# The kernel initiates.
traffic(b)
b.succeed("wg show wg0 latest-handshakes | awk '{exit !($2 > 0)}'")

# A source address `a` does not allow for `b` is dropped.
b.succeed("ip addr add 10.10.9.9/32 dev wg0")
b.fail(f"ping -c 2 -W 2 -I 10.10.9.9 {tunnel4[a]}")

# A fresh wg-userspace initiates.
stop_userspace(a)
start_userspace(a)
first = b.succeed("wg show wg0 latest-handshakes | awk '{print $2}'").strip()
b.sleep(1)
traffic(a)
second = b.succeed("wg show wg0 latest-handshakes | awk '{print $2}'").strip()
assert int(second) > int(first), "no new handshake when wg-userspace initiated"

b.succeed("systemctl stop capture")
status, out = b.execute("net-pcap /tmp/in.pcap")
print(out)
assert status == 0, "some captured frames were rejected (see above)"
assert "accepted  ipv4/udp " in out, "no WireGuard datagrams were accepted"

# --- 2. Own to own ------------------------------------------------------------

b.succeed("ip link del wg0")
start_userspace(b)
traffic(b)
