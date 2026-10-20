# NixOS VM test: the client sends ARP, ICMP and UDP over IPv4 and IPv6 to the
# server, which captures the frames it receives and runs them through the
# verified `net` decoders (`net-pcap`). See `packages.net-vm-test` in
# flake.nix.

start_all()
for m in (client, server):
    m.wait_for_unit("network.target")
    m.wait_until_succeeds("ip -6 addr show dev eth1 | grep -q 2001:db8")
    # No checksum or segmentation offloads: frames go on the wire complete.
    m.execute("ethtool -K eth1 tx off rx off sg off tso off gso off gro off")
    # Wait for IPv6 duplicate address detection to finish.
    m.wait_until_fails("ip -6 addr show dev eth1 tentative | grep -q .")

# Capture only what the server receives: that is what was on the wire. Linux
# captures of outgoing frames are taken before the NIC pads them.
server.succeed("systemd-run --unit=capture tcpdump -i eth1 -Q in -U -w /tmp/in.pcap")
server.wait_until_succeeds("test -s /tmp/in.pcap")

# Start from an empty neighbour cache, so that ARP and NDP go on the wire.
client.succeed("ip neigh flush dev eth1")
client.succeed("ping -4 -c 3 server")
client.succeed("ping -6 -c 3 server")
# Short datagrams (padded by the link layer) and long ones.
client.succeed("echo hello | socat - UDP4-SENDTO:server:9999")
client.succeed("echo hello6 | socat - UDP6-SENDTO:server:9999")
client.succeed("head -c 1400 /dev/urandom | socat - UDP4-SENDTO:server:9999")
client.succeed("head -c 1400 /dev/urandom | socat - UDP6-SENDTO:server:9999")
server.sleep(1)
server.succeed("systemctl stop capture")
server.copy_from_machine("/tmp/in.pcap")

status, out = server.execute("net-pcap /tmp/in.pcap")
print(out)
assert status == 0, "some frames were rejected (see above)"
for layer in ["arp", "ipv4/icmp", "ipv4/udp", "ipv6/icmp", "ipv6/udp"]:
    assert f"accepted  {layer} " in out, f"no {layer} frames were accepted"
