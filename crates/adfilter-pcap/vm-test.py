# NixOS VM test: the client looks up and connects to listed (ad) domains and
# a normal one, over IPv4 and IPv6; the server (dnsmasq and an `openssl
# s_server`) captures what it receives and runs it through `adfilter-pcap`.
# See `packages.adfilter-vm-test` in flake.nix.

start_all()
for m in (client, server):
    m.wait_for_unit("network.target")
    m.wait_until_succeeds("ip -6 addr show dev eth1 | grep -q 2001:db8")
    # No offloads: segments go on the wire as the stack made them.
    m.execute("ethtool -K eth1 tx off rx off sg off tso off gso off gro off")
    m.wait_until_fails("ip -6 addr show dev eth1 tentative | grep -q .")

server.wait_for_unit("dnsmasq.service")
server.succeed(
    "openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes"
    " -subj /CN=test -days 1 -keyout /tmp/key.pem -out /tmp/cert.pem"
)
server.succeed(
    "systemd-run --unit=tls openssl s_server -accept 443 -cert /tmp/cert.pem"
    " -key /tmp/key.pem -www"
)
server.wait_for_open_port(443)

server.succeed("systemd-run --unit=capture tcpdump -i eth1 -Q in -U -w /tmp/in.pcap")
server.wait_until_succeeds("test -s /tmp/in.pcap")

dig = "dig @server +tries=1 +time=2"
client.succeed(f"{dig} -4 ads.example A")
client.succeed(f"{dig} -6 Cdn.Tracker.io AAAA")
client.succeed(f"{dig} -4 example.org A")
for name in ["metrics.tracker.io", "example.org"]:
    client.succeed(
        f"timeout 10 openssl s_client -connect server:443 -servername {name} < /dev/null"
    )
server.sleep(1)
server.succeed("systemctl stop capture")
server.copy_from_machine("/tmp/in.pcap")

server.succeed("printf '# ads\\n0.0.0.0 ads.example\\n0.0.0.0 tracker.io\\n' > /tmp/hosts")
status, out = server.execute(
    "adfilter-pcap --list /tmp/hosts /tmp/in.pcap --out /tmp/kept.pcap"
)
print(out)
assert status == 0, "adfilter-pcap failed"
assert "dns  ads.example" in out and "answered NXDOMAIN" in out, "ads.example not answered"
assert "dns  cdn.tracker.io" in out, "cdn.tracker.io not answered"
assert "tls  metrics.tracker.io" in out, "the ClientHello to metrics.tracker.io was not dropped"
assert "example.org" not in out, "example.org was blocked"

# The answers written out are NXDOMAIN replies from the server's port 53, and
# the blocked connection's ClientHello is gone.
replies = server.succeed("tcpdump -n -r /tmp/kept.pcap udp src port 53")
print(replies)
assert replies.count("NXDomain") == 2, "expected two NXDOMAIN replies"
kept = server.succeed("adfilter-pcap --list /tmp/hosts /tmp/kept.pcap")
print(kept)
assert " 0 dropped" in kept, "blocked traffic was kept"
