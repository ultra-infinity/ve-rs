# NixOS VM test of the ultranet VPN: `client` connects with kernel WireGuard
# to `server` (the services.ultranet module), and browses `internet`
# (dnsmasq answering every name, TLS servers on 443 and 853, a UDP 443
# listener) through it. See nix/modules/ultranet/vm-test.nix.

import re

start_all()
for m in (client, server, internet):
    m.wait_for_unit("network.target")
internet.wait_for_unit("dnsmasq.service")
internet.succeed(
    "openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes"
    " -subj /CN=test -days 1 -keyout /tmp/key.pem -out /tmp/cert.pem"
)
for port in (443, 853):
    internet.succeed(
        f"systemd-run --unit=tls{port} openssl s_server -accept {port}"
        " -cert /tmp/cert.pem -key /tmp/key.pem -www"
    )
    internet.wait_for_open_port(port)
internet.succeed("systemd-run --unit=quic socat -u UDP-RECV:443 OPEN:/tmp/udp443,creat,append")
ip = internet.succeed("ip -4 -o addr show eth1 | awk '{print $4}' | cut -d/ -f1").strip()

server.wait_for_unit("ultranet.service")
server.wait_for_unit("unbound.service")
server.wait_until_succeeds("ip link show ultranet0")

# A client, added as an operator would.
conf = server.succeed("ultranet-ctl add alice")
print(conf)
assert "DNS = 10.77.0.1, fd77::1" in conf
client.succeed(f"mkdir -p /etc/wireguard && cat > /etc/wireguard/wg0.conf <<'EOF'\n{conf}EOF")
client.succeed("chmod 600 /etc/wireguard/wg0.conf && wg-quick up wg0")
client.wait_until_succeeds("ping -c 1 -W 1 10.77.0.1", timeout=30)
print(server.succeed("ultranet-ctl list"))


def dig(args):
    return client.succeed(f"dig +tries=1 +time=3 {args}")


# DNS: names resolve through the server; blocked ones do not exist.
out = dig("@10.77.0.1 example.org A")
assert "status: NOERROR" in out and ip in out, out
assert "status: NXDOMAIN" in dig("@10.77.0.1 ads.example A")
assert "status: NXDOMAIN" in dig("@10.77.0.1 cdn.tracker.io AAAA")
# Over IPv6 to the server too.
assert "status: NXDOMAIN" in dig("@fd77::1 ads.example A")
# A query to another resolver is filtered too, and what passes is answered
# by the server's resolver (the NAT redirects it).
assert "status: NXDOMAIN" in dig("@9.9.9.9 x.tracker.io A")
out = dig("@9.9.9.9 example.org A")
assert "status: NOERROR" in out and ip in out, out
# No HTTPS records, so no Encrypted ClientHello keys.
out = dig("@10.77.0.1 example.org HTTPS")
assert "status: NOERROR" in out and "ANSWER: 0" in out, out
# Firefox's DNS-over-HTTPS canary is blocked.
assert "status: NXDOMAIN" in dig("@10.77.0.1 use-application-dns.net A")

# TLS: a normal site works; a blocked one is reset at once.
def curl(name):
    return (
        "curl -sk --max-time 10 -o /dev/null -w '%{http_code}'"
        f" --resolve {name}:443:{ip} https://{name}/"
    )


assert client.succeed(curl("example.org")).strip() == "200"
status, _ = client.execute(curl("ads.example"))
assert status != 0, "the connection to ads.example went through"
status, out = client.execute(
    f"timeout 10 openssl s_client -connect {ip}:443 -servername metrics.tracker.io < /dev/null 2>&1"
)
print(out)
assert status != 0 and "CONNECTED" in out, "the handshake to metrics.tracker.io was not cut"

# QUIC is dropped; DNS over TLS is refused.
client.succeed(f"echo hello | socat - UDP4-SENDTO:{ip}:443")
status, _ = client.execute(f"timeout 10 openssl s_client -connect {ip}:853 < /dev/null")
assert status != 0, "DNS over TLS went through"
client.sleep(1)
assert internet.succeed("cat /tmp/udp443 2>/dev/null || true") == "", "QUIC went through"

# A new blocklist, compiled and reloaded while running.
server.succeed(
    "printf 'news.example\\n' > /tmp/more && ultranet-admin compile-list --list /tmp/more"
    " --out /var/lib/ultranet/blocklist.bin && systemctl reload ultranet"
)
client.wait_until_succeeds(
    "dig +tries=1 +time=3 @10.77.0.1 news.example | grep -q NXDOMAIN", timeout=20
)
assert "status: NOERROR" in dig("@10.77.0.1 ads.example A")

# A second client works alongside the first.
conf2 = server.succeed("ultranet-ctl add bob")
assert "Address = 10.77.0.3/32" in conf2
assert len(re.findall("# peer:", server.succeed("cat /var/lib/ultranet/peers"))) == 2

# Statistics are written every minute.
server.wait_until_succeeds("grep -q '^nxdomain=[1-9]' /run/ultranet/stats", timeout=90)
print(server.succeed("ultranet-ctl stats"))

# Removed, the client's tunnel stops at once.
server.succeed("ultranet-ctl remove alice")
client.wait_until_fails("ping -c 1 -W 1 10.77.0.1", timeout=20)
print(server.succeed("journalctl -u ultranet --no-pager | tail -20"))
