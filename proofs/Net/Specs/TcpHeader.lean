import Net.Funs
import Untrusted
import Net.Manual
import Net.Specs.ArpPacket
import Net.Specs.EthernetHeader
import Net.Specs.IcmpHeader
import Net.Specs.Ipv4Header
import Net.Specs.Ipv6Header

derive_decode_spec net.tcp.TcpHeader
derive_encode_spec net.tcp.TcpHeader
derive_roundtrip_spec net.tcp.TcpHeader
