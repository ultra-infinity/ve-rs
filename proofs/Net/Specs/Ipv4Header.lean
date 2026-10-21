import Net.Funs
import Untrusted
import Net.Manual
import Net.Specs.ArpPacket
import Net.Specs.EthernetHeader
import Net.Specs.IcmpHeader

derive_decode_spec net.ipv4.Ipv4Header
derive_encode_spec net.ipv4.Ipv4Header
derive_roundtrip_spec net.ipv4.Ipv4Header
