import DeriveDemo.Funs
import Untrusted
import DeriveDemo.Specs.Header
import DeriveDemo.Specs.Keyed
import DeriveDemo.Specs.Marker

derive_decode_spec derive_demo.Packet
derive_encode_spec derive_demo.Packet
derive_roundtrip_spec derive_demo.Packet
