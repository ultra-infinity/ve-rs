import DeriveDemo.Funs
import Untrusted
import DeriveDemo.Specs.Header
import DeriveDemo.Specs.Keyed
import DeriveDemo.Specs.Marker
import DeriveDemo.Specs.Packet
import DeriveDemo.Specs.Pair

derive_decode_spec derive_demo.Version
derive_encode_spec derive_demo.Version
derive_roundtrip_spec derive_demo.Version
