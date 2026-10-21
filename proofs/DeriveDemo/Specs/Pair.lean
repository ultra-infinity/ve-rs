import DeriveDemo.Funs
import Untrusted
import DeriveDemo.Specs.Header
import DeriveDemo.Specs.Keyed
import DeriveDemo.Specs.Marker
import DeriveDemo.Specs.Packet

derive_decode_spec derive_demo.Pair
derive_encode_spec derive_demo.Pair
derive_roundtrip_spec derive_demo.Pair
