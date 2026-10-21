import Wireguard.Funs
import Untrusted
import Wireguard.Specs.CookieReply
import Wireguard.Specs.Initiation

derive_decode_spec wireguard.message.Response
derive_encode_spec wireguard.message.Response
derive_roundtrip_spec wireguard.message.Response
