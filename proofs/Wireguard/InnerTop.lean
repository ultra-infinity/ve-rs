/- Specs of `wireguard::inner`: the IP packets carried inside the tunnel,
   decoded with the verified `net` decoders. -/
import Net.Ipv4Top
import Wireguard.Funs

open Aeneas Aeneas.Std Result untrusted

namespace wireguard.inner

/-- **Spec theorem for `wireguard::inner::ipv4_source`**: the source address
    of the IPv4 packet `packet` decodes to, or none if it is not a
    well-formed IPv4 packet. -/
@[step]
theorem ipv4_source.spec (packet : Slice U8) :
    ipv4_source packet ⦃ (r : Option U32) =>
      match r with
      | some a => ∃ p, net.ipv4.Ipv4Packet.Spec packet.val p ∧ a = (p.header.src : U32)
      | none => ∀ p, ¬ net.ipv4.Ipv4Packet.Spec packet.val p ⦄ := by
  unfold ipv4_source
  simp only [Untrusted.validate_eq]
  step as ⟨ u, hu ⟩
  step as ⟨ res, hres ⟩
  rw [hu] at hres
  cases res
  · rename_i p
    simp only [WP.spec_ok]
    exact ⟨p, hres, rfl⟩
  · simpa using hres

end wireguard.inner
