/- Hand-written spec of `<Arp as Validate<&[u8]>>::validate`. -/
import Net.Manual
import Net.Specs.ArpPacket

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.arp

/-- `l` is a well-formed Ethernet/IPv4 ARP packet, possibly followed by
    link-layer padding, that decodes to `a`: its first 28 bytes decode as
    `a.packet`, and `a.padding` is the rest. -/
def Arp.Spec (l : List U8) (a : Arp) : Prop :=
  28 ≤ l.length ∧ FmtD ArpPacket.Insts.UntrustedReaderDecode (l.take 28) a.packet 28 ∧
    (a.padding : Slice U8).val = l.drop 28

/-- **Spec theorem for `<Arp as Validate<&[u8]>>::validate`**: accepts exactly
    the well-formed ARP packets, and returns their decoding. -/
@[step]
theorem _root_.net.arp.Arp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Arp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Arp ValidationError) =>
        match r with
        | .Ok a => Arp.Spec input.val a
        | .Err _ => ∀ a, ¬ Arp.Spec input.val a ⦄ := by
  unfold Arp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  dsimp only
  split
  · simp only [WP.spec_ok]
    rintro a ⟨h28, -⟩
    scalar_tac
  · step*
    have hu : (u : Slice U8).val = input.val.take 28 := by
      rw [u_post, s_post]; simp [List.slice]
    have hlen : (input.val.take 28).length = 28 := by
      simp only [List.length_take]; scalar_tac
    apply WP.spec_bind
      (UntrustedShared0SliceU8.read_all.spec_of ArpPacket.Insts.UntrustedReaderDecode u)
    rintro (p | e) hres
    · simp only [hu, hlen] at hres
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step*
      exact ⟨by scalar_tac, hres, by simp [u1_post, s1_post]⟩
    · simp only [hu, hlen] at hres
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      rintro a ⟨-, hD, -⟩
      exact hres a.packet hD

end net.arp
