/- Hand-written spec of `<Icmpv4 as Validate<&[u8]>>::validate`. -/
import Net.Ipv4Top
import Net.Specs.IcmpHeader

open Aeneas Aeneas.Std Result untrusted untrusted.reader net.ipv4

namespace net.icmp

@[simp, scalar_tac_simps] theorem HEADER_LEN_val : HEADER_LEN.val = 8 := by simp [HEADER_LEN]

/-- `l` is a well-formed IPv4 packet carrying a whole ICMP message, which
    decodes to `m`: `l` is an IPv4 packet with protocol 1 that is not a
    fragment, its payload is at least 8 bytes long with a valid checksum, the
    first 8 decode as `m.header`, and `m.body` is the rest. -/
def Icmpv4.Spec (l : List U8) (m : Icmpv4) : Prop :=
  Ipv4Packet.Spec l m.ip ∧ (m.ip.header.protocol : U8).val = 1 ∧
    m.ip.header.fragment.more_fragments = false ∧ m.ip.header.fragment.offset.val = 0 ∧
    8 ≤ (payloadOf l).length ∧ inet.spec 0 (payloadOf l) = 0xFFFF ∧
    FmtD IcmpHeader.Insts.UntrustedReaderDecode ((payloadOf l).take 8) m.header 8 ∧
    (m.body : Slice U8).val = (payloadOf l).drop 8

/-- **Spec theorem for `<Icmpv4 as Validate<&[u8]>>::validate`**: accepts
    exactly the IPv4 packets carrying a well-formed ICMP message. -/
@[step]
theorem _root_.net.icmp.Icmpv4.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Icmpv4.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Icmpv4 ValidationError) =>
        match r with
        | .Ok m => Icmpv4.Spec input.val m
        | .Err _ => ∀ m, ¬ Icmpv4.Spec input.val m ⦄ := by
  unfold Icmpv4.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  simp only [Untrusted.validate_eq]
  step as ⟨ u0, hu0 ⟩
  step as ⟨ res, hres ⟩
  rw [hu0] at hres
  cases res
  · rename_i ip
    have hip : Ipv4Packet.Spec input.val ip := hres
    obtain ⟨h20, hhl, hhltl, htl, -⟩ := hres
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step*
    · rintro m ⟨hip', hp, -⟩
      rw [hip'.header_eq hip] at hp
      have := ‹(ip.header.protocol != PROTO_ICMP) = true›
      simp_all [PROTO_ICMP]
    · rintro m ⟨hip', -, hm, -⟩
      rw [hip'.header_eq hip] at hm
      simp_all
    · rintro m ⟨hip', -, -, ho, -⟩
      rw [hip'.header_eq hip] at ho
      have := ‹(ip.header.fragment.offset != 0#u16) = true›
      simp_all
    · have hd : message.val = payloadOf input.val := by
        rw [message_post, header_len_post, header_len_post1, slice_eq_payloadOf]
      rintro m ⟨-, -, -, -, h8, -⟩
      rw [← hd] at h8
      have := ‹message.len < HEADER_LEN›
      scalar_tac
    · have hd : message.val = payloadOf input.val := by
        rw [message_post, header_len_post, header_len_post1, slice_eq_payloadOf]
      rintro m ⟨-, -, -, -, -, hc, -⟩
      have := ‹(i2 != inet.VALID) = true›
      apply (bne_iff_ne.mp this)
      apply (UScalar.eq_equiv _ _).mpr
      rw [i2_post, hd, hc]; simp
    · have hd : message.val = payloadOf input.val := by
        rw [message_post, header_len_post, header_len_post1, slice_eq_payloadOf]
      have h8 : 8 ≤ (payloadOf input.val).length := by
        have := ‹¬message.len < HEADER_LEN›
        rw [← hd]; scalar_tac
      have hc : inet.spec 0 (payloadOf input.val) = 0xFFFF := by
        have := ‹¬(i2 != inet.VALID) = true›
        simp only [bne_iff_ne, ne_eq, not_not] at this
        rw [← hd, ← i2_post, this]; simp
      have hu : (u1 : Slice U8).val = (payloadOf input.val).take 8 := by
        rw [u1_post, s_post, hd]; simp [List.slice]
      have hlen : ((payloadOf input.val).take 8).length = 8 := by
        simp only [List.length_take]; omega
      apply WP.spec_bind
        (UntrustedShared0SliceU8.read_all.spec_of IcmpHeader.Insts.UntrustedReaderDecode u1)
      rintro (h | e) hres
      · simp only [hu, hlen] at hres
        simp only [bind_ok]
        step*
        refine ⟨hip, ?_, ?_, ?_, h8, hc, hres, ?_⟩
        · have := ‹¬(ip.header.protocol != PROTO_ICMP) = true›
          simp_all [PROTO_ICMP]
        · simpa using ‹¬ip.header.fragment.more_fragments = true›
        · have := ‹¬(ip.header.fragment.offset != 0#u16) = true›
          simp_all
        · simp [u2_post, s1_post, hd]
      · simp only [hu, hlen] at hres
        simp only [bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
        rintro m ⟨-, -, -, -, -, -, hD, -⟩
        exact hres m.header hD
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    rintro m ⟨hip, -⟩
    exact hres m.ip hip

end net.icmp
