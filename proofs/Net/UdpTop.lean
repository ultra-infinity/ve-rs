/- Hand-written spec of `<Ipv4Udp as Validate<&[u8]>>::validate`. -/
import Net.Ipv4Top
import Net.Specs.UdpHeader

open Aeneas Aeneas.Std Result untrusted untrusted.reader net.ipv4

namespace net.udp

@[simp, scalar_tac_simps] theorem HEADER_LEN_val : HEADER_LEN.val = 8 := by simp [HEADER_LEN]

/-- The IPv4 pseudo-header of the UDP datagram `d` carried by the IPv4 packet
    `l`: the source and destination addresses, a zero byte, the protocol 17,
    and the UDP length (bytes 4 and 5 of `d`). -/
def ipv4Pseudo (l d : List U8) : List U8 := (l.drop 12).take 8 ++ [0#u8, 17#u8] ++ (d.drop 4).take 2

/-- The checksum over the pseudo-header and the datagram, as
    `Ipv4Udp::validate` computes it: piece by piece. -/
theorem sum_ipv4Pseudo (l d : List U8) (hl : 20 ≤ l.length) (hd : 6 ≤ d.length) :
    inet.spec 0 (ipv4Pseudo l d ++ d) =
      inet.spec (inet.spec (inet.spec (inet.spec 0 ((l.drop 12).take 8)) [0#u8, 17#u8])
        (d.slice 4 6)) d := by
  have h1 : ((l.drop 12).take 8).length = 8 := by simp; omega
  have h2 : ((d.drop 4).take 2).length = 2 := by simp; omega
  simp only [ipv4Pseudo, List.slice]
  rw [inet.spec_append _ _ _ (by simp only [List.length_append, h1, h2]; rfl),
    inet.spec_append _ _ _ (by simp only [List.length_append, h1]; rfl),
    inet.spec_append _ _ _ (by simp only [h1])]

/-- `l` is a well-formed IPv4 packet carrying a whole UDP datagram, which
    decodes to `u`: `l` is an IPv4 packet with protocol 17 that is not a
    fragment, its payload `d` is at least 8 bytes, the first 8 decode as
    `u.header`, whose length is that of `d`, the checksum is either absent (0)
    or valid over the pseudo-header and `d`, and `u.payload` is the rest. -/
def Ipv4Udp.Spec (l : List U8) (u : Ipv4Udp) : Prop :=
  Ipv4Packet.Spec l u.ip ∧ (u.ip.header.protocol : U8).val = 17 ∧
    u.ip.header.fragment.more_fragments = false ∧ u.ip.header.fragment.offset.val = 0 ∧
    8 ≤ (payloadOf l).length ∧
    FmtD UdpHeader.Insts.UntrustedReaderDecode ((payloadOf l).take 8) u.header 8 ∧
    (u.header.length : U16).val = (payloadOf l).length ∧
    ((u.header.checksum : U16).val = 0 ∨
      inet.spec 0 (ipv4Pseudo l (payloadOf l) ++ payloadOf l) = 0xFFFF) ∧
    (u.payload : Slice U8).val = (payloadOf l).drop 8

/-- **Spec theorem for `<Ipv4Udp as Validate<&[u8]>>::validate`**: accepts
    exactly the IPv4 packets carrying a well-formed UDP datagram. -/
@[step]
theorem _root_.net.udp.Ipv4Udp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Ipv4Udp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Ipv4Udp ValidationError) =>
        match r with
        | .Ok u => Ipv4Udp.Spec input.val u
        | .Err _ => ∀ u, ¬ Ipv4Udp.Spec input.val u ⦄ := by
  unfold Ipv4Udp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
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
    · rintro u ⟨hip', hp, -⟩
      rw [hip'.header_eq hip] at hp
      have := ‹(ip.header.protocol != PROTO_UDP) = true›
      simp_all [PROTO_UDP]
    · rintro u ⟨hip', -, hm, -⟩
      rw [hip'.header_eq hip] at hm
      simp_all
    · rintro u ⟨hip', -, -, ho, -⟩
      rw [hip'.header_eq hip] at ho
      have := ‹(ip.header.fragment.offset != 0#u16) = true›
      simp_all
    · have hd : datagram.val = payloadOf input.val := by
        rw [datagram_post, header_len_post, header_len_post1, slice_eq_payloadOf]
      rintro u ⟨-, -, -, -, h8, -⟩
      rw [← hd] at h8
      have := ‹datagram.len < HEADER_LEN›
      scalar_tac
    · have hd : datagram.val = payloadOf input.val := by
        rw [datagram_post, header_len_post, header_len_post1, slice_eq_payloadOf]
      have h8 : 8 ≤ (payloadOf input.val).length := by
        have := ‹¬datagram.len < HEADER_LEN›
        rw [← hd]; scalar_tac
      have hu : (u1 : Slice U8).val = (payloadOf input.val).take 8 := by
        rw [u1_post, s_post, hd]; simp [List.slice]
      have hlen : ((payloadOf input.val).take 8).length = 8 := by
        simp only [List.length_take]; omega
      apply WP.spec_bind
        (UntrustedShared0SliceU8.read_all.spec_of UdpHeader.Insts.UntrustedReaderDecode u1)
      rintro (h | e) hres
      · simp only [hu, hlen] at hres
        simp only [bind_ok]
        step*
        · rintro u ⟨-, -, -, -, -, hD, hl, -⟩
          obtain ⟨rfl, -⟩ := (FmtLaws UdpHeader.Insts.UntrustedReaderDecode).functional _ _ _ _ _ hD hres
          have := ‹(i3 != datagram.len) = true›
          simp only [bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, i3_post, U16.cast_Usize_val_eq,
            Slice.len_val, hl, ← hd] at this
          exact this trivial
        · rintro u ⟨-, -, -, -, -, hD, -, hc, -⟩
          obtain ⟨rfl, -⟩ := (FmtLaws UdpHeader.Insts.UntrustedReaderDecode).functional _ _ _ _ _ hD hres
          rcases hc with hc | hc
          · have := ‹(u.header.checksum != 0#u16) = true›
            simp_all
          · have := ‹(i6 != inet.VALID) = true›
            apply (bne_iff_ne.mp this)
            apply (UScalar.eq_equiv _ _).mpr
            have hs1 : s1.val = (input.val.drop 12).take 8 := by rw [s1_post]; rfl
            have hs2 : s2.val = [0#u8, 17#u8] := by simp [s2_post, Array.make, PROTO_UDP]
            have hsum : i6.val =
                inet.spec 0 (ipv4Pseudo input.val (payloadOf input.val) ++ payloadOf input.val) := by
              rw [sum_ipv4Pseudo input.val (payloadOf input.val) h20 (by omega), i6_post, acc2_post,
                acc1_post, acc_post, hs1, hs2, s3_post, hd]
            rw [hsum, hc]; simp
        · refine ⟨hip, ?_, ?_, ?_, h8, hres, ?_, Or.inr ?_, ?_⟩
          · have := ‹¬(ip.header.protocol != PROTO_UDP) = true›
            simp_all [PROTO_UDP]
          · simpa using ‹¬ip.header.fragment.more_fragments = true›
          · have := ‹¬(ip.header.fragment.offset != 0#u16) = true›
            simp_all
          · have := ‹¬(i3 != datagram.len) = true›
            simp only [bne_iff_ne, ne_eq, not_not, i3_post] at this
            have := congrArg UScalar.val this
            simp only [U16.cast_Usize_val_eq, Slice.len_val] at this
            simpa [← hd] using this
          · have := ‹¬(i6 != inet.VALID) = true›
            simp only [bne_iff_ne, ne_eq, not_not] at this
            have hs1 : s1.val = (input.val.drop 12).take 8 := by rw [s1_post]; rfl
            have hs2 : s2.val = [0#u8, 17#u8] := by simp [s2_post, Array.make, PROTO_UDP]
            have hsum : i6.val =
                inet.spec 0 (ipv4Pseudo input.val (payloadOf input.val) ++ payloadOf input.val) := by
              rw [sum_ipv4Pseudo input.val (payloadOf input.val) h20 (by omega), i6_post, acc2_post,
                acc1_post, acc_post, hs1, hs2, s3_post, hd]
            rw [← hsum, this]; simp
          · simp [u2_post, s4_post, hd]
        · refine ⟨hip, ?_, ?_, ?_, h8, hres, ?_, Or.inl ?_, ?_⟩
          · have := ‹¬(ip.header.protocol != PROTO_UDP) = true›
            simp_all [PROTO_UDP]
          · simpa using ‹¬ip.header.fragment.more_fragments = true›
          · have := ‹¬(ip.header.fragment.offset != 0#u16) = true›
            simp_all
          · have := ‹¬(i3 != datagram.len) = true›
            simp only [bne_iff_ne, ne_eq, not_not, i3_post] at this
            have := congrArg UScalar.val this
            simp only [U16.cast_Usize_val_eq, Slice.len_val] at this
            simpa [← hd] using this
          · have := ‹¬(h.checksum != 0#u16) = true›
            simp_all
          · simp [u2_post, s4_post, hd]
      · simp only [hu, hlen] at hres
        simp only [bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
        rintro u ⟨-, -, -, -, -, hD, -⟩
        exact hres u.header hD
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    rintro u ⟨hip, -⟩
    exact hres u.ip hip

end net.udp
