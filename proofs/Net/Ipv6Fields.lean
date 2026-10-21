/- Hand-written specs of the `Decode` impls of `net::ipv6` that are not
   derived (`Ipv6Addr` and `VersionClassFlow`), and of the length helper of
   `Ipv6Packet::validate`. -/
import Net.Funs
import Net.Lemmas
import Untrusted

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.ipv6

/-! ## Constants -/

@[simp, scalar_tac_simps] theorem HEADER_LEN_val : HEADER_LEN.val = 40 := by simp [HEADER_LEN]

/-! ## `Ipv6Addr` -/

/-- **Spec theorem for `<Ipv6Addr as Decode>::decode`**: a big-endian `u128`. -/
instance _root_.net.ipv6.Ipv6Addr.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs Ipv6Addr.Insts.UntrustedReaderDecode
      (fun l a k => k = 16 ∧ 16 ≤ l.length ∧ (a : U128).val = beNat (l.take 16))
      (fun l => l.length < 16) where
  spec r hinv := by
    simp only [Ipv6Addr.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU128_spec r hinv)
    rintro ⟨res, r'⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · obtain ⟨hle, hv, hin, hpos, hinv'⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok,
        WP.uncurry'_pair]
      exact ⟨hin, hinv', 16, ⟨rfl, hle, hv⟩, hpos⟩
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, by scalar_tac⟩
  disjoint _ _ _ hD hF := by have := hD.2.1; omega
  functional _ a _ a' _ hD hD' :=
    ⟨(UScalar.eq_equiv (a : U128) a').mpr (hD.2.2.trans hD'.2.2.symm), hD.1.trans hD'.1.symm⟩

/-! ## `VersionClassFlow` -/

/-- The traffic class and flow label of the first header word `w`. -/
def VersionClassFlow.OfWord (w : Nat) (v : VersionClassFlow) : Prop :=
  v.traffic_class.val = w / 1048576 % 256 ∧ v.flow_label.val = w % 1048576

/-- **Spec theorem for `<VersionClassFlow as Decode>::decode`**: a big-endian
    `u32` with version 6 in its top four bits, split into its fields. -/
instance _root_.net.ipv6.VersionClassFlow.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs VersionClassFlow.Insts.UntrustedReaderDecode
      (fun l v k => k = 4 ∧ 4 ≤ l.length ∧ beNat (l.take 4) / 268435456 = 6 ∧
        VersionClassFlow.OfWord (beNat (l.take 4)) v)
      (fun l => ¬ (4 ≤ l.length ∧ beNat (l.take 4) / 268435456 = 6)) where
  spec r hinv := by
    simp only [VersionClassFlow.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU32_spec r hinv)
    rintro ⟨res, r'⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · rename_i a
      obtain ⟨hle, hv, hin, hpos, hinv'⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step*
      have hi6 : i.val = 6 := by simpa using ‹¬(i != 6#u32) = true›
      refine ⟨hin, hinv', hle, by rw [← hv, ← i_post, hi6], ⟨?_, by rw [i4_post, hv]⟩, hpos⟩
      rw [i3_post, UScalar.cast_val_eq, i2_post, i1_post, hv]
      simp only [UScalarTy.U8_numBits_eq]
      omega
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, fun ⟨h, _⟩ => by scalar_tac⟩
  disjoint _ _ _ hD hF := hF ⟨hD.2.1, hD.2.2.1⟩
  functional _ v _ v' _ hD hD' := by
    obtain ⟨hk, -, -, ht, hf⟩ := hD
    obtain ⟨hk', -, -, ht', hf'⟩ := hD'
    refine ⟨?_, hk.trans hk'.symm⟩
    rcases v with ⟨t, f⟩
    rcases v' with ⟨t', f'⟩
    simp only at ht hf ht' hf'
    have : t = t' := (UScalar.eq_equiv _ _).mpr (ht.trans ht'.symm)
    have : f = f' := (UScalar.eq_equiv _ _).mpr (hf.trans hf'.symm)
    simp_all

/-! ## Lengths -/

/-- Where the payload of the IPv6 packet `l` ends: 40 plus the payload length
    in bytes 4 and 5. -/
def payloadEnd (l : List U8) : Nat := 40 + beNat ((l.drop 4).take 2)

/-- **Spec theorem for `net::ipv6::payload_end`**. -/
@[step]
theorem payload_end.spec (input : Slice U8) (h : 40 ≤ input.length) :
    payload_end input ⦃ (r : Usize) => r.val = payloadEnd input.val ⦄ := by
  unfold payload_end
  step*
  rw [r_post, i3_post, i2_post, i1_post, i5_post, payloadEnd,
    beNat_take2_drop _ 4 (by scalar_tac), ← i_post, ← i4_post]
  simp only [U8.cast_Usize_val_eq, HEADER_LEN_val]
  omega

/-! ## Encoding -/

section
open untrusted.writer

/-- **Spec theorem for `<Ipv6Addr as Encode>::encode`**: a big-endian `u128`. -/
instance _root_.net.ipv6.Ipv6Addr.Insts.UntrustedWriterEncode.encode.spec :
    EncodesAs Ipv6Addr.Insts.UntrustedWriterEncode (fun a => beBytes 16 (a : U128).val) where
  spec v w hinv := by
    simp only [Ipv6Addr.Insts.UntrustedWriterEncode.encode]
    apply WP.spec_bind (EncodesAs.spec (inst := bytes.BigEndianU128.Insts.UntrustedWriterEncode) v w hinv)
    rintro ⟨r, w1, b⟩ hw
    simp only [WP.uncurry'_pair, uncurry, WP.spec_ok] at hw ⊢
    exact hw.wrap

/-- `Ipv6Addr` round-trips every address. -/
instance _root_.net.ipv6.Ipv6Addr.roundtrip :
    RoundTrip Ipv6Addr.Insts.UntrustedWriterEncode Ipv6Addr.Insts.UntrustedReaderDecode
      (fun _ => True) where
  roundtrip a rest h :=
    FmtRT bytes.BigEndianU128.Insts.UntrustedWriterEncode
      bytes.BigEndianU128.Insts.UntrustedReaderDecode a rest h

/-- The word `<VersionClassFlow as Encode>` writes. -/
def VersionClassFlow.word (v : VersionClassFlow) : Nat :=
  1610612736 + v.traffic_class.val * 1048576 + v.flow_label.val % 1048576

/-- **Spec theorem for `<VersionClassFlow as Encode>::encode`**: version 6, the
    traffic class and the flow label's 20 bits, big-endian. -/
instance _root_.net.ipv6.VersionClassFlow.Insts.UntrustedWriterEncode.encode.spec :
    EncodesAs VersionClassFlow.Insts.UntrustedWriterEncode
      (fun v => beBytes 4 (VersionClassFlow.word v)) where
  spec v w hinv := by
    simp only [VersionClassFlow.Insts.UntrustedWriterEncode.encode]
    have ht := v.traffic_class.hBounds
    simp only [UScalarTy.U8_numBits_eq] at ht
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨word, hword⟩
    apply WP.spec_bind (EncodesAs.spec (inst := bytes.BigEndianU32.Insts.UntrustedWriterEncode) word w hinv)
    rintro ⟨r, w1, b⟩ hw
    simp only [WP.uncurry'_pair, uncurry, WP.spec_ok] at hw ⊢
    have : word.val = VersionClassFlow.word v := by
      simp only [VersionClassFlow.word]; scalar_tac
    rw [this] at hw
    exact hw.wrap

/-- `VersionClassFlow` round-trips the flow labels the decoder accepts: 20
    bits. -/
instance _root_.net.ipv6.VersionClassFlow.roundtrip :
    RoundTrip VersionClassFlow.Insts.UntrustedWriterEncode
      VersionClassFlow.Insts.UntrustedReaderDecode
      (fun v => v.flow_label.val < 1048576) where
  roundtrip v rest h := by
    have ht := v.traffic_class.hBounds
    simp only [UScalarTy.U8_numBits_eq] at ht
    have hb : beNat ((beBytes 4 (VersionClassFlow.word v) ++ rest).take 4) =
        VersionClassFlow.word v := by
      rw [List.take_left' (by simp), beNat_beBytes]; simp only [VersionClassFlow.word]; omega
    refine ⟨by simp, by simp, ?_, ?_, ?_⟩ <;> rw [hb] <;> simp only [VersionClassFlow.word] <;> omega

end

end net.ipv6
