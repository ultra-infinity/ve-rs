/- Hand-written specs of the `Decode` impls of `net::ipv4` that are not
   derived (`Ipv4Addr`, `VersionIhl` and `Fragment`), and of the length helper
   of `Ipv4Packet::validate`. -/
import Net.Funs
import Net.Lemmas
import Untrusted

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.ipv4

/-! ## Constants -/

@[simp, scalar_tac_simps] theorem MIN_HEADER_LEN_val : MIN_HEADER_LEN.val = 20 := by
  simp [MIN_HEADER_LEN]

/-! ## `Ipv4Addr` -/

/-- **Spec theorem for `<Ipv4Addr as Decode>::decode`**: a big-endian `u32`. -/
instance _root_.net.ipv4.Ipv4Addr.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs Ipv4Addr.Insts.UntrustedReaderDecode
      (fun l a k => k = 4 ∧ 4 ≤ l.length ∧ (a : U32).val = beNat (l.take 4))
      (fun l => l.length < 4) where
  spec r hinv := by
    simp only [Ipv4Addr.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU32_spec r hinv)
    rintro ⟨res, r'⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · obtain ⟨hle, hv, hin, hpos, hinv'⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok,
        WP.uncurry'_pair]
      exact ⟨hin, hinv', 4, ⟨rfl, hle, hv⟩, hpos⟩
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, by scalar_tac⟩
  disjoint _ _ _ hD hF := by have := hD.2.1; omega
  functional _ a _ a' _ hD hD' :=
    ⟨(UScalar.eq_equiv (a : U32) a').mpr (hD.2.2.trans hD'.2.2.symm), hD.1.trans hD'.1.symm⟩

/-! ## `VersionIhl` -/

/-- The first header byte `b` says version 4 and an IHL of at least 5. -/
def VersionIhl.Valid (b : Nat) : Prop := b / 16 = 4 ∧ 5 ≤ b % 16

/-- **Spec theorem for `<VersionIhl as Decode>::decode`**: one byte with
    version 4 and an IHL of at least 5; the IHL is its low nibble. -/
instance _root_.net.ipv4.VersionIhl.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs VersionIhl.Insts.UntrustedReaderDecode
      (fun l v k => k = 1 ∧ 1 ≤ l.length ∧ VersionIhl.Valid (beNat (l.take 1)) ∧
        v.ihl.val = beNat (l.take 1) % 16)
      (fun l => ¬ (1 ≤ l.length ∧ VersionIhl.Valid (beNat (l.take 1)))) where
  spec r hinv := by
    simp only [VersionIhl.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU8_spec r hinv)
    rintro ⟨res, r'⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · rename_i b
      obtain ⟨hle, hv, hin, hpos, hinv'⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step*
      · rename_i hne
        refine ⟨hin, hinv', ?_⟩
        simp only [VersionIhl.Valid]
        rintro ⟨-, hv4, -⟩
        have : i = 4#u8 := (UScalar.eq_equiv _ _).mpr (by rw [i_post, hv]; simpa using hv4)
        simp [this] at hne
      · refine ⟨hin, hinv', ?_⟩
        simp only [VersionIhl.Valid]
        rintro ⟨-, -, h5⟩
        scalar_tac
      · rename_i hne _
        have hi4 : i.val = 4 := by simpa using hne
        refine ⟨hin, hinv', hle, ?_, by rw [ihl_post, hv], hpos⟩
        simp only [VersionIhl.Valid]
        constructor <;> scalar_tac
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, fun ⟨h, _⟩ => by scalar_tac⟩
  disjoint _ _ _ hD hF := hF ⟨hD.2.1, hD.2.2.1⟩
  functional _ v _ v' _ hD hD' := by
    obtain ⟨hk, -, -, hi⟩ := hD
    obtain ⟨hk', -, -, hi'⟩ := hD'
    refine ⟨?_, hk.trans hk'.symm⟩
    rcases v with ⟨i⟩
    rcases v' with ⟨i'⟩
    simp only at hi hi'
    have : i = i' := (UScalar.eq_equiv _ _).mpr (hi.trans hi'.symm)
    rw [this]

/-! ## `Fragment` -/

/-- The flags and fragment offset of the word `t`. -/
def Fragment.OfWord (t : Nat) (f : Fragment) : Prop :=
  f.dont_fragment = decide (t / 16384 = 1) ∧ f.more_fragments = decide (t / 8192 % 2 = 1) ∧
    f.offset.val = t % 8192

/-- **Spec theorem for `<Fragment as Decode>::decode`**: a big-endian `u16`
    whose reserved top bit is clear, split into its fields. -/
instance _root_.net.ipv4.Fragment.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs Fragment.Insts.UntrustedReaderDecode
      (fun l f k => k = 2 ∧ 2 ≤ l.length ∧ beNat (l.take 2) < 32768 ∧
        Fragment.OfWord (beNat (l.take 2)) f)
      (fun l => ¬ (2 ≤ l.length ∧ beNat (l.take 2) < 32768)) where
  spec r hinv := by
    simp only [Fragment.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU16_spec r hinv)
    rintro ⟨res, r'⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · rename_i a
      obtain ⟨hle, hv, hin, hpos, hinv'⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step*
      have := ‹¬a ≥ 32768#u16›
      refine ⟨hin, hinv', hle, by scalar_tac, ?_, hpos⟩
      simp only [Fragment.OfWord]
      refine ⟨?_, ?_, by rw [i3_post, hv]⟩
      · simp only [decide_eq_decide, UScalar.eq_equiv, i_post, hv]; simp
      · simp only [decide_eq_decide, UScalar.eq_equiv, i2_post, i1_post, hv]; simp
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, fun ⟨h, _⟩ => by scalar_tac⟩
  disjoint _ _ _ hD hF := hF ⟨hD.2.1, hD.2.2.1⟩
  functional _ f _ f' _ hD hD' := by
    obtain ⟨hk, -, -, hd, hm, ho⟩ := hD
    obtain ⟨hk', -, -, hd', hm', ho'⟩ := hD'
    refine ⟨?_, hk.trans hk'.symm⟩
    rcases f with ⟨d, m, o⟩
    rcases f' with ⟨d', m', o'⟩
    simp only at hd hm ho hd' hm' ho'
    have : o = o' := (UScalar.eq_equiv _ _).mpr (ho.trans ho'.symm)
    simp_all

/-! ## Lengths -/

/-- The header length of the IPv4 packet `l`: four times its IHL. -/
def headerLen (l : List U8) : Nat := 4 * (beNat (l.take 1) % 16)

/-- The total length of the IPv4 packet `l`, from bytes 2 and 3. -/
def totalLen (l : List U8) : Nat := beNat ((l.drop 2).take 2)

/-- **Spec theorem for `net::ipv4::lengths`**: the header and total lengths. -/
@[step]
theorem lengths.spec (input : Slice U8) (h : 20 ≤ input.length) :
    lengths input ⦃ (hl : Usize) (tl : Usize) =>
      hl.val = headerLen input.val ∧ tl.val = totalLen input.val ⦄ := by
  unfold lengths
  step*
  refine ⟨?_, ?_⟩
  · rw [header_len_post, i2_post, i1_post, headerLen, beNat_take1 _ (by scalar_tac), ← i_post]
    simp only [U8.cast_Usize_val_eq]
    omega
  · rw [total_len_post, i5_post, i4_post, i7_post, totalLen, beNat_take2_drop _ 2 (by scalar_tac),
      ← i3_post, ← i6_post]
    simp only [U8.cast_Usize_val_eq]

/-! ## Encoding -/

section
open untrusted.writer

/-- **Spec theorem for `<Ipv4Addr as Encode>::encode`**: a big-endian `u32`. -/
instance _root_.net.ipv4.Ipv4Addr.Insts.UntrustedWriterEncode.encode.spec :
    EncodesAs Ipv4Addr.Insts.UntrustedWriterEncode (fun a => beBytes 4 (a : U32).val) where
  spec v w hinv := by
    simp only [Ipv4Addr.Insts.UntrustedWriterEncode.encode]
    apply WP.spec_bind (EncodesAs.spec (inst := bytes.BigEndianU32.Insts.UntrustedWriterEncode) v w hinv)
    rintro ⟨r, w1, b⟩ hw
    simp only [WP.uncurry'_pair, uncurry, WP.spec_ok] at hw ⊢
    exact hw.wrap

/-- `Ipv4Addr` round-trips every address. -/
instance _root_.net.ipv4.Ipv4Addr.roundtrip :
    RoundTrip Ipv4Addr.Insts.UntrustedWriterEncode Ipv4Addr.Insts.UntrustedReaderDecode
      (fun _ => True) where
  roundtrip a rest h :=
    FmtRT bytes.BigEndianU32.Insts.UntrustedWriterEncode bytes.BigEndianU32.Insts.UntrustedReaderDecode
      a rest h

/-- **Spec theorem for `<VersionIhl as Encode>::encode`**: version 4, then the
    IHL's low four bits. -/
instance _root_.net.ipv4.VersionIhl.Insts.UntrustedWriterEncode.encode.spec :
    EncodesAs VersionIhl.Insts.UntrustedWriterEncode
      (fun v => beBytes 1 (64 + v.ihl.val % 16)) where
  spec v w hinv := by
    simp only [VersionIhl.Insts.UntrustedWriterEncode.encode]
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    apply WP.spec_bind (EncodesAs.spec (inst := bytes.BigEndianU8.Insts.UntrustedWriterEncode) i1 w hinv)
    rintro ⟨r, w1, b⟩ hw
    simp only [WP.uncurry'_pair, uncurry, WP.spec_ok] at hw ⊢
    rw [hi1, hi] at hw
    exact hw.wrap

/-- `VersionIhl` round-trips the header lengths the decoder accepts. -/
instance _root_.net.ipv4.VersionIhl.roundtrip :
    RoundTrip VersionIhl.Insts.UntrustedWriterEncode VersionIhl.Insts.UntrustedReaderDecode
      (fun v => 5 ≤ v.ihl.val ∧ v.ihl.val < 16) where
  roundtrip v rest h := by
    have hb : beNat ((beBytes 1 (64 + v.ihl.val % 16) ++ rest).take 1) = 64 + v.ihl.val := by
      rw [List.take_left' (by simp), beNat_beBytes]; omega
    refine ⟨by simp, by simp, ?_, ?_⟩ <;> simp only [hb, VersionIhl.Valid] <;> omega

/-- The word `<Fragment as Encode>` writes. -/
def Fragment.word (f : Fragment) : Nat :=
  f.offset.val % 8192 + (if f.dont_fragment then 16384 else 0) +
    (if f.more_fragments then 8192 else 0)

/-- **Spec theorem for `<Fragment as Encode>::encode`**: the flags and the
    offset's 13 bits, big-endian. -/
instance _root_.net.ipv4.Fragment.Insts.UntrustedWriterEncode.encode.spec :
    EncodesAs Fragment.Insts.UntrustedWriterEncode (fun f => beBytes 2 (Fragment.word f)) where
  spec v w hinv := by
    simp only [Fragment.Insts.UntrustedWriterEncode.encode]
    step as ⟨f, hf⟩
    have hf' : f.val < 8192 := by scalar_tac
    have fin : ∀ g : U16, g.val = Fragment.word v →
        (do
          let (r, w1, encode_back) ← bytes.BigEndianU16.Insts.UntrustedWriterEncode.encode g w
          ok (r, w1, fun w2 => { w with out := (encode_back w2).out })) ⦃ res w' back =>
            Writes w (beBytes 2 (Fragment.word v)) res w' back ⦄ := by
      intro g hg
      apply WP.spec_bind (EncodesAs.spec (inst := bytes.BigEndianU16.Insts.UntrustedWriterEncode) g w hinv)
      rintro ⟨r, w1, b⟩ hw
      simp only [WP.uncurry'_pair, uncurry, WP.spec_ok] at hw ⊢
      rw [hg] at hw
      exact hw.wrap
    rcases hd : v.dont_fragment <;> rcases hm : v.more_fragments <;>
      simp only [Bool.false_eq_true, if_false, if_true, bind_ok]
    · exact fin f (by simp [Fragment.word, hd, hm, hf])
    · step as ⟨f2, hf2⟩
      exact fin f2 (by simp [Fragment.word, hd, hm, hf2, hf])
    · step as ⟨f1, hf1⟩
      exact fin f1 (by simp [Fragment.word, hd, hm, hf1, hf])
    · step as ⟨f1, hf1⟩
      step as ⟨f2, hf2⟩
      exact fin f2 (by simp [Fragment.word, hd, hm, hf2, hf1, hf] <;> omega)

/-- `Fragment` round-trips the offsets the decoder accepts: 13 bits. -/
instance _root_.net.ipv4.Fragment.roundtrip :
    RoundTrip Fragment.Insts.UntrustedWriterEncode Fragment.Insts.UntrustedReaderDecode
      (fun f => f.offset.val < 8192) where
  roundtrip v rest h := by
    have hw : Fragment.word v < 32768 := by
      unfold Fragment.word; split <;> split <;> omega
    have hb : beNat ((beBytes 2 (Fragment.word v) ++ rest).take 2) = Fragment.word v := by
      rw [List.take_left' (by simp), beNat_beBytes]; omega
    refine ⟨by simp, by simp, by rw [hb]; exact hw, ?_⟩
    rw [hb]
    unfold Fragment.OfWord Fragment.word
    rcases v with ⟨df, mf, o⟩
    simp only at h ⊢
    cases df <;> cases mf <;> simp <;> omega

end

end net.ipv4
