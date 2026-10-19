/- Hand-written specs of the `Decode` impls of `net::ethernet` that are not
   derived: `MacAddr`, `EtherType`, `VlanTag` and `Tagging`. -/
import Net.Funs
import Untrusted

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.ethernet

/-! ## Constants -/

@[simp, scalar_tac_simps] theorem HEADER_LEN_val : HEADER_LEN.val = 14 := by simp [HEADER_LEN]
@[simp, scalar_tac_simps] theorem MIN_PAYLOAD_val : MIN_PAYLOAD.val = 46 := by simp [MIN_PAYLOAD]
@[simp, scalar_tac_simps] theorem MAX_PAYLOAD_val : MAX_PAYLOAD.val = 1500 := by simp [MAX_PAYLOAD]
@[simp, scalar_tac_simps] theorem MIN_ETHER_TYPE_val : MIN_ETHER_TYPE.val = 1536 := by
  simp [MIN_ETHER_TYPE]
@[simp, scalar_tac_simps] theorem VLAN_TAG_LEN_val : VLAN_TAG_LEN.val = 4 := by simp [VLAN_TAG_LEN]
@[simp, scalar_tac_simps] theorem MIN_PAYLOAD_TAGGED_val : MIN_PAYLOAD_TAGGED.val = 42 := by
  simp [MIN_PAYLOAD_TAGGED]
@[simp, scalar_tac_simps] theorem TPID_8021Q_val : TPID_8021Q.val = 33024 := by simp [TPID_8021Q]
@[simp, scalar_tac_simps] theorem VID_RESERVED_val : VID_RESERVED.val = 4095 := by
  simp [VID_RESERVED]
@[simp, scalar_tac_simps] theorem FCS_LEN_val : FCS_LEN.val = 4 := by simp [FCS_LEN]

/-! ## `MacAddr` -/

/-- **Spec theorem for `<MacAddr as Decode>::decode`**: the next 6 bytes, as is. -/
instance _root_.net.ethernet.MacAddr.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs MacAddr.Insts.UntrustedReaderDecode
      (fun l m k => k = 6 ∧ 6 ≤ l.length ∧ (m : Array U8 6#usize).val = l.take 6)
      (fun l => l.length < 6) where
  spec r hinv := by
    simp only [MacAddr.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read_byte.spec_cons r)
    rintro ⟨res1, r1⟩ h1
    simp only [WP.uncurry'_pair, uncurry] at h1 ⊢
    cases res1
    · obtain ⟨hrest1, hin1, hpos1, hinv1⟩ := h1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply WP.spec_bind (Reader.read_byte.spec_cons r1)
      rintro ⟨res2, r2⟩ h2
      simp only [WP.uncurry'_pair, uncurry] at h2 ⊢
      cases res2
      · obtain ⟨hrest2, hin2, hpos2, hinv2⟩ := h2
        simp only [bind_ok]
        apply WP.spec_bind (Reader.read_byte.spec_cons r2)
        rintro ⟨res3, r3⟩ h3
        simp only [WP.uncurry'_pair, uncurry] at h3 ⊢
        cases res3
        · obtain ⟨hrest3, hin3, hpos3, hinv3⟩ := h3
          simp only [bind_ok]
          apply WP.spec_bind (Reader.read_byte.spec_cons r3)
          rintro ⟨res4, r4⟩ h4
          simp only [WP.uncurry'_pair, uncurry] at h4 ⊢
          cases res4
          · obtain ⟨hrest4, hin4, hpos4, hinv4⟩ := h4
            simp only [bind_ok]
            apply WP.spec_bind (Reader.read_byte.spec_cons r4)
            rintro ⟨res5, r5⟩ h5
            simp only [WP.uncurry'_pair, uncurry] at h5 ⊢
            cases res5
            · obtain ⟨hrest5, hin5, hpos5, hinv5⟩ := h5
              simp only [bind_ok]
              apply WP.spec_bind (Reader.read_byte.spec_cons r5)
              rintro ⟨res6, r6⟩ h6
              simp only [WP.uncurry'_pair, uncurry] at h6 ⊢
              cases res6
              · obtain ⟨hrest6, hin6, hpos6, hinv6⟩ := h6
                simp only [bind_ok]
                simp only [WP.spec_ok, WP.uncurry'_pair]
                refine ⟨by simp [*], hinv6, 6, ⟨rfl, ?_, ?_⟩, by scalar_tac⟩
                · simp [hrest1, hrest2, hrest3, hrest4, hrest5, hrest6]
                · simp [Array.make, hrest1, hrest2, hrest3, hrest4, hrest5, hrest6]
              · obtain ⟨hnil, -, rfl⟩ := h6
                simp only [bind_ok,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
                refine ⟨by simp [hin1, hin2, hin3, hin4, hin5, ], hinv5, ?_⟩
                simp [hrest1, hrest2, hrest3, hrest4, hrest5, hnil]
            · obtain ⟨hnil, -, rfl⟩ := h5
              simp only [bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
              refine ⟨by simp [hin1, hin2, hin3, hin4, ], hinv4, ?_⟩
              simp [hrest1, hrest2, hrest3, hrest4, hnil]
          · obtain ⟨hnil, -, rfl⟩ := h4
            simp only [bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
            refine ⟨by simp [hin1, hin2, hin3, ], hinv3, ?_⟩
            simp [hrest1, hrest2, hrest3, hnil]
        · obtain ⟨hnil, -, rfl⟩ := h3
          simp only [bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
          refine ⟨by simp [hin1, hin2, ], hinv2, ?_⟩
          simp [hrest1, hrest2, hnil]
      · obtain ⟨hnil, -, rfl⟩ := h2
        simp only [bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
        refine ⟨by simp [hin1, ], hinv1, ?_⟩
        simp [hrest1, hnil]
    · obtain ⟨hnil, -, rfl⟩ := h1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      refine ⟨by simp [], hinv, ?_⟩
      simp [hnil]
  disjoint _ _ _ hD hF := Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hF hD.2.1)
  functional _ m _ m' _ hD hD' := by
    refine ⟨?_, hD.1.trans hD'.1.symm⟩
    exact Aeneas.Std.Array.ext (m : Aeneas.Std.Array U8 6#usize) m' (hD.2.2.trans hD'.2.2.symm)

/-! ## `EtherType` -/

/-- **Spec theorem for `<EtherType as Decode>::decode`**: a big-endian `u16` of
    at least `0x0600` (smaller values are 802.3 lengths). -/
instance _root_.net.ethernet.EtherType.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs EtherType.Insts.UntrustedReaderDecode
      (fun l t k => k = 2 ∧ 2 ≤ l.length ∧ (t : U16).val = beNat (l.take 2) ∧
        1536 ≤ (t : U16).val)
      (fun l => ¬ (2 ≤ l.length ∧ 1536 ≤ beNat (l.take 2))) where
  spec r hinv := by
    simp only [EtherType.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU16_spec r hinv)
    rintro ⟨res, r'⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · obtain ⟨hle, hv, hin, hpos, hinv'⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      split
      · rename_i hge
        simp only [WP.spec_ok, WP.uncurry'_pair]
        simp only [ge_iff_le, UScalar.le_equiv, MIN_ETHER_TYPE_val] at hge
        exact ⟨hin, hinv', 2, ⟨rfl, hle, hv, by scalar_tac⟩, hpos⟩
      · rename_i hlt
        simp only [WP.spec_ok, WP.uncurry'_pair]
        simp only [ge_iff_le, UScalar.le_equiv, MIN_ETHER_TYPE_val, not_le] at hlt
        exact ⟨hin, hinv', fun ⟨_, h⟩ => by scalar_tac⟩
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, fun ⟨h, _⟩ => by scalar_tac⟩
  disjoint _ _ _ hD hF := hF ⟨hD.2.1, hD.2.2.1 ▸ hD.2.2.2⟩
  functional _ t _ t' _ hD hD' :=
    ⟨(UScalar.eq_equiv (t : U16) t').mpr (hD.2.2.1.trans hD'.2.2.1.symm), hD.1.trans hD'.1.symm⟩


/-! ## `VlanTag` -/

/-- The fields of a tag control information word `t`. -/
def VlanTag.OfTci (t : Nat) (v : VlanTag) : Prop :=
  v.pcp.val = t / 8192 ∧ v.dei = decide (t / 4096 % 2 = 1) ∧ v.vid.val = t % 4096

/-- **Spec theorem for `<VlanTag as Decode>::decode`**: a big-endian TCI whose
    VLAN ID is not the reserved `0xFFF`, split into its fields. -/
instance _root_.net.ethernet.VlanTag.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs VlanTag.Insts.UntrustedReaderDecode
      (fun l v k => k = 2 ∧ 2 ≤ l.length ∧ beNat (l.take 2) % 4096 ≠ 4095 ∧
        VlanTag.OfTci (beNat (l.take 2)) v)
      (fun l => ¬ (2 ≤ l.length ∧ beNat (l.take 2) % 4096 ≠ 4095)) where
  spec r hinv := by
    simp only [VlanTag.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU16_spec r hinv)
    rintro ⟨res, r'⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · rename_i a
      obtain ⟨hle, hv, hin, hpos, hinv'⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step*
      · have hres : vid = VID_RESERVED := ‹_›
        have hvid : vid.val = (a : U16).val % 4096 := by
          rw [vid_post, UScalar.val_and]
          simpa using Nat.and_two_pow_sub_one_eq_mod (a : U16).val 12
        have h4095 : vid.val = 4095 := by rw [hres]; simp
        refine ⟨hin, hinv', fun ⟨_, hne⟩ => hne ?_⟩
        rw [← hv]
        scalar_tac
      · have hres : ¬vid = VID_RESERVED := ‹_›
        have hvid : vid.val = (a : U16).val % 4096 := by
          rw [vid_post, UScalar.val_and]
          simpa using Nat.and_two_pow_sub_one_eq_mod (a : U16).val 12
        have hne : vid.val ≠ 4095 := fun h => hres ((UScalar.eq_equiv _ _).mpr (by simp [h]))
        have hpcp : i1.val = (a : U16).val / 8192 := by
          have hi : i.val = (a : U16).val / 8192 := by
            rw [i_post, Nat.shiftRight_eq_div_pow]
          rw [i1_post, UScalar.cast_val_eq, hi]
          have : (a : U16).val < 65536 := by scalar_tac
          simp only [UScalarTy.U8_numBits_eq]
          scalar_tac
        have hdei : i3.val = (a : U16).val / 4096 % 2 := by
          rw [i3_post, UScalar.val_and, i2_post, Nat.shiftRight_eq_div_pow]
          simp [Nat.and_one_is_mod]
        refine ⟨hin, hinv', hle, by rw [← hv]; scalar_tac, ?_, hpos⟩
        rw [← hv]
        refine ⟨hpcp, ?_, by rw [hvid]⟩
        simp only [UScalar.eq_equiv, hdei]
        simp
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, fun ⟨h, _⟩ => by scalar_tac⟩
  disjoint _ _ _ hD hF := hF ⟨hD.2.1, hD.2.2.1⟩
  functional _ v _ v' _ hD hD' := by
    obtain ⟨hk, -, -, hp, hd, hv⟩ := hD
    obtain ⟨hk', -, -, hp', hd', hv'⟩ := hD'
    refine ⟨?_, hk.trans hk'.symm⟩
    rcases v with ⟨p, d, i⟩
    rcases v' with ⟨p', d', i'⟩
    simp only at hp hd hv hp' hd' hv'
    have : p = p' := (UScalar.eq_equiv _ _).mpr (hp.trans hp'.symm)
    have : i = i' := (UScalar.eq_equiv _ _).mpr (hv.trans hv'.symm)
    simp_all

/-! ## `Tagging` -/

/-- The bytes `l` after the MAC addresses decode as `g` in `k` bytes: either an
    802.1Q tag (TPID `0x8100`, a valid TCI) followed by an EtherType other than
    `0x8100`, or directly an EtherType (at least `0x0600`). -/
def Tagging.Decodes (l : List U8) (g : Tagging) (k : Nat) : Prop :=
  2 ≤ l.length ∧
    ((beNat (l.take 2) = 33024 ∧ ∃ v, FmtD VlanTag.Insts.UntrustedReaderDecode (l.drop 2) v 2 ∧
        FmtD EtherType.Insts.UntrustedReaderDecode (l.drop 4) g.ether_type 2 ∧
        (g.ether_type : U16).val ≠ 33024 ∧ g.vlan = some v ∧ k = 6) ∨
      (beNat (l.take 2) ≠ 33024 ∧ 1536 ≤ beNat (l.take 2) ∧ g.vlan = none ∧
        (g.ether_type : U16).val = beNat (l.take 2) ∧ k = 2))

/-- **Spec theorem for `<Tagging as Decode>::decode`**: decodes exactly as
    `Tagging.Decodes` says, and fails exactly when no such decoding exists. -/
instance _root_.net.ethernet.Tagging.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs Tagging.Insts.UntrustedReaderDecode Tagging.Decodes
      (fun l => ∀ g k, ¬ Tagging.Decodes l g k) where
  spec r hinv := by
    simp only [Tagging.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU16_spec r hinv)
    rintro ⟨res, r1⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · rename_i t
      obtain ⟨hle, ht, hin1, hpos1, hinv1⟩ := h
      have hrest1 := Reader.rest_advance r r1 2 hin1 hpos1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      split
      · have htp : t = TPID_8021Q := ‹_›
        have hb : beNat ((Reader.rest r).take 2) = 33024 := by
          rw [← ht]; simpa using congrArg UScalar.val htp
        apply WP.spec_bind (Reader.decode.spec VlanTag.Insts.UntrustedReaderDecode r1 hinv1)
        rintro ⟨res2, r2⟩ h2
        simp only [WP.uncurry'_pair, uncurry] at h2 ⊢
        cases res2
        · rename_i v
          obtain ⟨k2, hDv, hin2, hpos2, hinv2⟩ := h2
          obtain rfl : k2 = 2 := hDv.1
          have hrest2 := Reader.rest_advance r1 r2 2 hin2 hpos2
          simp only [bind_ok]
          apply WP.spec_bind (Reader.decode.spec EtherType.Insts.UntrustedReaderDecode r2 hinv2)
          rintro ⟨res3, r3⟩ h3
          simp only [WP.uncurry'_pair, uncurry] at h3 ⊢
          cases res3
          · rename_i e
            obtain ⟨k3, hDe, hin3, hpos3, hinv3⟩ := h3
            obtain rfl : k3 = 2 := hDe.1
            have hrest3 : Reader.rest r2 = (Reader.rest r).drop 4 := by
              rw [hrest2, hrest1, List.drop_drop]
            have hDv' : FmtD VlanTag.Insts.UntrustedReaderDecode ((Reader.rest r).drop 2) v 2 := by
              rw [← hrest1]; exact hDv
            have hDe' : FmtD EtherType.Insts.UntrustedReaderDecode ((Reader.rest r).drop 4) e 2 := by
              rw [← hrest3]; exact hDe
            simp only [bind_ok]
            split
            · have he : e = TPID_8021Q := ‹_›
              simp only [WP.spec_ok, WP.uncurry'_pair]
              refine ⟨by simp [hin3, hin2, hin1], hinv3, ?_⟩
              rintro g k ⟨-, ⟨-, v', -, hge, hne, -⟩ | ⟨hne, -⟩⟩
              · have := ((FmtLaws EtherType.Insts.UntrustedReaderDecode).functional _ _ _ _ _ hDe' hge).1
                rw [← this] at hne
                exact hne (by simpa using congrArg UScalar.val he)
              · exact hne hb
            · have he : ¬ e = TPID_8021Q := ‹_›
              simp only [WP.spec_ok, WP.uncurry'_pair]
              refine ⟨by simp [hin3, hin2, hin1], hinv3, 6,
                ⟨hle, Or.inl ⟨hb, v, hDv', hDe', ?_, rfl, rfl⟩⟩, by scalar_tac⟩
              intro h
              exact he ((UScalar.eq_equiv _ _).mpr (by simpa using h))
          · obtain ⟨hF3, rfl⟩ := h3
            have hrest3 : Reader.rest r3 = (Reader.rest r).drop 4 := by
              rw [hrest2, hrest1, List.drop_drop]
            simp only [bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
            refine ⟨by simp [hin2, hin1], hinv2, ?_⟩
            rintro g k ⟨-, ⟨-, v', -, hge, -⟩ | ⟨hne, -⟩⟩
            · apply hF3
              rw [hrest3]
              exact ⟨hge.2.1, hge.2.2.1 ▸ hge.2.2.2⟩
            · exact hne hb
        · obtain ⟨hF2, rfl⟩ := h2
          simp only [bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
          refine ⟨hin1, hinv1, ?_⟩
          rintro g k ⟨-, ⟨-, v', hv', -⟩ | ⟨hne, -⟩⟩
          · apply hF2
            rw [hrest1]
            exact ⟨hv'.2.1, hv'.2.2.1⟩
          · exact hne hb
      · have htp : ¬ t = TPID_8021Q := ‹_›
        have hb : beNat ((Reader.rest r).take 2) ≠ 33024 := by
          rw [← ht]
          intro h
          exact htp ((UScalar.eq_equiv _ _).mpr (by simpa using h))
        split
        · have hge : t ≥ MIN_ETHER_TYPE := ‹_›
          simp only [WP.spec_ok, WP.uncurry'_pair]
          refine ⟨hin1, hinv1, 2, ⟨hle, Or.inr ⟨hb, ?_, rfl, ht, rfl⟩⟩, hpos1⟩
          rw [← ht]
          simpa using hge
        · have hlt : ¬ t ≥ MIN_ETHER_TYPE := ‹_›
          simp only [WP.spec_ok, WP.uncurry'_pair]
          refine ⟨hin1, hinv1, ?_⟩
          rintro g k ⟨-, ⟨hb', -⟩ | ⟨-, h1536, -⟩⟩
          · exact hb hb'
          · apply hlt
            simp only [ge_iff_le, UScalar.le_equiv, MIN_ETHER_TYPE_val]
            rw [ht]
            exact h1536
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, fun g k ⟨h, _⟩ => by scalar_tac⟩
  disjoint _ _ _ hD hF := hF _ _ hD
  functional := by
    rintro l ⟨vl, et⟩ k ⟨vl', et'⟩ k'
      ⟨-, ⟨hb, v, hv, he, -, hvl, rfl⟩ | ⟨hb, -, hvl, he, rfl⟩⟩
      ⟨-, ⟨hb', v', hv', he', -, hvl', rfl⟩ | ⟨hb', -, hvl', he', rfl⟩⟩
    · simp only at hvl hvl' he he'
      obtain ⟨rfl, -⟩ := (FmtLaws VlanTag.Insts.UntrustedReaderDecode).functional _ _ _ _ _ hv hv'
      obtain ⟨rfl, -⟩ := (FmtLaws EtherType.Insts.UntrustedReaderDecode).functional _ _ _ _ _ he he'
      subst hvl hvl'
      exact ⟨rfl, rfl⟩
    · exact absurd hb hb'
    · exact absurd hb' hb
    · simp only at hvl hvl' he he'
      have : et = et' := (UScalar.eq_equiv _ _).mpr (he.trans he'.symm)
      subst hvl hvl' this
      exact ⟨rfl, rfl⟩

end net.ethernet
