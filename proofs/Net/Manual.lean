/- Hand-written specs for the `net` crate that derived types build on: the
   two `Decode` impls that are not derived. Kept by `cargo untrusted verify`;
   imported by its automatic attempts. -/
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

end net.ethernet
