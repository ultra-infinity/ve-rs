/- Hand-written specs of the `Decode` impls of `net::arp` that are not
   derived: `EthernetIpv4` and `Operation`. -/
import Net.Funs
import Untrusted

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.arp

/-! ## Constants -/

@[simp, scalar_tac_simps] theorem PACKET_LEN_val : PACKET_LEN.val = 28 := by simp [PACKET_LEN]
@[simp, scalar_tac_simps] theorem OP_REQUEST_val : OP_REQUEST.val = 1 := by simp [OP_REQUEST]
@[simp, scalar_tac_simps] theorem OP_REPLY_val : OP_REPLY.val = 2 := by simp [OP_REPLY]

/-! ## `EthernetIpv4` -/

/-- `l` starts with the fixed fields of an Ethernet/IPv4 ARP packet:
    `00 01 08 00 06 04`. -/
def EthernetIpv4.Valid (l : List U8) : Prop :=
  6 ≤ l.length ∧ beNat (l.take 4) = 0x00010800 ∧ beNat ((l.drop 4).take 2) = 0x0604

/-- **Spec theorem for `<EthernetIpv4 as Decode>::decode`**: the six bytes
    `00 01 08 00 06 04`. -/
instance _root_.net.arp.EthernetIpv4.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs EthernetIpv4.Insts.UntrustedReaderDecode
      (fun l _ k => k = 6 ∧ EthernetIpv4.Valid l)
      (fun l => ¬ EthernetIpv4.Valid l) where
  spec r hinv := by
    simp only [EthernetIpv4.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.read.BigEndianU32_spec r hinv)
    rintro ⟨res, r1⟩ h
    simp only [WP.uncurry'_pair, uncurry] at h ⊢
    cases res
    · rename_i a
      obtain ⟨hle, hv, hin1, hpos1, hinv1⟩ := h
      have hrest1 := Reader.rest_advance r r1 4 hin1 hpos1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      split
      · rename_i hne
        simp only [WP.spec_ok, WP.uncurry'_pair]
        refine ⟨hin1, hinv1, fun ⟨_, ha, _⟩ => ?_⟩
        have : a = 67584#u32 := (UScalar.eq_equiv _ _).mpr (by rw [hv, ha]; rfl)
        simp [this] at hne
      · rename_i heq
        have ha : (a : U32).val = 67584 := by simpa using heq
        apply WP.spec_bind (Reader.read.BigEndianU16_spec r1 hinv1)
        rintro ⟨res2, r2⟩ h2
        simp only [WP.uncurry'_pair, uncurry] at h2 ⊢
        cases res2
        · rename_i b
          obtain ⟨hle2, hv2, hin2, hpos2, hinv2⟩ := h2
          rw [hrest1] at hle2 hv2
          simp only [bind_ok]
          split
          · rename_i hne
            simp only [WP.spec_ok, WP.uncurry'_pair]
            refine ⟨by rw [hin2, hin1], hinv2, fun ⟨_, _, hb⟩ => ?_⟩
            have : b = 1540#u16 := (UScalar.eq_equiv _ _).mpr (by rw [hv2, hb]; rfl)
            simp [this] at hne
          · rename_i heq2
            have hb : (b : U16).val = 1540 := by simpa using heq2
            simp only [WP.spec_ok, WP.uncurry'_pair]
            refine ⟨by rw [hin2, hin1], hinv2, 6, ⟨rfl, ?_, ?_, ?_⟩, by scalar_tac⟩
            · simp only [List.length_drop] at hle2; omega
            · rw [← hv, ha]
            · rw [← hv2, hb]
        · obtain ⟨hlt2, -, rfl⟩ := h2
          simp only [bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
          refine ⟨hin1, hinv1, fun ⟨h6, _⟩ => ?_⟩
          rw [hrest1] at hlt2
          simp only [List.length_drop] at hlt2
          omega
    · obtain ⟨hlt, -, rfl⟩ := h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, fun ⟨h6, _⟩ => by scalar_tac⟩
  disjoint _ _ _ hD hF := hF hD.2
  functional _ _ _ _ _ hD hD' := ⟨rfl, hD.1.trans hD'.1.symm⟩

/-! ## `Operation` -/

/-- The operation of the ARP packet `l`: the big-endian `u16` at bytes 6–7. -/
def Operation.Of (l : List U8) : Nat := beNat ((l.drop 6).take 2)

/-- **Spec theorem for `<Operation as Decode>::decode`**: the fixed fields
    (`EthernetIpv4`), then a big-endian `u16` that is 1 (request) or 2
    (reply). -/
instance _root_.net.arp.Operation.Insts.UntrustedReaderDecode.decode.spec :
    DecodesAs Operation.Insts.UntrustedReaderDecode
      (fun l o k => k = 8 ∧ EthernetIpv4.Valid l ∧ 8 ≤ l.length ∧
        (Operation.Of l = 1 ∨ Operation.Of l = 2) ∧ (o : U16).val = Operation.Of l)
      (fun l => ¬ (EthernetIpv4.Valid l ∧ 8 ≤ l.length ∧
        (Operation.Of l = 1 ∨ Operation.Of l = 2))) where
  spec r hinv := by
    simp only [Operation.Insts.UntrustedReaderDecode.decode]
    apply WP.spec_bind (Reader.decode.spec EthernetIpv4.Insts.UntrustedReaderDecode r hinv)
    rintro ⟨res1, r1⟩ h1
    simp only [WP.uncurry'_pair, uncurry] at h1 ⊢
    cases res1
    · obtain ⟨k1, ⟨rfl, hV⟩, hin1, hpos1, hinv1⟩ := h1
      have hrest1 := Reader.rest_advance r r1 6 hin1 hpos1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply WP.spec_bind (Reader.read.BigEndianU16_spec r1 hinv1)
      rintro ⟨res, r'⟩ h
      simp only [WP.uncurry'_pair, uncurry] at h ⊢
      cases res
      · rename_i a
        obtain ⟨hle, hv, hin, hpos, hinv'⟩ := h
        rw [hrest1] at hle hv
        have h8 : 8 ≤ (Reader.rest r).length := by simp only [List.length_drop] at hle; omega
        simp only [bind_ok]
        split
        · rename_i h1
          split
          · rename_i h2
            simp only [WP.spec_ok, WP.uncurry'_pair]
            refine ⟨by rw [hin, hin1], hinv', fun ⟨_, _, h12⟩ => ?_⟩
            rcases h12 with h12 | h12
            · have : a = OP_REQUEST :=
                (UScalar.eq_equiv _ _).mpr (by rw [hv, ← Operation.Of, h12]; simp)
              simp [this] at h1
            · have : a = OP_REPLY :=
                (UScalar.eq_equiv _ _).mpr (by rw [hv, ← Operation.Of, h12]; simp)
              simp [this] at h2
          · rename_i h2
            have : (a : U16).val = 2 := by simpa using h2
            simp only [WP.spec_ok, WP.uncurry'_pair]
            exact ⟨by rw [hin, hin1], hinv', 8,
              ⟨rfl, hV, h8, Or.inr (by rw [Operation.Of, ← hv, this]), hv⟩, by scalar_tac⟩
        · rename_i h1
          have : (a : U16).val = 1 := by simpa using h1
          simp only [WP.spec_ok, WP.uncurry'_pair]
          exact ⟨by rw [hin, hin1], hinv', 8,
            ⟨rfl, hV, h8, Or.inl (by rw [Operation.Of, ← hv, this]), hv⟩, by scalar_tac⟩
      · obtain ⟨hlt, -, rfl⟩ := h
        simp only [bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
        refine ⟨hin1, hinv1, fun ⟨_, h8, _⟩ => ?_⟩
        rw [hrest1] at hlt
        simp only [List.length_drop] at hlt
        omega
    · obtain ⟨hF, rfl⟩ := h1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨trivial, hinv, fun ⟨hV, _⟩ => hF hV⟩
  disjoint _ _ _ hD hF := hF ⟨hD.2.1, hD.2.2.1, hD.2.2.2.1⟩
  functional _ o _ o' _ hD hD' :=
    ⟨(UScalar.eq_equiv (o : U16) o').mpr (hD.2.2.2.2.trans hD'.2.2.2.2.symm),
      hD.1.trans hD'.1.symm⟩

end net.arp
