/- Hand-written specs of the `Validate` impls of `net::ethernet`: `Frame` and
   `FrameWithFcs`. -/
import Net.Manual
import Net.Specs.EthernetHeader

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.ethernet

/-! ## What a well-formed frame is -/

/-- The frame `l` carries an 802.1Q tag: bytes 12 and 13 are the TPID `0x8100`. -/
def Frame.Tagged (l : List U8) : Prop := beNat ((l.drop 12).take 2) = 33024

open Classical in
/-- The header length: 18 bytes with a tag, 14 without. -/
noncomputable def Frame.headerLen (l : List U8) : Nat := if Frame.Tagged l then 18 else 14

open Classical in
/-- The smallest payload: 42 bytes with a tag, 46 without (frames are at least
    64 bytes with the FCS). -/
noncomputable def Frame.minPayload (l : List U8) : Nat := if Frame.Tagged l then 42 else 46

/-- `l` is a well-formed Ethernet II frame (without FCS) that decodes to `f`:
    its header (18 bytes if tagged, else 14) decodes as `f.header`, the payload
    is between the minimum and 1500 bytes, and `f.payload` is exactly the rest. -/
def Frame.Spec (l : List U8) (f : Frame) : Prop :=
  14 ≤ l.length ∧
    Frame.headerLen l + Frame.minPayload l ≤ l.length ∧
    l.length ≤ Frame.headerLen l + 1500 ∧
    FmtD EthernetHeader.Insts.UntrustedReaderDecode (l.take (Frame.headerLen l)) f.header
      (Frame.headerLen l) ∧
    (f.payload : Slice U8).val = l.drop (Frame.headerLen l)

/-- `l` is a well-formed Ethernet II frame followed by its FCS: the last 4
    bytes, least significant first, are the CRC-32 of the rest, which is a
    well-formed frame decoding to `fw.frame`. -/
def FrameWithFcs.Spec (l : List U8) (fw : FrameWithFcs) : Prop :=
  4 ≤ l.length ∧
    net.crc32.spec (l.take (l.length - 4)) = BitVec.ofNat 32 (leNat (l.drop (l.length - 4))) ∧
    Frame.Spec (l.take (l.length - 4)) fw.frame

/-! ## Helper lemmas -/

theorem take2_drop12 (l : List U8) (h : 14 ≤ l.length) :
    (l.drop 12).take 2 = [l[12], l[13]] := by
  rw [List.drop_eq_getElem_cons (show 12 < l.length by scalar_tac),
    List.drop_eq_getElem_cons (show 12 + 1 < l.length by scalar_tac)]
  rfl

theorem beNat_pair (a b : U8) : beNat [a, b] = 33024 ↔ a.val = 129 ∧ b.val = 0 := by
  simp only [beNat, List.foldl_cons, List.foldl_nil]
  constructor
  · intro h; scalar_tac
  · rintro ⟨ha, hb⟩; simp [ha, hb]

theorem U32_bv_eq_ofNat (x : U32) : x.bv = BitVec.ofNat 32 x.val := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, UScalar.bv_toNat, Nat.mod_eq_of_lt (by simpa using x.hBounds)]

theorem tagged_iff (l : List U8) (h : 14 ≤ l.length) :
    Frame.Tagged l ↔ (l[12]'(by scalar_tac)).val = 129 ∧ (l[13]'(by scalar_tac)).val = 0 := by
  rw [Frame.Tagged, take2_drop12 l h, beNat_pair]


/-! ## `Frame` -/

/-- **Spec theorem for `<Frame as Validate<&[u8]>>::validate`**: accepts exactly
    the well-formed Ethernet II frames (tagged or not), and returns their
    decoding. -/
@[step]
theorem _root_.net.ethernet.Frame.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Frame.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Frame ValidationError) =>
        match r with
        | .Ok f => Frame.Spec input.val f
        | .Err _ => ∀ f, ¬ Frame.Spec input.val f ⦄ := by
  unfold Frame.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  dsimp only
  split
  · simp only [WP.spec_ok]
    rintro f ⟨h14, -⟩
    scalar_tac
  · have h14 : 14 ≤ input.val.length := by scalar_tac
    step as ⟨ i1, hi1 ⟩
    split
    · have h129 : i1 = 129#u8 := ‹_›
      step as ⟨ i2, hi2 ⟩
      split
      · have h0 : i2 = 0#u8 := by simpa using ‹decide (i2 = 0#u8) = true›
        have htag : Frame.Tagged input.val := by
          rw [tagged_iff _ h14, ← hi1, ← hi2, h129, h0]; simp
        step as ⟨ hl, hl_post ⟩
        have hHL : Frame.headerLen input.val = (hl).val := by
          simp only [Frame.headerLen, htag]; scalar_tac
        have hMP : Frame.minPayload input.val = 42 := by
          simp only [Frame.minPayload, htag]; rfl
        step*
        · rintro f ⟨-, hlo, hhi, -⟩
          simp only [hHL, hMP] at hlo hhi
          scalar_tac
        · rintro f ⟨-, hlo, hhi, -⟩
          simp only [hHL, hMP] at hlo hhi
          scalar_tac
        · rintro f ⟨-, hlo, hhi, -⟩
          simp only [hHL, hMP] at hlo hhi
          scalar_tac
        · have hu : (u : Slice U8).val = input.val.take (hl).val := by
            rw [u_post, s_post]; simp [List.slice]
          have hlen : (input.val.take (hl).val).length = (hl).val := by
            simp only [List.length_take]; scalar_tac
          apply WP.spec_bind
            (UntrustedShared0SliceU8.read_all.spec_of EthernetHeader.Insts.UntrustedReaderDecode u)
          rintro (h | e) hres
          · simp only [hu, hlen] at hres
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step*
            refine ⟨h14, by rw [hHL, hMP]; scalar_tac, by rw [hHL]; scalar_tac, by rw [hHL]; exact hres, ?_⟩
            simp [u1_post, s1_post, hHL]
          · simp only [hu, hlen] at hres
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
            rintro f ⟨-, -, -, hD, -⟩
            rw [hHL] at hD
            exact hres f.header hD
      · have hn0 : ¬ i2 = 0#u8 := by simpa using ‹¬ decide (i2 = 0#u8) = true›
        have htag : ¬ Frame.Tagged input.val := by
          rw [tagged_iff _ h14, ← hi1, ← hi2]
          rintro ⟨-, h⟩
          exact hn0 ((UScalar.eq_equiv _ _).mpr (by simpa using h))
        have hHL : Frame.headerLen input.val = (HEADER_LEN).val := by
          simp only [Frame.headerLen, htag]; scalar_tac
        have hMP : Frame.minPayload input.val = 46 := by
          simp only [Frame.minPayload, htag]; rfl
        step*
        · rintro f ⟨-, hlo, hhi, -⟩
          simp only [hHL, hMP] at hlo hhi
          scalar_tac
        · rintro f ⟨-, hlo, hhi, -⟩
          simp only [hHL, hMP] at hlo hhi
          scalar_tac
        · have hu : (u : Slice U8).val = input.val.take (HEADER_LEN).val := by
            rw [u_post, s_post]; simp [List.slice]
          have hlen : (input.val.take (HEADER_LEN).val).length = (HEADER_LEN).val := by
            simp only [List.length_take]; scalar_tac
          apply WP.spec_bind
            (UntrustedShared0SliceU8.read_all.spec_of EthernetHeader.Insts.UntrustedReaderDecode u)
          rintro (h | e) hres
          · simp only [hu, hlen] at hres
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step*
            refine ⟨h14, by rw [hHL, hMP]; scalar_tac, by rw [hHL]; scalar_tac, by rw [hHL]; exact hres, ?_⟩
            simp [u1_post, s1_post, hHL]
          · simp only [hu, hlen] at hres
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
            rintro f ⟨-, -, -, hD, -⟩
            rw [hHL] at hD
            exact hres f.header hD
    · have hn : ¬ i1 = 129#u8 := ‹_›
      have htag : ¬ Frame.Tagged input.val := by
        rw [tagged_iff _ h14, ← hi1]
        rintro ⟨h, -⟩
        exact hn ((UScalar.eq_equiv _ _).mpr (by simpa using h))
      have hHL : Frame.headerLen input.val = (HEADER_LEN).val := by
        simp only [Frame.headerLen, htag]; scalar_tac
      have hMP : Frame.minPayload input.val = 46 := by
        simp only [Frame.minPayload, htag]; rfl
      simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, uncurry]
      step*
      · rintro f ⟨-, hlo, hhi, -⟩
        simp only [hHL, hMP] at hlo hhi
        scalar_tac
      · rintro f ⟨-, hlo, hhi, -⟩
        simp only [hHL, hMP] at hlo hhi
        scalar_tac
      · have hu : (u : Slice U8).val = input.val.take (HEADER_LEN).val := by
          rw [u_post, s_post]; simp [List.slice]
        have hlen : (input.val.take (HEADER_LEN).val).length = (HEADER_LEN).val := by
          simp only [List.length_take]; scalar_tac
        apply WP.spec_bind
          (UntrustedShared0SliceU8.read_all.spec_of EthernetHeader.Insts.UntrustedReaderDecode u)
        rintro (h | e) hres
        · simp only [hu, hlen] at hres
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step*
          refine ⟨h14, by rw [hHL, hMP]; scalar_tac, by rw [hHL]; scalar_tac, by rw [hHL]; exact hres, ?_⟩
          simp [u1_post, s1_post, hHL]
        · simp only [hu, hlen] at hres
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
          rintro f ⟨-, -, -, hD, -⟩
          rw [hHL] at hD
          exact hres f.header hD
/-! ## `FrameWithFcs` -/

/-- **Spec theorem for `<FrameWithFcs as Validate<&[u8]>>::validate`**: accepts
    exactly the well-formed frames followed by their correct CRC-32. -/
theorem _root_.net.ethernet.FrameWithFcs.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    FrameWithFcs.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result FrameWithFcs ValidationError) =>
        match r with
        | .Ok fw => FrameWithFcs.Spec input.val fw
        | .Err _ => ∀ fw, ¬ FrameWithFcs.Spec input.val fw ⦄ := by
  unfold FrameWithFcs.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  dsimp only
  split
  · simp only [WP.spec_ok]
    rintro fw ⟨h4, -⟩
    scalar_tac
  · step*
    have hbody : body.val = input.val.take (input.val.length - 4) := by
      rw [body_post]; simp [List.slice, body_len_post]
    have hs : (u : Slice U8).val = input.val.drop (input.val.length - 4) := by
      rw [u_post, s_post]; simp [body_len_post]
    simp only [Untrusted.validate_eq]
    step as ⟨ res, hres ⟩
    cases res
    rename_i fcs
    · obtain ⟨-, hfcs⟩ := hres
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step*
      · have hne : i2 ≠ fcs := by
          intro h
          have := ‹(i2 != fcs) = true›
          simp [h] at this
        rintro fw ⟨-, hcrc, -⟩
        apply hne
        apply (UScalar.eq_equiv_bv_eq _ _).mpr
        have h1 : i2.bv = net.crc32.spec body.val := i2_post
        calc i2.bv = net.crc32.spec body.val := h1
          _ = BitVec.ofNat 32 (leNat (u : Slice U8).val) := by rw [hbody, hcrc, ← hs]
          _ = (fcs : U32).bv := by rw [← hfcs, U32_bv_eq_ofNat]
      · have heq : i2 = fcs :=
          (UScalar.eq_equiv _ _).mpr (by simpa using ‹¬ (i2 != fcs) = true›)
        have hcrc : net.crc32.spec (input.val.take (input.val.length - 4)) =
            BitVec.ofNat 32 (leNat (input.val.drop (input.val.length - 4))) := by
          have h1 : i2.bv = net.crc32.spec body.val := i2_post
          calc net.crc32.spec (input.val.take (input.val.length - 4))
              = net.crc32.spec body.val := by rw [hbody]
            _ = (fcs : U32).bv := by rw [← h1, heq]
            _ = BitVec.ofNat 32 (leNat (u : Slice U8).val) := by rw [U32_bv_eq_ofNat, hfcs]
            _ = BitVec.ofNat 32 (leNat (input.val.drop (input.val.length - 4))) := by rw [hs]
        cases r1
        · simp only at r1_post
          simp only [bind_ok, WP.spec_ok]
          refine ⟨by scalar_tac, hcrc, ?_⟩
          rw [← hbody, ← u1_post]
          exact r1_post
        · simp only [bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
          simp only at r1_post
          rintro fw ⟨-, -, hF⟩
          rw [← hbody, ← u1_post] at hF
          exact r1_post fw.frame hF
    · exfalso
      obtain ⟨hne, -⟩ := hres
      apply hne
      rw [u_post, s_post1]
      scalar_tac

end net.ethernet
