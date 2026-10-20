/- `wireguard::noise` computes exactly the handshake of `NoiseSpec.lean`. -/
import Wireguard.NoiseSpec

open Aeneas Aeneas.Std Result

namespace wireguard.noise

open wireguard.crypto Spec

/-! ## Constants -/

theorem CONSTRUCTION_val : CONSTRUCTION.val = construction := by
  simp only [CONSTRUCTION, Array.make]
  decide

theorem IDENTIFIER_val : IDENTIFIER.val = identifier := by
  simp only [IDENTIFIER, Array.make]
  decide

@[simp, scalar_tac_simps] theorem TIMESTAMP_LEN_val : TIMESTAMP_LEN.val = 12 := by
  simp [TIMESTAMP_LEN]

/-! ## Timestamps -/

/-- **Spec theorem for the loop of `timestamp_after`**: compares the bytes from
    `i` on. -/
@[step]
theorem timestamp_after_loop.spec (a b : Array U8 12#usize) (i : Usize) (hi : i.val ≤ 12) :
    timestamp_after_loop a b i ⦃ (r : Bool) => r = after (a.val.drop i.val) (b.val.drop i.val) ⦄ := by
  unfold timestamp_after_loop
  split
  · have hl : i.val < a.val.length := by simp; scalar_tac
    have hl' : i.val < b.val.length := by simp; scalar_tac
    step*
    · rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons hl', ← i1_post, ← i2_post]
      have hne : i1 ≠ i2 := by simpa using ‹(i1 != i2) = true›
      simp only [after, hne, ↓reduceIte, gt_iff_lt]
      simp [UScalar.lt_equiv]
    · rw [r_post, List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons hl', ← i1_post, ← i2_post,
        i3_post]
      have heq : i1 = i2 := (UScalar.eq_equiv _ _).mpr (by simpa using ‹¬(i1 != i2) = true›)
      simp [after, heq]
  · simp only [WP.spec_ok]
    have : i.val = 12 := by scalar_tac
    simp [this, after]
termination_by 12 - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `timestamp_after`**. -/
@[step]
theorem timestamp_after.spec (a b : Array U8 12#usize) :
    timestamp_after a b ⦃ (r : Bool) => r = after a.val b.val ⦄ := by
  unfold timestamp_after
  step*
  simpa using r_post

@[simp] theorem empty_val : (Std.Array.empty U8).val = [] := rfl

/-! ## The handshake -/

theorem aeadOpen_some (P : Primitives) {k : Key} {n : Nat} {ad ct out : List U8}
    (h : P.aead k n ad out = ct) : aeadOpen P k n ad ct = some out := by
  have hex : ∃ m, P.aead k n ad m = ct := ⟨out, h⟩
  simp only [aeadOpen, hex, ↓reduceDIte, Option.some.injEq]
  exact P.aead_inj _ _ _ _ _ (hex.choose_spec.trans h.symm)

theorem aeadOpen_none (P : Primitives) {k : Key} {n : Nat} {ad ct : List U8}
    (h : ¬ ∃ m, P.aead k n ad m = ct) : aeadOpen P k n ad ct = none := by
  simp [aeadOpen, h]

/-- What an opening returns, as `aeadOpen`: the unique plaintext. -/
theorem aeadOpen_eq (P : Primitives) {k : Key} {n : Nat} {ad ct out : List U8} {b : Bool}
    (h1 : b = true ↔ ∃ m, P.aead k n ad m = ct) (h2 : b = true → P.aead k n ad out = ct) :
    aeadOpen P k n ad ct = if b then some out else none := by
  unfold aeadOpen
  cases b
  · simp only [Bool.false_eq_true, false_iff] at h1
    simp [h1]
  · have hex : ∃ m, P.aead k n ad m = ct := h1.mp rfl
    simp only [hex, ↓reduceDIte, ↓reduceIte, Option.some.injEq]
    exact P.aead_inj _ _ _ _ _ (hex.choose_spec.trans (h2 rfl).symm)

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

/-- **Spec theorem for `mix_hash`**: `Hash(h ‖ data)`. -/
@[step]
theorem mix_hash.spec (hh : Key) (data : Slice U8) :
    mix_hash inst c hh data ⦃ (r : Key) => r = P.hash (hh.val ++ data.val) ⦄ := by
  unfold mix_hash
  step*

/-- **Spec theorem for `initial_chain`**. -/
@[step]
theorem initial_chain.spec (sr : Key) :
    initial_chain inst c sr ⦃ (r : Chain) => r = initialChain P sr ⦄ := by
  unfold initial_chain
  step*
  simp_all [initialChain, CONSTRUCTION_val, IDENTIFIER_val]

/-- **Spec theorem for `transport_keys`**. -/
@[step]
theorem transport_keys.spec (ch : Chain) :
    transport_keys inst c ch ⦃ (r : Key × Key) => r = transportKeys P ch ⦄ := by
  unfold transport_keys
  step*
  simp_all [transportKeys]

/-- **Spec theorem for `create_initiation`**: the initiation of section 5.4.2. -/
@[step]
theorem create_initiation.spec (siPriv siPub srPub eiPriv : Key) (sender : U32)
    (ts : Array U8 12#usize) :
    create_initiation inst c siPriv siPub srPub eiPriv sender ts
      ⦃ (r : Option (message.Initiation × InitiatorState)) =>
        r = createInitiation P siPriv siPub srPub eiPriv sender ts ⦄ := by
  unfold create_initiation
  step*
  all_goals (try obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp key1_post)
  all_goals (try obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp key2_post)
  all_goals subst_vars
  all_goals simp_all [createInitiation, zeros32, zeros16, Array.eq_iff, Array.from_slice_val,
    P.aead_length]


/-- **Spec theorem for `create_response`**: the response of section 5.4.3. -/
@[step]
theorem create_response.spec (ch : Chain) (eiPub siPub psk erPriv : Key) (sender receiver : U32) :
    create_response inst c ch eiPub siPub psk erPriv sender receiver
      ⦃ (r : Option (message.Response × Chain)) =>
        r = createResponse P ch eiPub siPub psk erPriv sender receiver ⦄ := by
  unfold create_response
  step*
  all_goals (try obtain ⟨rfl, h23⟩ := Prod.ext_iff.mp key3_post)
  all_goals (try obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h23)
  all_goals subst_vars
  all_goals simp_all [createResponse, zeros32, zeros16, Array.eq_iff, Array.from_slice_val,
    P.aead_length]

/-- **Spec theorem for `consume_initiation_static`**. -/
@[step]
theorem consume_initiation_static.spec (srPriv srPub : Key) (msg : message.Initiation) :
    consume_initiation_static inst c srPriv srPub msg
      ⦃ (r : Option InitiationStatic) => r = consumeInitiationStatic P srPriv srPub msg ⦄ := by
  unfold consume_initiation_static
  step*
  all_goals (try have hopen := aeadOpen_eq P b1_post1 b1_post2)
  all_goals (try obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp key1_post)
  all_goals subst_vars
  all_goals simp_all [consumeInitiationStatic, zeros32, Array.eq_iff, Array.from_slice_val,
    P.aead_length]


/-- **Spec theorem for `consume_initiation_timestamp`**. -/
@[step]
theorem consume_initiation_timestamp.spec (srPriv : Key) (st : InitiationStatic)
    (msg : message.Initiation) :
    consume_initiation_timestamp inst c srPriv st msg
      ⦃ (r : Option (Chain × Array U8 12#usize)) =>
        r = consumeInitiationTimestamp P srPriv st msg ⦄ := by
  unfold consume_initiation_timestamp
  step*
  all_goals (try have hopen := aeadOpen_eq P b1_post1 b1_post2)
  all_goals (try obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp key_post)
  all_goals subst_vars
  all_goals simp_all [consumeInitiationTimestamp, zeros32, Array.eq_iff, Array.from_slice_val,
    P.aead_length]

/-- **Spec theorem for `consume_response`**. -/
@[step]
theorem consume_response.spec (st : InitiatorState) (siPriv psk : Key) (msg : message.Response) :
    consume_response inst c st siPriv psk msg
      ⦃ (r : Option Chain) => r = consumeResponse P st siPriv psk msg ⦄ := by
  unfold consume_response
  step*
  all_goals (try have hopen := aeadOpen_eq P b2_post1 b2_post2)
  all_goals (try obtain ⟨rfl, h23⟩ := Prod.ext_iff.mp key3_post)
  all_goals (try obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h23)
  all_goals subst_vars
  all_goals simp_all [consumeResponse, zeros32, Array.eq_iff, Array.from_slice_val, P.aead_length]

end

end wireguard.noise
