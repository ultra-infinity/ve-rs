/- Specs of `wireguard::replay`: the sliding replay window accepts a counter
   exactly when it is below `REJECT_AFTER_MESSAGES`, at most `WINDOW` behind
   the largest accepted, and not accepted before.

   The window is described by the set `S` of accepted counters. `Holds` says
   what the bitmap means: with `t` one more than the largest accepted
   counter, the bit at position `v mod 8192` tells whether the counter
   `v - 1` was accepted, for every `v` in the last 128 words below `t`. -/
import Wireguard.Funs
import Untrusted

open Aeneas Aeneas.Std Result

namespace wireguard.replay

/-! ## The meaning of the bitmap -/

/-- Counters at or above this are never accepted: `2^64 - 2^13 - 1`. -/
def REJECT : Nat := 18446744073709543423

/-- The bitmap, read as bits: `bit t bit S` holds when `bit (v mod 8192)` says
    whether `v - 1 ∈ S`, for each `v` in the 128 words up to `t`'s, and every
    counter in `S` is below `t`. -/
def Holds (t : Nat) (bit : Nat → Bool) (S : Set Nat) : Prop :=
  (∀ c ∈ S, c + 1 ≤ t) ∧
  ∀ v, t / 64 ≤ v / 64 + 127 → v / 64 ≤ t / 64 →
    (bit (v % 8192) = true ↔ 1 ≤ v ∧ v ≤ t ∧ v - 1 ∈ S)

/-- Two counters in the same 128 words with the same position are equal. -/
theorem pos_unique {t v v' : Nat} (h1 : t / 64 ≤ v / 64 + 127) (h2 : v / 64 ≤ t / 64)
    (h1' : t / 64 ≤ v' / 64 + 127) (h2' : v' / 64 ≤ t / 64) (h : v % 8192 = v' % 8192) :
    v = v' := by
  omega

/-- Whether the counter `v - 1`, recent enough, was accepted. -/
theorem Holds.seen {t : Nat} {bit : Nat → Bool} {S : Set Nat} (hh : Holds t bit S) {v : Nat}
    (h1 : 1 ≤ v) (hv : v ≤ t) (hw : t ≤ v + 8128) :
    bit (v % 8192) = true ↔ v - 1 ∈ S := by
  rw [hh.2 v (by omega) (by omega)]
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨h1, hv, h⟩

open Classical in
/-- Moving the top forward to `v`, after clearing the words in between
    (`clear w` for the `n` words after `t`'s, all of them at most). -/
theorem Holds.advance {t : Nat} {bit : Nat → Bool} {S : Set Nat} (hh : Holds t bit S) {v n : Nat}
    (hv : t < v) (hn : n = min (v / 64 - t / 64) 128) :
    Holds v (fun p => if ∃ k, 1 ≤ k ∧ k ≤ n ∧ (t / 64 + k) % 128 = p / 64 then false else bit p) S := by
  refine ⟨fun c hc => by have := hh.1 c hc; omega, ?_⟩
  intro v' h1 h2
  by_cases hw : v' / 64 ≤ t / 64
  · -- An old word: not cleared, and it still means what it meant.
    have hnc : ¬ ∃ k, 1 ≤ k ∧ k ≤ n ∧ (t / 64 + k) % 128 = v' % 8192 / 64 := by
      rintro ⟨k, hk1, hk2, hk⟩; omega
    simp only [hnc, ↓reduceIte]
    rw [hh.2 v' (by omega) hw]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨a, by omega, c⟩
    · rintro ⟨a, -, c⟩; exact ⟨a, by have := hh.1 _ c; omega, c⟩
  · -- A new word: cleared, and no counter there was accepted.
    have hc : ∃ k, 1 ≤ k ∧ k ≤ n ∧ (t / 64 + k) % 128 = v' % 8192 / 64 :=
      ⟨(v' / 64 - t / 64 - 1) % 128 + 1, by omega, by omega, by omega⟩
    simp only [hc, ↓reduceIte, Bool.false_eq_true, false_iff, not_and]
    intro _ _ hs
    have := hh.1 _ hs
    omega

/-- Setting the bit of the counter `v - 1` accepts it. -/
theorem Holds.set {t : Nat} {bit : Nat → Bool} {S : Set Nat} (hh : Holds t bit S) {v : Nat}
    (h1 : 1 ≤ v) (hv : v ≤ t) (hw : t ≤ v + 8128) :
    Holds t (fun p => bit p || decide (p = v % 8192)) (insert (v - 1) S) := by
  refine ⟨?_, ?_⟩
  · rintro c (rfl | hc)
    · omega
    · exact hh.1 c hc
  · intro v' h1' h2'
    simp only [Bool.or_eq_true, decide_eq_true_eq, Set.mem_insert_iff]
    by_cases he : v' % 8192 = v % 8192
    · have := pos_unique h1' h2' (by omega) (by omega) he
      subst this
      simp only [he, or_true, true_iff]
      exact ⟨h1, hv, by simp⟩
    · simp only [he, or_false]
      rw [hh.2 v' h1' h2']
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨a, b, Or.inr c⟩
      · rintro ⟨a, b, e | c⟩
        · exact absurd (by omega : v' % 8192 = v % 8192) he
        · exact ⟨a, b, c⟩

/-! ## The bitmap as bits -/

/-- Bit `p` (below 8192) of the bitmap: bit `p mod 64` of word `p / 64`. -/
def bitAt (bm : Array U64 128#usize) (p : Nat) : Bool := (bm.val[p / 64]!).val.testBit (p % 64)

/-- The invariant of a window: it means the set `S` of accepted counters. -/
def Replay.Inv (r : Replay) (S : Set Nat) : Prop :=
  r.top.val ≤ REJECT ∧ Holds r.top.val (bitAt r.bitmap) S

theorem getElem!_set (l : List U64) (i j : Nat) (x : U64) (hi : i < l.length) :
    (l.set i x)[j]! = if i = j then x else l[j]! := by
  by_cases h : i = j
  · subst h; simp [hi]
  · simp [h]

theorem and_two_pow_ne_zero (x s : Nat) : x &&& 2 ^ s ≠ 0 ↔ x.testBit s = true := by
  constructor
  · intro h; by_contra hb; apply h; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : s = i
    · subst hi; simpa using hb
    · simp [hi]
  · intro h hz
    have := congrArg (fun n => n.testBit s) hz
    simp [Nat.testBit_and, h] at this

theorem testBit_or_two_pow (x s j : Nat) :
    (x ||| 2 ^ s).testBit j = (x.testBit j || decide (s = j)) := by
  simp [Nat.testBit_or, Nat.testBit_two_pow]

/-- Setting the bit of `v` in its word. -/
theorem bitAt_set_or (a : Array U64 128#usize) (v : Nat) (w : Usize) (z : U64)
    (hw : w.val = v / 64 % 128) (hz : z.val = (a.val[w.val]!).val ||| 2 ^ (v % 64)) (p : Nat)
    (hp : p < 8192) :
    bitAt (a.set w z) p = (bitAt a p || decide (p = v % 8192)) := by
  have hl : w.val < a.val.length := by simp; omega
  simp only [bitAt, Array.set_val_eq, getElem!_set _ _ _ _ hl]
  by_cases h : w.val = p / 64
  · simp only [h, ↓reduceIte, hz, testBit_or_two_pow]
    rw [← h]
    congr 1
    simp only [decide_eq_decide]
    omega
  · have hne : p ≠ v % 8192 := by omega
    simp [h, hne]

/-! ## Specs -/

@[simp, scalar_tac_simps] theorem REJECT_eq : REJECT = 18446744073709543423 := rfl

@[simp, scalar_tac_simps] theorem REJECT_AFTER_MESSAGES_val : REJECT_AFTER_MESSAGES.val = REJECT := by
  simp [REJECT_AFTER_MESSAGES, REJECT]
@[simp, scalar_tac_simps] theorem WINDOW_val : WINDOW.val = 8128 := by simp [WINDOW]
@[simp, scalar_tac_simps] theorem WORDS_val : WORDS.val = 128 := by simp [WORDS]

open Classical in
/-- **Spec theorem for the clearing loop of `check_and_update`**: zeroes the
    words `(current + k) mod 128` for `k` from `i` to `n`. -/
@[step]
theorem Replay.check_and_update_loop.spec (a : Array U64 128#usize) (current n i : U64)
    (hi : 1 ≤ i.val) (hin : i.val ≤ n.val + 1) (hn : n.val ≤ 128) (hc : current.val ≤ 2 ^ 63) :
    Replay.check_and_update_loop a current n i ⦃ (a' : Array U64 128#usize) =>
      ∀ j < 128, a'.val[j]! =
        if ∃ k, i.val ≤ k ∧ k ≤ n.val ∧ (current.val + k) % 128 = j then 0#u64 else a.val[j]! ⦄ := by
  unfold Replay.check_and_update_loop
  split
  · step*
    all_goals
      have hi3 : i3.val = (current.val + i.val) % 128 := by
        rw [i3_post, UScalar.cast_val_eq, i2_post, i1_post]
        apply Nat.mod_eq_of_lt
        rcases System.Platform.numBits_eq with h | h <;>
          simp only [UScalarTy.Usize_numBits_eq, h] <;> omega
    · simp; omega
    · have hlt : i3.val < a.val.length := by simp; omega
      rw [a'_post j j_post, a1_post, Array.set_val_eq, getElem!_set _ _ _ _ hlt, hi3, i4_post]
      by_cases h1 : ∃ k, i.val + 1 ≤ k ∧ k ≤ n.val ∧ (current.val + k) % 128 = j
      · have h2 : ∃ k, i.val ≤ k ∧ k ≤ n.val ∧ (current.val + k) % 128 = j :=
          let ⟨k, a, b, c⟩ := h1; ⟨k, by omega, b, c⟩
        rw [if_pos h1, if_pos h2]
      · by_cases h3 : (current.val + i.val) % 128 = j
        · have h2 : ∃ k, i.val ≤ k ∧ k ≤ n.val ∧ (current.val + k) % 128 = j :=
            ⟨i.val, le_refl _, by scalar_tac, h3⟩
          rw [if_neg h1, if_pos h3, if_pos h2]
        · have h2 : ¬ ∃ k, i.val ≤ k ∧ k ≤ n.val ∧ (current.val + k) % 128 = j := by
            rintro ⟨k, a, b, c⟩
            rcases Nat.eq_or_lt_of_le a with e | e
            · exact h3 (e ▸ c)
            · exact h1 ⟨k, by omega, b, c⟩
          rw [if_neg h1, if_neg h3, if_neg h2]
  · simp only [WP.spec_ok]
    intro j hj
    have : ¬ ∃ k, i.val ≤ k ∧ k ≤ n.val ∧ (current.val + k) % 128 = j := by
      rintro ⟨k, h1, h2, -⟩; scalar_tac
    simp [this]
termination_by n.val + 1 - i.val
decreasing_by all_goals scalar_tac

/-- The bit test of `check_and_update`: `x &&& (1 << (v % 64)) != 0`, on the
    word of `v`, reads the bit of `v`. -/
theorem test_bit (a : Array U64 128#usize) (v : Nat) (w : Usize) (bit x : U64)
    (hw : w.val = v / 64 % 128) (hbit : bit.val = 2 ^ (v % 64)) (hx : x = a.val[w.val]!) :
    ((x &&& bit) != 0#u64) = bitAt a (v % 8192) := by
  have hiff : (x &&& bit) ≠ 0#u64 ↔ bitAt a (v % 8192) = true := by
    have h0 : (0#u64 : U64).val = 0 := by simp
    rw [ne_eq, UScalar.eq_equiv, UScalar.val_and, hbit, h0, ← ne_eq, and_two_pow_ne_zero]
    simp only [bitAt, hx, hw]
    rw [show v % 8192 / 64 = v / 64 % 128 by omega, show v % 8192 % 64 = v % 64 by omega]
  by_cases h : bitAt a (v % 8192) = true
  · simp [hiff.mpr h, h]
  · simp only [Bool.not_eq_true] at h
    have : x &&& bit = 0#u64 := by by_contra hne; exact absurd (hiff.mp hne) (by simp [h])
    simp [this, h]

/-- `Holds` only reads the positions below 8192. -/
theorem Holds.congr {t : Nat} {bit bit' : Nat → Bool} {S : Set Nat} (hh : Holds t bit S)
    (h : ∀ p < 8192, bit p = bit' p) : Holds t bit' S :=
  ⟨hh.1, fun v h1 h2 => by rw [← h (v % 8192) (by omega)]; exact hh.2 v h1 h2⟩

open Classical in
/-- The bitmap after the clearing loop, as bits. -/
theorem cleared_bits (a a' : Array U64 128#usize) (current n : Nat)
    (h : ∀ j < 128, a'.val[j]! =
      if ∃ k, 1 ≤ k ∧ k ≤ n ∧ (current + k) % 128 = j then 0#u64 else a.val[j]!) (p : Nat)
    (hp : p < 8192) :
    bitAt a' p = if ∃ k, 1 ≤ k ∧ k ≤ n ∧ (current + k) % 128 = p / 64 then false else bitAt a p := by
  simp only [bitAt, h (p / 64) (by omega)]
  split <;> simp

/-- `1 << s` is `2^s`, for `s < 64`. -/
theorem shift_one (s z : U64) (hs : s.val < 64) (hz : z.val = (1 <<< s.val) % U64.size) :
    z.val = 2 ^ s.val := by
  rw [hz, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
  simp only [U64.size, U64.numBits]
  exact Nat.pow_lt_pow_right (by omega) hs

/-- **Spec theorem for `Replay::check_and_update`**: accepts `c` exactly when
    it is below `REJECT_AFTER_MESSAGES`, at most `WINDOW` behind the largest
    accepted counter, and not accepted before; it is then recorded. -/
@[step]
theorem Replay.check_and_update.spec (r : Replay) (S : Set Nat) (hinv : r.Inv S) (c : U64) :
    Replay.check_and_update r c ⦃ (b : Bool) (r' : Replay) =>
      (b = true ↔ c.val < REJECT ∧ r.top.val ≤ c.val + 1 + 8128 ∧ c.val ∉ S) ∧
        r'.Inv (if b then insert c.val S else S) ⦄ := by
  obtain ⟨htop, hh⟩ := hinv
  unfold Replay.check_and_update
  split
  · simp only [WP.spec_ok]
    constructor
    · simp only [Bool.false_eq_true, false_iff, not_and]; intro h; scalar_tac
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨htop, hh⟩
  · have hc : c.val < REJECT := by scalar_tac
    step as ⟨ v, hv ⟩
    step as ⟨ i, hi ⟩
    split
    · simp only [WP.spec_ok]
      constructor
      · simp only [Bool.false_eq_true, false_iff, not_and]; intro _ h; scalar_tac
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨htop, hh⟩
    · have hwin : r.top.val ≤ v.val + 8128 := by scalar_tac
      split
      · have hgt : r.top.val < v.val := by scalar_tac
        step as ⟨ current, hcur ⟩
        step as ⟨ index, hidx ⟩
        step as ⟨ i1, hi1, hi1' ⟩
        step as ⟨ i2, hi2 ⟩
        obtain ⟨n, hn_eq, hnv⟩ : ∃ n : U64,
            (if i1 > i2 then ok (UScalar.cast .U64 WORDS) else ok i1 : Result U64) = ok n ∧
              n.val = min (v.val / 64 - r.top.val / 64) 128 := by
          have hi2v : i2.val = 128 := by rw [hi2]; simp [UScalar.cast_val_eq]
          split
          · exact ⟨_, rfl, by simp [UScalar.cast_val_eq]; scalar_tac⟩
          · exact ⟨_, rfl, by scalar_tac⟩
        rw [hn_eq, bind_ok]
        step as ⟨ a, ha ⟩
        have hbits : Holds v.val (bitAt a) S := by
          apply (hh.advance hgt hnv).congr
          intro p hp
          rw [cleared_bits r.bitmap a current.val n.val ha p hp, hcur]
        step as ⟨ i3, hi3 ⟩
        step as ⟨ i4, hi4 ⟩
        step as ⟨ w, hw ⟩
        have hwv : w.val = v.val / 64 % 128 := by
          rw [hw, UScalar.cast_val_eq, hi4, hi3]
          apply Nat.mod_eq_of_lt
          rcases System.Platform.numBits_eq with h | h <;>
            simp only [UScalarTy.Usize_numBits_eq, h] <;> omega
        step as ⟨ i5, hi5 ⟩
        step as ⟨ bit, hbit, hbit' ⟩
        step as ⟨ i6, hi6 ⟩
        step as ⟨ i7, hi7, hi7' ⟩
        have hbv : bit.val = 2 ^ (v.val % 64) := by
          rw [shift_one i5 bit (by scalar_tac) hbit, hi5]
        have htest := test_bit a v.val w bit i6 hwv hbv
          (by rw [hi6]; simp; rw [List.getElem?_eq_getElem (by simp; omega)]; rfl)
        have hi7e : i7 = i6 &&& bit := (UScalar.eq_equiv _ _).mpr hi7
        rw [hi7e, htest]
        have hseen := hbits.seen (v := v.val) (by omega) le_rfl (by omega)
        split
        · rename_i hset
          simp only [WP.spec_ok]
          constructor
          · simp only [Bool.false_eq_true, false_iff, not_and]
            intro _ _ hnot
            apply hnot
            have := hseen.mp hset
            rwa [show v.val - 1 = c.val by omega] at this
          · try simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨by scalar_tac, hbits⟩
        · rename_i hclr
          step as ⟨ i8, hi8, hi8' ⟩
          step as ⟨ a1, ha1 ⟩
          try simp only [WP.spec_ok]
          constructor
          · try simp only [true_iff]
            refine ⟨hc, by omega, fun hcS => hclr ?_⟩
            exact hseen.mpr (by rwa [show v.val - 1 = c.val by omega])
          · simp only [↓reduceIte]
            refine ⟨by scalar_tac, ?_⟩
            have hs := hbits.set (v := v.val) (by omega) le_rfl (by omega)
            rw [show v.val - 1 = c.val by omega] at hs
            apply hs.congr
            intro p hp
            rw [ha1, bitAt_set_or a v.val w i8 hwv
              (by simp [hi8, hbv, hi6]; rw [List.getElem?_eq_getElem (by simp; omega)]; rfl) p hp]
      · have hbits := hh
        have hle : v.val ≤ r.top.val := by scalar_tac
        step as ⟨ i3, hi3 ⟩
        step as ⟨ i4, hi4 ⟩
        step as ⟨ w, hw ⟩
        have hwv : w.val = v.val / 64 % 128 := by
          rw [hw, UScalar.cast_val_eq, hi4, hi3]
          apply Nat.mod_eq_of_lt
          rcases System.Platform.numBits_eq with h | h <;>
            simp only [UScalarTy.Usize_numBits_eq, h] <;> omega
        step as ⟨ i5, hi5 ⟩
        step as ⟨ bit, hbit, hbit' ⟩
        step as ⟨ i6, hi6 ⟩
        step as ⟨ i7, hi7, hi7' ⟩
        have hbv : bit.val = 2 ^ (v.val % 64) := by
          rw [shift_one i5 bit (by scalar_tac) hbit, hi5]
        have htest := test_bit r.bitmap v.val w bit i6 hwv hbv
          (by rw [hi6]; simp; rw [List.getElem?_eq_getElem (by simp; omega)]; rfl)
        have hi7e : i7 = i6 &&& bit := (UScalar.eq_equiv _ _).mpr hi7
        rw [hi7e, htest]
        have hseen := hbits.seen (v := v.val) (by omega) (by scalar_tac) (by omega)
        split
        · rename_i hset
          simp only [WP.spec_ok]
          constructor
          · simp only [Bool.false_eq_true, false_iff, not_and]
            intro _ _ hnot
            apply hnot
            have := hseen.mp hset
            rwa [show v.val - 1 = c.val by omega] at this
          · try simp only [Bool.false_eq_true, ↓reduceIte]
            exact ⟨by scalar_tac, hbits⟩
        · rename_i hclr
          step as ⟨ i8, hi8, hi8' ⟩
          step as ⟨ a1, ha1 ⟩
          try simp only [WP.spec_ok]
          constructor
          · try simp only [true_iff]
            refine ⟨hc, by omega, fun hcS => hclr ?_⟩
            exact hseen.mpr (by rwa [show v.val - 1 = c.val by omega])
          · simp only [↓reduceIte]
            refine ⟨by scalar_tac, ?_⟩
            have hs := hbits.set (v := v.val) (by omega) (by scalar_tac) (by omega)
            rw [show v.val - 1 = c.val by omega] at hs
            apply hs.congr
            intro p hp
            rw [ha1, bitAt_set_or r.bitmap v.val w i8 hwv
              (by simp [hi8, hbv, hi6]; rw [List.getElem?_eq_getElem (by simp; omega)]; rfl) p hp]


/-- The empty window means the empty set. -/
theorem empty_inv : Replay.Inv { top := 0#u64, bitmap := Array.repeat 128#usize 0#u64 } ∅ := by
  refine ⟨by simp [REJECT], fun c hc => absurd hc (Set.notMem_empty c), ?_⟩
  intro v _ _
  have h0 : (Array.repeat 128#usize 0#u64).val[v % 8192 / 64]! = 0#u64 := by
    rw [Array.repeat_val]
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  simp only [bitAt]
  rw [h0]
  simp

/-- **Spec theorem for `Replay::new`**: a window that has seen nothing. -/
@[step]
theorem Replay.new.spec : Replay.new ⦃ (r : Replay) => r.Inv ∅ ⦄ := by
  unfold Replay.new
  simpa using empty_inv

/-- **Spec theorem for `<Replay as Default>::default`**. -/
@[step]
theorem Replay.Insts.CoreDefaultDefault.default.spec :
    Replay.Insts.CoreDefaultDefault.default ⦃ (r : Replay) => r.Inv ∅ ⦄ := by
  unfold Replay.Insts.CoreDefaultDefault.default
  step*

/-- **No replays.** Once a counter is accepted, the window never accepts it
    again (here, right after; `check_and_update.spec` keeps it in the set of
    accepted counters from then on). -/
theorem no_replay (r : Replay) (S : Set Nat) (hinv : r.Inv S) (c : U64) :
    Replay.check_and_update r c ⦃ (b : Bool) (r' : Replay) =>
      b = true → Replay.check_and_update r' c ⦃ (b' : Bool) (_ : Replay) => b' = false ⦄ ⦄ := by
  apply WP.spec_mono (Replay.check_and_update.spec r S hinv c)
  rintro ⟨b, r'⟩ ⟨-, hinv'⟩ hb
  simp only [hb, ↓reduceIte] at hinv'
  apply WP.spec_mono (Replay.check_and_update.spec r' _ hinv' c)
  rintro ⟨b', -⟩ ⟨hiff, -⟩
  revert hiff
  cases b' <;> simp

end wireguard.replay
