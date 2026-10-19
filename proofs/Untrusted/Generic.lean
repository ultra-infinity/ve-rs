/- Generic models of the four kinds of integer conversion in `int.rs`, with
   their specs. Every generated `validate` for an integer pair is
   definitionally one of these models, so the concrete specs in
   `Untrusted/Proofs/Int.lean` are instances of the generic ones. -/
import Untrusted.Funs
import Untrusted.Spec

open Aeneas Aeneas.Std Result

namespace untrusted.generic

theorem IScalar.zero_inBounds (ty : IScalarTy) : IScalar.cMin ty ≤ 0 ∧ 0 ≤ IScalar.cMax ty := by
  cases ty <;> decide

/-- `unsigned → unsigned`: cast, cast back, compare. -/
def validateUU (src tgt : UScalarTy) (input : UScalar src) :
    Result (core.result.Result (UScalar tgt) ValidationError) := do
  let out ← lift (UScalar.cast tgt input)
  let i ← lift (UScalar.cast src out)
  if i = input
  then ok (core.result.Result.Ok out)
  else ok (core.result.Result.Err ValidationError.OutOfRange)

/-- `unsigned → signed`: also rejects results that became negative. -/
def validateUI (src : UScalarTy) (tgt : IScalarTy) (input : UScalar src) :
    Result (core.result.Result (IScalar tgt) ValidationError) := do
  let out ← lift (UScalar.hcast tgt input)
  if out >= IScalar.ofInt 0 (IScalar.zero_inBounds tgt)
  then
    let i ← lift (IScalar.hcast src out)
    if i = input
    then ok (core.result.Result.Ok out)
    else ok (core.result.Result.Err ValidationError.OutOfRange)
  else ok (core.result.Result.Err ValidationError.OutOfRange)

/-- `signed → unsigned`: rejects negative inputs up front. -/
def validateIU (src : IScalarTy) (tgt : UScalarTy) (input : IScalar src) :
    Result (core.result.Result (UScalar tgt) ValidationError) := do
  let out ← lift (IScalar.hcast tgt input)
  if input >= IScalar.ofInt 0 (IScalar.zero_inBounds src)
  then
    let i ← lift (UScalar.hcast src out)
    if i = input
    then ok (core.result.Result.Ok out)
    else ok (core.result.Result.Err ValidationError.OutOfRange)
  else ok (core.result.Result.Err ValidationError.OutOfRange)

/-- `signed → signed`: cast, cast back, compare. -/
def validateII (src tgt : IScalarTy) (input : IScalar src) :
    Result (core.result.Result (IScalar tgt) ValidationError) := do
  let out ← lift (IScalar.cast tgt input)
  let i ← lift (IScalar.cast src out)
  if i = input
  then ok (core.result.Result.Ok out)
  else ok (core.result.Result.Err ValidationError.OutOfRange)

/-! ## Arithmetic facts behind the round-trip checks -/

open Aeneas.Arith in
theorem bmod_pow2_bounds (n : Nat) (x : Int) :
    -2^(n-1) ≤ Int.bmod x (2^n) ∧ Int.bmod x (2^n) < 2^(n-1) :=
  Int.bmod_pow2_bounds n x

open Aeneas.Arith in
theorem bmod_pow2_eq (n : Nat) (x : Int) (hn : n ≠ 0)
    (h0 : -2^(n-1) ≤ x) (h1 : x < 2^(n-1)) : Int.bmod x (2^n) = x :=
  Int.bmod_pow2_eq_of_inBounds' n x hn h0 h1

theorem emod_le_self (y m : Int) (hy : 0 ≤ y) (hm : 0 < m) : y % m ≤ y := by
  rw [Int.emod_def]
  have := Int.mul_nonneg hm.le (Int.ediv_nonneg hy hm.le)
  scalar_tac

theorem IScalar.ofInt_zero_val (ty : IScalarTy) h : (IScalar.ofInt (ty := ty) 0 h).val = 0 := by
  simp

/-! ## Generic specs -/

/-- **Generic spec for `unsigned → unsigned` conversions** -/
theorem validateUU.spec (src tgt : UScalarTy) (input : UScalar src) :
    validateUU src tgt input ⦃ (r : core.result.Result (UScalar tgt) ValidationError) =>
      match r with
      | .Ok out => (out.val : Int) = input.val
      | .Err e => e = .OutOfRange ∧ ¬ UInRange tgt input.val ⦄ := by
  have hx := input.hBounds
  have hmax := UScalar.max_def tgt
  have : 0 < 2 ^ tgt.numBits := by positivity
  have hle := Nat.mod_le input.val (2 ^ tgt.numBits)
  simp only [validateUU, lift, bind_ok]
  split
  · rename_i h
    rw [UScalar.eq_equiv, UScalar.cast_val_eq, UScalar.cast_val_eq,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hx)] at h
    simp only [WP.spec_ok, UScalar.cast_val_eq, h]
  · rename_i h
    rw [UScalar.eq_equiv, UScalar.cast_val_eq, UScalar.cast_val_eq,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hx), Nat.mod_eq_iff_lt (by positivity)] at h
    simp only [WP.spec_ok, UInRange, true_and]
    scalar_tac

/-- **Generic spec for `unsigned → signed` conversions** -/
theorem validateUI.spec (src : UScalarTy) (tgt : IScalarTy) (input : UScalar src) :
    validateUI src tgt input ⦃ (r : core.result.Result (IScalar tgt) ValidationError) =>
      match r with
      | .Ok out => out.val = (input.val : Int)
      | .Err e => e = .OutOfRange ∧ ¬ IInRange tgt input.val ⦄ := by
  have hx := input.hBounds
  have hmin := IScalar.min_def tgt
  have hmax := IScalar.max_def tgt
  have hm := IScalarTy.numBits_nonzero tgt
  have hy := bmod_pow2_bounds tgt.numBits input.val
  have hsrc : (0 : Int) < 2 ^ src.numBits := by positivity
  /- In range, the value survives both casts. -/
  have key : IInRange tgt input.val →
      Int.bmod input.val (2 ^ tgt.numBits) = input.val := by
    intro ⟨h0, h1⟩
    apply bmod_pow2_eq _ _ hm <;> scalar_tac
  simp only [validateUI, lift, bind_ok, ge_iff_le, IScalar.le_equiv, IScalar.ofInt_zero_val,
    UScalar.hcast_val_eq]
  split
  · rename_i hpos
    split
    · rename_i h
      rw [UScalar.eq_equiv, IScalar.hcast_val_eq, UScalar.hcast_val_eq] at h
      simp only [WP.spec_ok, UScalar.hcast_val_eq]
      by_cases hr : IInRange tgt input.val
      · exact key hr
      · exfalso
        have hle := emod_le_self _ (2 ^ src.numBits) hpos hsrc
        have hnn := Int.emod_nonneg (Int.bmod input.val (2 ^ tgt.numBits)) hsrc.ne'
        simp only [IInRange, not_and_or, not_le] at hr
        generalize Int.bmod (input.val : Int) (2 ^ tgt.numBits) = y at *
        have h' := congrArg (fun n : Nat => (n : Int)) h
        simp only [Int.toNat_of_nonneg hnn] at h'
        clear key h hx
        scalar_tac
    · rename_i h
      simp only [WP.spec_ok, true_and]
      intro hr
      apply h
      rw [UScalar.eq_equiv, IScalar.hcast_val_eq, UScalar.hcast_val_eq, key hr,
        Int.emod_eq_of_lt (by scalar_tac) (by scalar_tac)]
      simp
  · rename_i hneg
    simp only [WP.spec_ok, true_and]
    intro hr
    rw [key hr] at hneg
    scalar_tac

/-- **Generic spec for `signed → unsigned` conversions** -/
theorem validateIU.spec (src : IScalarTy) (tgt : UScalarTy) (input : IScalar src) :
    validateIU src tgt input ⦃ (r : core.result.Result (UScalar tgt) ValidationError) =>
      match r with
      | .Ok out => (out.val : Int) = input.val
      | .Err e => e = .OutOfRange ∧ ¬ UInRange tgt input.val ⦄ := by
  have hx := input.hBounds
  have hmax := UScalar.max_def tgt
  have hn := IScalarTy.numBits_nonzero src
  have : (0 : Int) < 2 ^ tgt.numBits := by positivity
  /- In range, the value survives both casts. -/
  have key : UInRange tgt input.val →
      ((input.val % 2 ^ tgt.numBits).toNat : Int) = input.val := by
    intro ⟨h0, h1⟩
    rw [Int.emod_eq_of_lt h0 (by scalar_tac), Int.toNat_of_nonneg h0]
  simp only [validateIU, lift, bind_ok, ge_iff_le, IScalar.le_equiv, IScalar.ofInt_zero_val]
  split
  · rename_i hpos
    have hlt := Int.emod_lt_of_pos input.val this
    have hnn := Int.emod_nonneg input.val this.ne'
    split
    · rename_i h
      rw [IScalar.eq_equiv, UScalar.hcast_val_eq, IScalar.hcast_val_eq,
        Int.toNat_of_nonneg hnn] at h
      simp only [WP.spec_ok, IScalar.hcast_val_eq, Int.toNat_of_nonneg hnn]
      by_cases hr : UInRange tgt input.val
      · simpa [Int.toNat_of_nonneg hnn] using key hr
      · exfalso
        simp only [UInRange, not_and_or, not_le] at hr
        have : (0 : Int) < 2 ^ (src.numBits - 1) := by positivity
        rw [bmod_pow2_eq src.numBits (input.val % 2 ^ tgt.numBits) hn (by scalar_tac)
          (by scalar_tac)] at h
        scalar_tac
    · rename_i h
      simp only [WP.spec_ok, true_and]
      intro hr
      apply h
      rw [IScalar.eq_equiv, UScalar.hcast_val_eq, IScalar.hcast_val_eq, key hr]
      exact bmod_pow2_eq _ _ hn hx.1 hx.2
  · rename_i hneg
    simp only [WP.spec_ok, true_and, UInRange]
    scalar_tac

/-- **Generic spec for `signed → signed` conversions** -/
theorem validateII.spec (src tgt : IScalarTy) (input : IScalar src) :
    validateII src tgt input ⦃ (r : core.result.Result (IScalar tgt) ValidationError) =>
      match r with
      | .Ok out => out.val = input.val
      | .Err e => e = .OutOfRange ∧ ¬ IInRange tgt input.val ⦄ := by
  have hx := input.hBounds
  have hmin := IScalar.min_def tgt
  have hmax := IScalar.max_def tgt
  have hout := (IScalar.cast tgt input).hBounds
  /- In range, the value survives both casts. -/
  have key : IInRange tgt input.val → (IScalar.cast tgt input).val = input.val := by
    intro ⟨h0, h1⟩
    apply IScalar.val_mod_pow_inBounds <;> scalar_tac
  have back : (IScalar.cast src (IScalar.cast tgt input)).val = input.val →
      IInRange tgt input.val := by
    intro h
    by_contra hr
    simp only [IInRange, not_and_or, not_le] at hr
    rw [IScalar.val_mod_pow_inBounds _ _ (by scalar_tac) (by scalar_tac)] at h
    scalar_tac
  simp only [validateII, lift, bind_ok]
  split
  · rename_i h
    rw [IScalar.eq_equiv] at h
    simp only [WP.spec_ok]
    exact key (back h)
  · rename_i h
    simp only [WP.spec_ok, true_and]
    intro hr
    apply h
    rw [IScalar.eq_equiv, IScalar.val_mod_pow_inBounds _ _ (by scalar_tac) (by scalar_tac), key hr]

end untrusted.generic
