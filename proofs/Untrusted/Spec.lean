/- Specification vocabulary used by the theorems in `Untrusted/Proofs/`, and
   pure lemmas about it. Nothing here mentions the generated model. -/
import Aeneas

open Aeneas Aeneas.Std

namespace untrusted

/-! ## Integer ranges -/

/-- `v` is representable in the unsigned integer type `ty`. -/
def UInRange (ty : UScalarTy) (v : Int) : Prop := 0 ≤ v ∧ v ≤ (UScalar.max ty : Int)

/-- `v` is representable in the signed integer type `ty`. -/
def IInRange (ty : IScalarTy) (v : Int) : Prop := IScalar.min ty ≤ v ∧ v ≤ IScalar.max ty

/-! ## Byte strings -/

/-- The number denoted by a big-endian byte string. -/
def beNat (l : List U8) : Nat := l.foldl (fun acc b => acc * 256 + b.val) 0

/-- The number denoted by a little-endian byte string. -/
def leNat (l : List U8) : Nat := beNat l.reverse

@[simp] theorem beNat_nil : beNat [] = 0 := rfl

theorem beNat_append_singleton (l : List U8) (b : U8) :
    beNat (l ++ [b]) = beNat l * 256 + b.val := by
  simp [beNat, List.foldl_append]

theorem beNat_singleton (l : List U8) (h : l.length = 1) : beNat l = (l[0]'(by simp [h])).val := by
  match l, h with
  | [b], _ => simp [beNat]

theorem leNat_singleton (l : List U8) (h : l.length = 1) : leNat l = (l[0]'(by simp [h])).val := by
  match l, h with
  | [b], _ => simp [leNat, beNat]

theorem beNat_lt (l : List U8) : beNat l < 256 ^ l.length := by
  induction l using List.reverseRecOn
  · simp
  · rename_i l b ih
    rw [beNat_append_singleton, List.length_append, List.length_singleton, Nat.pow_succ]
    scalar_tac

theorem beNat_mul_lt (l : List U8) (n : Nat) (h : l.length < n) :
    beNat l * 256 < 256 ^ n := by
  have h1 := beNat_lt l
  have h2 : 256 ^ (l.length + 1) ≤ 256 ^ n := Nat.pow_le_pow_right (by decide) h
  rw [Nat.pow_succ] at h2
  scalar_tac

/-- The prefix of length `i + 1` is the prefix of length `i` followed by the byte at `i`. -/
theorem beNat_take_succ (l : List U8) (i : Nat) (h : i < l.length) :
    beNat (l.take (i + 1)) = beNat (l.take i) * 256 + l[i].val := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, beNat_append_singleton]

/-- The reversed suffix from `j` is the reversed suffix from `j + 1` followed by the byte at `j`. -/
theorem beNat_drop (l : List U8) (j : Nat) (h : j < l.length) :
    beNat (l.drop j).reverse = beNat (l.drop (j + 1)).reverse * 256 + l[j].val := by
  rw [List.drop_eq_getElem_cons h, List.reverse_cons, beNat_append_singleton]

/-- Shifting `a` left by one byte (modulo `M`) and or-ing in a byte `b` appends `b`. -/
theorem shl8_or (a b M : Nat) (hb : b < 256) (ha : a * 256 < M) :
    (a <<< 8 % M) ||| b = a * 256 + b := by
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by simpa using ha)]
  have := Nat.shiftLeft_add_eq_or_of_lt (i := 8) (show b < 2 ^ 8 by simpa using hb) a
  rw [Nat.shiftLeft_eq] at this
  simpa using this.symm

end untrusted
