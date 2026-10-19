/- Facts about byte positions shared by the specs of the `net` crate. -/
import Untrusted

open Aeneas Aeneas.Std untrusted

namespace net

/-- The big-endian value of the byte at position `i`. -/
theorem beNat_take1_drop (l : List U8) (i : Nat) (h : i < l.length) :
    beNat ((l.drop i).take 1) = l[i].val := by
  rw [List.drop_eq_getElem_cons h]
  simp only [beNat, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  omega

/-- The big-endian value of the two bytes at position `i`. -/
theorem beNat_take2_drop (l : List U8) (i : Nat) (h : i + 1 < l.length) :
    beNat ((l.drop i).take 2) = l[i].val * 256 + l[i + 1].val := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h]
  simp only [beNat, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  omega

theorem beNat_take1 (l : List U8) (h : 0 < l.length) : beNat (l.take 1) = l[0].val := by
  simpa using beNat_take1_drop l 0 h

end net
