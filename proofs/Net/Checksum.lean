/- The Internet checksum (RFC 1071): the reference definition, and specs of
   `net::inet`. -/
import Net.Funs
import Untrusted

open Aeneas Aeneas.Std Result

namespace net.inet

/-! ## The reference definition

The data is read as big-endian 16-bit words, an odd final byte padded with a
zero byte, and the words are added with end-around carry. -/

/-- One's-complement addition of two 16-bit values: a carry out of bit 15 is
    added back in. -/
def add1c (a b : Nat) : Nat := if a + b < 65536 then a + b else a + b - 65535

/-- The big-endian 16-bit words of a byte string, the last byte padded with
    zero. -/
def words : List U8 → List Nat
  | a :: b :: t => (256 * a.val + b.val) :: words t
  | [a] => [256 * a.val]
  | [] => []

/-- The one's-complement sum of the words of `l`, starting from `acc`. A byte
    string with a correct checksum sums to `0xFFFF` from `0`. -/
def spec (acc : Nat) (l : List U8) : Nat := (words l).foldl add1c acc

/-- The worked IPv4 header example (its checksum is `0xB861`) sums to
    `0xFFFF`. -/
theorem spec_check :
    spec 0 [0x45#u8, 0x00#u8, 0x00#u8, 0x73#u8, 0x00#u8, 0x00#u8, 0x40#u8, 0x00#u8,
      0x40#u8, 0x11#u8, 0xb8#u8, 0x61#u8, 0xc0#u8, 0xa8#u8, 0x00#u8, 0x01#u8,
      0xc0#u8, 0xa8#u8, 0x00#u8, 0xc7#u8] = 0xFFFF := by
  decide +kernel

@[simp] theorem spec_nil (acc : Nat) : spec acc [] = acc := rfl

theorem spec_cons_cons (acc : Nat) (a b : U8) (t : List U8) :
    spec acc (a :: b :: t) = spec (add1c acc (256 * a.val + b.val)) t := rfl

theorem spec_single (acc : Nat) (a : U8) : spec acc [a] = add1c acc (256 * a.val) := rfl

theorem words_append (a b : List U8) (h : a.length % 2 = 0) :
    words (a ++ b) = words a ++ words b := by
  induction a using words.induct with
  | case1 x y t ih =>
    simp only [List.cons_append, words, List.cons_append, List.cons.injEq, true_and]
    exact ih (by simp at h; omega)
  | case2 x => simp at h
  | case3 => rfl

/-- Summing a byte string of even length, then the rest, is summing both. -/
theorem spec_append (acc : Nat) (a b : List U8) (h : a.length % 2 = 0) :
    spec acc (a ++ b) = spec (spec acc a) b := by
  simp only [spec, words_append a b h, List.foldl_append]

/-! ## Specs -/

@[simp, scalar_tac_simps] theorem VALID_val : VALID.val = 65535 := by simp [VALID]

/-- **Spec theorem for `net::inet::add`**: one's-complement addition. -/
@[step]
theorem add.spec (a b : U16) : add a b ⦃ (r : U16) => r.val = add1c a.val b.val ⦄ := by
  unfold add
  step*
  · simp only [add1c]; split <;> scalar_tac
  · simp only [add1c]; split <;> scalar_tac

/-- **Spec theorem for the loop of `net::inet::sum`**: adds the words from
    byte `i` on. -/
@[step]
theorem sum_loop.spec (data : Slice U8) (acc : U16) (i : Usize) (_hi : i.val ≤ data.length) :
    sum_loop data acc i ⦃ (r : U16) => r.val = spec acc.val (data.val.drop i.val) ⦄ := by
  unfold sum_loop
  dsimp only
  split
  · step*
    have h1 : i.val < data.val.length := by scalar_tac
    split
    · have h2 : i.val + 1 < data.val.length := by scalar_tac
      step as ⟨ b0, hb0 ⟩
      step as ⟨ c0, hc0 ⟩
      step as ⟨ t0, ht0 ⟩
      step as ⟨ j, hj ⟩
      step as ⟨ b1, hb1 ⟩
      step as ⟨ c1, hc1 ⟩
      step as ⟨ w, hw ⟩
      step as ⟨ i4, hi4 ⟩
      step as ⟨ acc1, hacc1 ⟩
      step as ⟨ r, hr ⟩
      have hc0' : c0.val = b0.val := by rw [hc0]; simp [UScalar.cast_val_eq]; scalar_tac
      have hc1' : c1.val = b1.val := by rw [hc1]; simp [UScalar.cast_val_eq]; scalar_tac
      rw [hr, hacc1, List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2,
        spec_cons_cons, show i4.val = i.val + 1 + 1 by scalar_tac, ← hb0,
        show (data.val)[i.val + 1] = b1 by rw [hb1]; simp [hj]]
      congr 2
      scalar_tac
    · step as ⟨ b0, hb0 ⟩
      step as ⟨ c0, hc0 ⟩
      step as ⟨ w, hw ⟩
      step as ⟨ i4, hi4 ⟩
      step as ⟨ acc1, hacc1 ⟩
      step as ⟨ r, hr ⟩
      have hc0' : c0.val = b0.val := by rw [hc0]; simp [UScalar.cast_val_eq]; scalar_tac
      have hd : data.val.drop i.val = [data.val[i.val]] := by
        rw [List.drop_eq_getElem_cons h1, List.drop_eq_nil_of_le (by scalar_tac)]
      have hd' : data.val.drop i4.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
      rw [hr, hacc1, hd, hd', spec_single, spec_nil, ← hb0]
      congr 1
      scalar_tac
  · simp only [WP.spec_ok]
    rw [List.drop_eq_nil_of_le (by scalar_tac), spec_nil]
termination_by data.length - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `net::inet::sum`**: adds the words of `data` to `acc`. -/
@[step]
theorem sum.spec (acc : U16) (data : Slice U8) :
    sum acc data ⦃ (r : U16) => r.val = spec acc.val data.val ⦄ := by
  unfold sum
  step*
  simpa using r_post

end net.inet
