/- CRC-32 (IEEE 802.3): the reference definition, and specs of `net::crc32`. -/
import Net.Funs
import Untrusted

open Aeneas Aeneas.Std Result

-- The Rust function `net::crc32::crc32` repeats its module's name.
set_option linter.dupNamespace false

namespace net.crc32

/-! ## The reference definition

The reflected CRC-32 of IEEE 802.3 (CRC-32/ISO-HDLC): the register starts at
all ones, each byte is XORed into its low end and shifted out least significant
bit first through the polynomial `0xEDB88320`, and the result is complemented. -/

/-- One shift of the register. -/
def step (c : BitVec 32) : BitVec 32 :=
  if c &&& 1#32 = 1#32 then (c >>> 1) ^^^ 0xEDB88320#32 else c >>> 1

/-- Feeds one byte into the register. -/
def feed (c : BitVec 32) (b : U8) : BitVec 32 := step^[8] (c ^^^ b.bv.setWidth 32)

/-- The CRC-32 of a byte string. -/
def spec (l : List U8) : BitVec 32 := ~~~ (l.foldl feed 0xFFFFFFFF#32)

/-- The standard check value: the CRC-32 of the ASCII string `"123456789"`. -/
theorem spec_check :
    spec [49#u8, 50#u8, 51#u8, 52#u8, 53#u8, 54#u8, 55#u8, 56#u8, 57#u8] = 0xCBF43926#32 := by
  decide +kernel

@[simp, scalar_tac_simps, bvify] theorem POLY_bv : POLY.bv = 0xEDB88320#32 := by
  simp [POLY]

/-! ## Specs -/

/-- **Spec theorem for the shift loop of `net::crc32::update`**: the `8 - k`
    remaining shifts. -/
@[step]
theorem update_loop.spec (c : U32) (k : I32) (h0 : 0 ≤ k.val) (h8 : k.val ≤ 8) :
    update_loop c k ⦃ (r : U32) => r.bv = step^[(8 - k.val).toNat] c.bv ⦄ := by
  unfold update_loop
  split
  · step as ⟨ i, _, i_bv ⟩
    split
    · rename_i hi
      step*
      have hlow : c.bv &&& 1#32 = 1#32 := by
        rw [hi] at i_bv
        simpa using i_bv.symm
      have hs : step c.bv = (x ^^^ POLY).bv := by
        simp [step, hlow, x_post1]
      have hn : (8 - k.val).toNat = (8 - k1.val).toNat + 1 := by scalar_tac
      rw [hn, Function.iterate_succ_apply, hs, r_post]
    · rename_i hi
      step*
      have hlow : c.bv &&& 1#32 ≠ 1#32 := by
        intro h
        apply hi
        apply (UScalar.eq_equiv_bv_eq _ _).mpr
        rw [i_bv]
        simpa using h
      have hs : step c.bv = c1.bv := by
        simp [step, hlow, c1_post1]
      have hn : (8 - k.val).toNat = (8 - k1.val).toNat + 1 := by scalar_tac
      rw [hn, Function.iterate_succ_apply, hs, r_post]
  · simp only [WP.spec_ok]
    have : (8 - k.val).toNat = 0 := by scalar_tac
    simp [this]
termination_by (8 - k.val).toNat
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `net::crc32::update`**: feeds one byte. -/
@[step]
theorem update.spec (crc : U32) (byte : U8) :
    update crc byte ⦃ (r : U32) => r.bv = feed crc.bv byte ⦄ := by
  unfold update
  step*
  simp [r_post, c_post1, i_post, feed]

/-- **Spec theorem for the byte loop of `net::crc32::crc32`**: feeds the bytes
    from `i` on. -/
@[step]
theorem crc32_loop.spec (data : Slice U8) (crc : U32) (i : Usize) (hi : i.val ≤ data.length) :
    crc32_loop data crc i ⦃ (r : U32) => r.bv = (data.val.drop i.val).foldl feed crc.bv ⦄ := by
  unfold crc32_loop
  dsimp only
  split
  · step*
    have hlt : i.val < data.val.length := by scalar_tac
    rw [r_post, crc1_post, show i3.val = i.val + 1 by scalar_tac,
      List.drop_eq_getElem_cons hlt, List.foldl_cons, i2_post]
  · simp only [WP.spec_ok]
    rw [List.drop_eq_nil_of_le (by scalar_tac), List.foldl_nil]
termination_by data.length - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `net::crc32::crc32`**: the CRC-32 of `data`. -/
@[step]
theorem crc32.spec (data : Slice U8) :
    crc32 data ⦃ (r : U32) => r.bv = spec data.val ⦄ := by
  unfold crc32
  step*
  simp only [net.crc32.spec, crc_post, List.drop_zero, UScalar.bv_not]
  rfl

end net.crc32
