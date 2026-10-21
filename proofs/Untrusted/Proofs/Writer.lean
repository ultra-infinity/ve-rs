/- Specs of `untrusted::writer`: the writer's methods, and the bytes the
   integer encoders write.

   Every method of `Writer` returns, besides its result and the new writer, a
   backward function, Aeneas's model of handing the `&mut [u8]` the writer
   holds back to its owner: it puts the final output back into the original
   writer. `Writes w e res w' back` says what a method that writes the bytes
   `e` does: on success the output is `w`'s with `e` at its position, on
   failure there was no room; and `back` only carries the output back. -/
import Untrusted.Proofs.DecodesArray

open Aeneas Aeneas.Std Result

namespace untrusted.writer

/-! ## Specification vocabulary -/

/-- The writer invariant: the position is within the output. -/
def Writer.Inv (w : Writer) : Prop := w.pos.val ≤ w.out.length

/-- `w`'s output once `e` is written at its position. -/
def Writer.put (w : Writer) (e : List U8) : List U8 :=
  w.out.val.take w.pos.val ++ e ++ w.out.val.drop (w.pos.val + e.length)

/-- What a writer method (or `encode`) writing `e` from the valid writer `w`
    did, given its result `res`, the new writer `w'` and the backward function
    `back`. On failure the output before `w`'s position is unchanged; the
    position itself is not promised (`Writer::encode` restores it). -/
def Writes (w : Writer) (e : List U8) (res : core.result.Result Unit EncodeError) (w' : Writer)
    (back : Writer → Writer) : Prop :=
  (∀ x, back x = { w with out := x.out }) ∧ w'.out.length = w.out.length ∧ Writer.Inv w' ∧
  match res with
  | .Ok _ => w.pos.val + e.length ≤ w.out.length ∧ w'.pos.val = w.pos.val + e.length ∧
      w'.out.val = Writer.put w e
  | .Err _ => w.out.length < w.pos.val + e.length ∧
      w'.out.val.take w.pos.val = w.out.val.take w.pos.val

/-! ## Composing writes -/

theorem put_put (w w1 : Writer) (e1 e2 : List U8) (hinv : Writer.Inv w)
    (hpos : w1.pos.val = w.pos.val + e1.length)
    (hout : w1.out.val = Writer.put w e1) :
    Writer.put w1 e2 = Writer.put w (e1 ++ e2) := by
  simp only [Writer.Inv, Slice.length] at hinv
  -- `w1`'s output is `A ++ e1 ++ D`, with `A` the `w.pos` bytes before.
  have hA : (w.out.val.take w.pos.val ++ e1).length = w.pos.val + e1.length := by simp; omega
  have hd : (w.out.val.take w.pos.val ++ e1 ++ w.out.val.drop (w.pos.val + e1.length)).drop
      (w.pos.val + e1.length + e2.length) = w.out.val.drop (w.pos.val + e1.length + e2.length) := by
    rw [← List.drop_drop, List.drop_left' hA, List.drop_drop]
  unfold Writer.put
  rw [hout, hpos]
  unfold Writer.put
  rw [List.take_left' hA, hd]
  simp [List.append_assoc, Nat.add_assoc]

/-- Writing `e1` then `e2` writes `e1 ++ e2`; the backward functions compose
    the way Aeneas composes them for `a?; b`. -/
theorem Writes.cons {w w1 w2 : Writer} {e1 e2 : List U8} {u : Unit} {res}
    {b1 b2 : Writer → Writer} (hinv : Writer.Inv w) (h1 : Writes w e1 (.Ok u) w1 b1)
    (h2 : Writes w1 e2 res w2 b2) :
    Writes w (e1 ++ e2) res w2 (fun x => { w with out := (b1 { w1 with out := (b2 x).out }).out }) := by
  obtain ⟨hb1, hl1, hi1, hroom1, hpos1, hout1⟩ := h1
  obtain ⟨hb2, hl2, hi2, h2⟩ := h2
  refine ⟨fun x => by simp [hb1, hb2], hl2.trans hl1, hi2, ?_⟩
  simp only [Writer.Inv, Slice.length] at hinv hi1 hl1 hroom1 hl2
  cases res
  · obtain ⟨hroom2, hpos2, hout2⟩ := h2
    simp only [List.length_append, Slice.length] at hroom2 ⊢
    refine ⟨by omega, by omega, ?_⟩
    rw [hout2, put_put w w1 e1 e2 hinv hpos1 hout1]
  · obtain ⟨hroom2, htake2⟩ := h2
    simp only [List.length_append, Slice.length] at hroom2 ⊢
    refine ⟨by omega, ?_⟩
    have hle : w.pos.val ≤ w1.pos.val := by omega
    have htt : ∀ l : List U8, (l.take w1.pos.val).take w.pos.val = l.take w.pos.val := fun l => by
      rw [List.take_take, Nat.min_eq_left hle]
    rw [← htt, htake2, htt, hout1, Writer.put, List.append_assoc,
      List.take_left' (by simp; omega)]

/-- `Writes.cons` for a write inside a sequence: Aeneas composes the inner
    backward functions without rebuilding the writer around each. -/
theorem Writes.cons_in {w w1 w2 : Writer} {e1 e2 : List U8} {u : Unit} {res}
    {b1 b2 : Writer → Writer} (hinv : Writer.Inv w) (h1 : Writes w e1 (.Ok u) w1 b1)
    (h2 : Writes w1 e2 res w2 b2) :
    Writes w (e1 ++ e2) res w2 (fun x => b1 { w1 with out := (b2 x).out }) := by
  obtain ⟨-, rest⟩ := Writes.cons hinv h1 h2
  refine ⟨fun x => ?_, rest⟩
  simp [h1.1, h2.1]

/-- A first write that fails makes the whole sequence fail; the backward
    function is the one Aeneas builds for `a?` returning early. -/
theorem Writes.err_cons {w w1 : Writer} {e1 : List U8} {err} {b1 : Writer → Writer}
    (e2 : List U8) (err' : EncodeError) (h1 : Writes w e1 (.Err err) w1 b1) :
    Writes w (e1 ++ e2) (.Err err') w1 (fun x => { w with out := (b1 x).out }) := by
  obtain ⟨hb1, hl1, hi1, hroom1, htake1⟩ := h1
  refine ⟨fun x => by simp [hb1], hl1, hi1, ?_, htake1⟩
  simp only [List.length_append]
  omega

/-- A write seen through one more backward function that only carries the
    output back, as Aeneas wraps a call in tail position. -/
theorem Writes.wrap {w w' : Writer} {e : List U8} {res} {b : Writer → Writer}
    (h : Writes w e res w' b) : Writes w e res w' (fun x => { w with out := (b x).out }) := by
  obtain ⟨hb, rest⟩ := h
  exact ⟨fun x => by simp [hb], rest⟩

/-- A write of `e ++ []` is a write of `e`. -/
theorem Writes.append_nil {w w' : Writer} {e : List U8} {res} {b : Writer → Writer}
    (h : Writes w e res w' b) : Writes w (e ++ []) res w' b := by
  rwa [List.append_nil]

/-- A failed write of `e` is a failed write of `e` followed by anything. -/
theorem Writes.err_append {w w' : Writer} {e : List U8} {err} {b : Writer → Writer}
    (rest : List U8) (err' : EncodeError) (h : Writes w e (.Err err) w' b) :
    Writes w (e ++ rest) (.Err err') w' b := by
  obtain ⟨hb, hl, hi, hroom, htake⟩ := h
  refine ⟨hb, hl, hi, ?_, htake⟩
  simp only [List.length_append]
  omega

/-- Writing nothing. -/
theorem Writes.nil {w : Writer} (hinv : Writer.Inv w) :
    Writes w [] (.Ok ()) w (fun x => { w with out := x.out }) := by
  refine ⟨fun _ => rfl, rfl, hinv, by simp [Writer.Inv] at hinv ⊢; omega, by simp, ?_⟩
  simp [Writer.put]

/-- The result of a failed write is `NoRoom`, the only error. -/
theorem Writes.err_eq {w w' : Writer} {e : List U8} {err} {b : Writer → Writer}
    (h : Writes w e (.Err err) w' b) : err = .NoRoom := by
  cases err; rfl

/-! ## The bytes of a number -/

/-- The byte `x mod 256`. -/
def byte (x : Nat) : U8 := UScalar.ofNatCore (x % 256) (by simp; omega)

@[simp] theorem byte_val (x : Nat) : (byte x).val = x % 256 := by simp [byte]

/-- The `n` low bytes of `x`, most significant first. -/
def beBytes : Nat → Nat → List U8
  | 0, _ => []
  | n + 1, x => beBytes n (x / 256) ++ [byte x]

/-- The `n` low bytes of `x`, least significant first. -/
def leBytes : Nat → Nat → List U8
  | 0, _ => []
  | n + 1, x => byte x :: leBytes n (x / 256)

@[simp] theorem beBytes_length (n x : Nat) : (beBytes n x).length = n := by
  induction n generalizing x <;> simp [beBytes, *]

@[simp] theorem leBytes_length (n x : Nat) : (leBytes n x).length = n := by
  induction n generalizing x <;> simp [leBytes, *]

theorem leBytes_eq_reverse (n x : Nat) : leBytes n x = (beBytes n x).reverse := by
  induction n generalizing x <;> simp [leBytes, beBytes, *]

theorem beNat_beBytes (n x : Nat) : beNat (beBytes n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [beBytes, Nat.mod_one]
  | succ n ih =>
    rw [beBytes, beNat_append_singleton, ih, byte_val, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    ring

theorem leNat_leBytes (n x : Nat) : leNat (leBytes n x) = x % 256 ^ n := by
  rw [leNat, leBytes_eq_reverse, List.reverse_reverse, beNat_beBytes]

/-! ## Loops -/

/-- **Spec theorem for the loop of `put_bytes`**: writes `src[i..]` at
    `pos + i`. -/
@[step]
theorem put_bytes_loop.spec (out : Slice U8) (pos : Usize) (src : Slice U8) (i : Usize)
    (h : pos.val + src.length ≤ out.length) (hi : i.val ≤ src.length) :
    put_bytes_loop out pos src i ⦃ (out' : Slice U8) =>
      out'.val = out.val.take (pos.val + i.val) ++ src.val.drop i.val ++
        out.val.drop (pos.val + src.length) ⦄ := by
  unfold put_bytes_loop
  dsimp only
  split
  · step*
    have hlt : pos.val + i.val < out.val.length := by scalar_tac
    have hsi : i.val < src.val.length := by scalar_tac
    rw [out'_post, s_post, Slice.set_val_eq, i3_post, i4_post, ← Nat.add_assoc,
      untrusted.take_set_succ _ _ _ hlt, List.drop_set_of_lt (by scalar_tac),
      List.drop_eq_getElem_cons hsi, i2_post]
    simp
  · simp only [WP.spec_ok]
    have : i.val = src.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp), List.append_nil]
    exact (List.take_append_drop _ _).symm
termination_by src.length - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `put_bytes`**: writes `src` at `pos`. -/
@[step]
theorem put_bytes.spec (out : Slice U8) (pos : Usize) (src : Slice U8)
    (h : pos.val + src.length ≤ out.length) :
    put_bytes out pos src ⦃ (out' : Slice U8) =>
      out'.val = out.val.take pos.val ++ src.val ++ out.val.drop (pos.val + src.length) ⦄ := by
  unfold put_bytes
  step*
  simpa using out'_post

@[simp] theorem byte_mod (x : Nat) : byte (x % 256) = byte x := by
  rw [UScalar.eq_equiv]; simp

theorem cast_u8 {ty : UScalarTy} (x : UScalar ty) : UScalar.cast .U8 x = byte x.val := by
  rw [UScalar.eq_equiv, UScalar.cast_val_eq, byte_val]; rfl


/-- **Spec theorem for the loop of `put_be`**: writes the `i` low bytes of
    `v` at `pos`, most significant first. -/
@[step]
theorem put_be_loop.spec (out : Slice U8) (pos : Usize) (v : U128) (i : Usize)
    (h : pos.val + i.val ≤ out.length) :
    put_be_loop out pos v i ⦃ (out' : Slice U8) =>
      out'.val = out.val.take pos.val ++ beBytes i.val v.val ++ out.val.drop (pos.val + i.val) ⦄ := by
  unfold put_be_loop
  split
  · step*
    have hlt : pos.val + i1.val < out.val.length := by scalar_tac
    have hi : i.val = i1.val + 1 := by scalar_tac
    have hs : s.val = out.val.set (pos.val + i1.val) (byte v.val) := by
      rw [s_post, Slice.set_val_eq, i3_post, i4_post, cast_u8, i2_post, byte_mod]
    have hlen : s.val.length = out.val.length := by rw [hs, List.length_set]
    rw [out'_post, hs, v1_post, hi, beBytes, List.take_set_of_le (by omega),
      List.drop_eq_getElem_cons (by simp; omega), List.getElem_set_self,
      List.drop_set_of_lt (by omega)]
    simp [List.append_assoc, Nat.add_assoc]
  · simp only [WP.spec_ok]
    have : i.val = 0 := by scalar_tac
    simp [this, beBytes]
termination_by i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `put_be`**. -/
@[step]
theorem put_be.spec (out : Slice U8) (pos : Usize) (v : U128) (n : Usize)
    (h : pos.val + n.val ≤ out.length) :
    put_be out pos v n ⦃ (out' : Slice U8) =>
      out'.val = out.val.take pos.val ++ beBytes n.val v.val ++ out.val.drop (pos.val + n.val) ⦄ := by
  unfold put_be
  step*

/-- **Spec theorem for the loop of `put_le`**: writes the bytes `i..n` of
    the little-endian `v`, from `v`'s byte `i` on, at `pos + i`. -/
@[step]
theorem put_le_loop.spec (out : Slice U8) (pos n : Usize) (v : U128) (i : Usize)
    (h : pos.val + n.val ≤ out.length) (hi : i.val ≤ n.val) :
    put_le_loop out pos n v i ⦃ (out' : Slice U8) =>
      out'.val = out.val.take (pos.val + i.val) ++ leBytes (n.val - i.val) v.val ++
        out.val.drop (pos.val + n.val) ⦄ := by
  unfold put_le_loop
  split
  · step*
    have hlt : pos.val + i.val < out.val.length := by scalar_tac
    have hs : s.val = out.val.set (pos.val + i.val) (byte v.val) := by
      rw [s_post, Slice.set_val_eq, i2_post, i3_post, cast_u8, i1_post, byte_mod]
    have hn : n.val - i.val = (n.val - i4.val) + 1 := by scalar_tac
    rw [out'_post, hs, v1_post, i4_post, ← Nat.add_assoc, untrusted.take_set_succ _ _ _ hlt,
      List.drop_set_of_lt (by scalar_tac), hn, leBytes]
    simp [List.append_assoc, ← i4_post]
  · simp only [WP.spec_ok]
    have : i.val = n.val := by scalar_tac
    simp [this, leBytes]
termination_by n.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `put_le`**. -/
@[step]
theorem put_le.spec (out : Slice U8) (pos : Usize) (v : U128) (n : Usize)
    (h : pos.val + n.val ≤ out.length) :
    put_le out pos v n ⦃ (out' : Slice U8) =>
      out'.val = out.val.take pos.val ++ leBytes n.val v.val ++ out.val.drop (pos.val + n.val) ⦄ := by
  unfold put_le
  step*

/-! ## The writer's methods -/

/-- **Spec theorem for `Writer::remaining`** -/
@[step]
theorem Writer.remaining.spec (self : Writer) (h : Writer.Inv self) :
    Writer.remaining self ⦃ (n : Usize) => n.val = self.out.length - self.pos.val ⦄ := by
  unfold Writer.remaining
  simp only [Writer.Inv] at h
  step*

theorem put_length (w : Writer) (e : List U8) (hinv : Writer.Inv w)
    (hroom : w.pos.val + e.length ≤ w.out.length) : (Writer.put w e).length = w.out.length := by
  simp only [Writer.Inv, Slice.length] at hinv hroom
  simp only [Writer.put, Slice.length, List.length_append, List.length_take, List.length_drop]
  omega

/-- A write of `e` that fits, from the valid `w`, giving `out`. -/
theorem Writes.ok {w : Writer} {e : List U8} (out : Slice U8) (pos : Usize) (hinv : Writer.Inv w)
    (hroom : w.pos.val + e.length ≤ w.out.length) (hpos : pos.val = w.pos.val + e.length)
    (hout : out.val = Writer.put w e) :
    Writes w e (.Ok ()) { out, pos } (fun x => { w with out := x.out }) := by
  have hl : out.length = w.out.length := by
    rw [Slice.length, hout, put_length w e hinv hroom]
  exact ⟨fun _ => rfl, hl, by simp only [Writer.Inv, hl]; omega, hroom, hpos, hout⟩

/-- A write of `e` that does not fit, from the valid `w`. -/
theorem Writes.no_room {w : Writer} {e : List U8} (hinv : Writer.Inv w)
    (hroom : w.out.length < w.pos.val + e.length) :
    Writes w e (.Err .NoRoom) w (fun x => { w with out := x.out }) :=
  ⟨fun _ => rfl, rfl, hinv, hroom, rfl⟩

/-- **Spec theorem for `Writer::write_byte`** -/
@[step]
theorem Writer.write_byte.spec (self : Writer) (b : U8) (h : Writer.Inv self) :
    Writer.write_byte self b ⦃ res w' back => Writes self [b] res w' back ⦄ := by
  unfold Writer.write_byte
  simp only [Writer.Inv] at h
  simp only []
  split
  · have hlt : self.pos.val < self.out.val.length := by scalar_tac
    step as ⟨ s, s_post ⟩
    step as ⟨ i1, i1_post ⟩
    apply Writes.ok _ _ h (by simp [Slice.length]; omega) (by simp [i1_post])
    rw [s_post, Slice.set_val_eq, Writer.put, List.length_singleton,
      List.set_eq_take_append_cons_drop, if_pos hlt]
    simp
  · have hge : self.out.val.length ≤ self.pos.val := by scalar_tac
    simp only [WP.spec_ok]
    exact Writes.no_room h (by simp [Slice.length]; omega)

/-- **Spec theorem for `Writer::write_bytes`** -/
@[step]
theorem Writer.write_bytes.spec (self : Writer) (b : Slice U8) (h : Writer.Inv self) :
    Writer.write_bytes self b ⦃ res w' back => Writes self b.val res w' back ⦄ := by
  unfold Writer.write_bytes
  step as ⟨ i1, i1_post ⟩
  split
  · have hgt : self.out.val.length < self.pos.val + b.val.length := by scalar_tac
    simp only [WP.spec_ok]
    exact Writes.no_room h (by simp [Slice.length]; omega)
  · have hle : self.pos.val + b.val.length ≤ self.out.val.length := by
      simp only [Writer.Inv] at h; scalar_tac
    step as ⟨ s, s_post ⟩
    step as ⟨ i3, i3_post ⟩
    exact Writes.ok _ _ h (by simp [Slice.length]; omega) (by simp [i3_post])
      (by simp [Writer.put, s_post])

/-- **Spec theorem for `Writer::write_be`** -/
@[step]
theorem Writer.write_be.spec (self : Writer) (v : U128) (n : Usize) (h : Writer.Inv self) :
    Writer.write_be self v n ⦃ res w' back => Writes self (beBytes n.val v.val) res w' back ⦄ := by
  unfold Writer.write_be
  step as ⟨ i, i_post ⟩
  split
  · have hgt : self.out.val.length < self.pos.val + n.val := by scalar_tac
    simp only [WP.spec_ok]
    exact Writes.no_room h (by simp [Slice.length]; omega)
  · have hle : self.pos.val + n.val ≤ self.out.val.length := by
      simp only [Writer.Inv] at h; scalar_tac
    step as ⟨ s, s_post ⟩
    step as ⟨ i1, i1_post ⟩
    exact Writes.ok _ _ h (by simp [Slice.length]; omega) (by simp [i1_post])
      (by simp [Writer.put, s_post])

/-- **Spec theorem for `Writer::write_le`** -/
@[step]
theorem Writer.write_le.spec (self : Writer) (v : U128) (n : Usize) (h : Writer.Inv self) :
    Writer.write_le self v n ⦃ res w' back => Writes self (leBytes n.val v.val) res w' back ⦄ := by
  unfold Writer.write_le
  step as ⟨ i, i_post ⟩
  split
  · have hgt : self.out.val.length < self.pos.val + n.val := by scalar_tac
    simp only [WP.spec_ok]
    exact Writes.no_room h (by simp [Slice.length]; omega)
  · have hle : self.pos.val + n.val ≤ self.out.val.length := by
      simp only [Writer.Inv] at h; scalar_tac
    step as ⟨ s, s_post ⟩
    step as ⟨ i1, i1_post ⟩
    exact Writes.ok _ _ h (by simp [Slice.length]; omega) (by simp [i1_post])
      (by simp [Writer.put, s_post])

/-! ## `Encode` impls -/

/-- `inst` writes `E v` for every value `v`.

From any valid writer, `encode v` never panics: it either writes the bytes
`E v` at the writer's position, or fails, exactly when they do not fit. -/
class EncodesAs {T : Type} (inst : Encode T) (E : outParam (T → List U8)) : Prop where
  spec : ∀ (v : T) (w : Writer), Writer.Inv w →
    inst.encode v w ⦃ res w' back => Writes w (E v) res w' back ⦄

/-- The bytes `inst` writes, found through its `EncodesAs` instance. -/
abbrev FmtE {T : Type} (inst : Encode T) {E : T → List U8} [EncodesAs inst E] : T → List U8 := E

/-- **Spec theorem for `untrusted::writer::Writer::encode`**: writes like
    `T`, and on failure leaves the position unchanged. -/
@[step]
theorem Writer.encode.spec {T : Type} (inst : Encode T) {E} [h : EncodesAs inst E]
    (self : Writer) (v : T) (hinv : Writer.Inv self) :
    Writer.encode inst self v ⦃ res w' back =>
      Writes self (E v) res w' back ∧ (∀ e, res = .Err e → w'.pos = self.pos) ⦄ := by
  unfold Writer.encode
  apply WP.spec_bind (h.spec v self hinv)
  rintro ⟨r, self1, back⟩ hw
  simp only [WP.uncurry'_pair, uncurry] at hw ⊢
  cases r
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨hw.wrap, fun _ h => nomatch h⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    obtain ⟨hb, hl, -, hroom, htake⟩ := hw
    refine ⟨⟨fun x => by simp [hb], hl, ?_, hroom, htake⟩, fun _ _ => by first | rfl | trivial⟩
    simp only [Writer.Inv, hl] at hinv ⊢
    exact hinv

/-- **Spec theorem for `untrusted::writer::encode_into`**: writes `E v` to
    the start of `out` and returns its length, or fails exactly when it does
    not fit. -/
theorem encode_into.spec {T : Type} (inst : Encode T) {E} [h : EncodesAs inst E] (v : T)
    (out : Slice U8) :
    encode_into inst v out ⦃ res out' =>
      out'.length = out.length ∧
      match res with
      | .Ok n => n.val = (E v).length ∧ (E v).length ≤ out.length ∧
          out'.val = E v ++ out.val.drop (E v).length
      | .Err _ => out.length < (E v).length ⦄ := by
  unfold encode_into
  apply WP.spec_bind (h.spec v { out, pos := 0#usize } (by simp [Writer.Inv]))
  rintro ⟨r, cursor, back⟩ hw
  simp only [WP.uncurry'_pair, uncurry] at hw ⊢
  obtain ⟨hb, hl, -, hw⟩ := hw
  cases r
  · obtain ⟨hroom, hpos, hout⟩ := hw
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok, WP.uncurry'_pair, hb]
    simp [Writer.put] at hroom hpos hout ⊢
    exact ⟨hl, by simpa using hpos, by simpa using hroom, hout⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, WP.uncurry'_pair, hb]
    exact ⟨hl, by simpa using hw.1⟩

end untrusted.writer
