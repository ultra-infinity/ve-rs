import Untrusted.Funs
import Untrusted.Spec
import Untrusted.Proofs.Core

open Aeneas Aeneas.Std Result

namespace untrusted.reader

/-! ## Specification vocabulary -/

/-- The reader invariant: the position is within the input. -/
def Reader.Inv (r : Reader) : Prop := r.pos.val ≤ r.input.length

/-- The bytes not yet read. -/
def Reader.rest (r : Reader) : List U8 := r.input.val.drop r.pos.val

/-! ## Specs -/

@[step]
theorem Reader.remaining.spec (self : Reader) (h : Reader.Inv self) :
    Reader.remaining self ⦃ (n : Usize) => n.val = (Reader.rest self).length ⦄ := by
  unfold Reader.remaining
  step*
  · simpa [Reader.Inv] using h
  · simp [Reader.rest, n_post]

@[step]
theorem Reader.at_end.spec (self : Reader) (h : Reader.Inv self) :
    Reader.at_end self ⦃ (b : Bool) => (b = true ↔ Reader.rest self = []) ⦄ := by
  unfold Reader.at_end
  simp only [Reader.Inv] at h
  simp only [WP.spec_ok, decide_eq_true_eq, UScalar.eq_equiv, Slice.len_val, Reader.rest,
    List.drop_eq_nil_iff]
  constructor <;> intro <;> scalar_tac

@[step]
theorem Reader.peek.spec (self : Reader) (b : U8) :
    Reader.peek self b ⦃ (r : Bool) => (r = true ↔ (Reader.rest self).head? = some b) ⦄ := by
  unfold Reader.peek
  step*
  · simp [Reader.rest, List.head?_drop, List.getElem?_eq_getElem (show self.pos.val < self.input.val.length by scalar_tac), i1_post]
  · simp [Reader.rest, List.drop_eq_nil_iff.mpr (show self.input.val.length ≤ self.pos.val by scalar_tac)]

@[step]
theorem Reader.read_byte.spec (self : Reader) :
    Reader.read_byte self ⦃ (res : core.result.Result U8 ValidationError) (self' : Reader) =>
      match res with
      | .Ok byte => (Reader.rest self).head? = some byte ∧ self'.input = self.input ∧
          self'.pos.val = self.pos.val + 1 ∧ Reader.Inv self'
      | .Err e => Reader.rest self = [] ∧ e = .EndOfInput ∧ self' = self ⦄ := by
  unfold Reader.read_byte
  step*
  · simp only [Reader.Inv]
    refine ⟨?_, by scalar_tac, by scalar_tac⟩
    simp [Reader.rest, List.head?_drop, List.getElem?_eq_getElem (show self.pos.val < self.input.val.length by scalar_tac), b_post]
  · simp [Reader.rest, List.drop_eq_nil_iff]
    scalar_tac

@[step]
theorem Reader.read_bytes.spec (self : Reader) (n : Usize) (h : Reader.Inv self) :
    Reader.read_bytes self n
      ⦃ (res : core.result.Result (Untrusted (Slice U8)) ValidationError) (self' : Reader) =>
        match res with
        | .Ok s => n.val ≤ (Reader.rest self).length ∧
            (s : Slice U8).val = (Reader.rest self).take n.val ∧
            self'.input = self.input ∧ self'.pos.val = self.pos.val + n.val ∧ Reader.Inv self'
        | .Err e => (Reader.rest self).length < n.val ∧ e = .EndOfInput ∧ self' = self ⦄ := by
  unfold Reader.read_bytes
  step*
  · simp only [Reader.Inv, Reader.rest, List.length_drop] at h i_post
    scalar_tac
  · simp only [Reader.Inv, Reader.rest, List.length_drop] at h i_post
    dsimp only
    scalar_tac
  · simp only [Reader.Inv, Reader.rest, List.length_drop] at h i_post ⊢
    refine ⟨by scalar_tac, ?_, end_post, by scalar_tac⟩
    rw [s_post, List.slice, end_post, Nat.add_sub_cancel_left]

@[step]
theorem Reader.read_bytes_to_end.spec (self : Reader) (h : Reader.Inv self) :
    Reader.read_bytes_to_end self ⦃ (s : Untrusted (Slice U8)) (self' : Reader) =>
      (s : Slice U8).val = Reader.rest self ∧ self'.input = self.input ∧
        Reader.rest self' = [] ∧ Reader.Inv self' ⦄ := by
  unfold Reader.read_bytes_to_end
  simp only [Reader.Inv] at h
  step*
  simp [Reader.rest, Reader.Inv, rest_post]

@[step]
theorem Reader.finish.spec (self : Reader) (h : Reader.Inv self) :
    Reader.finish self ⦃ (res : core.result.Result Unit ValidationError) =>
      match res with
      | .Ok _ => Reader.rest self = []
      | .Err e => Reader.rest self ≠ [] ∧ e = .TrailingData ⦄ := by
  unfold Reader.finish
  step*

@[step]
theorem Reader.skip.spec (self : Reader) (n : Usize) (h : Reader.Inv self) :
    Reader.skip self n ⦃ (res : core.result.Result Unit ValidationError) (self' : Reader) =>
      match res with
      | .Ok _ => n.val ≤ (Reader.rest self).length ∧ self'.input = self.input ∧
          self'.pos.val = self.pos.val + n.val ∧ Reader.Inv self'
      | .Err e => (Reader.rest self).length < n.val ∧ e = .EndOfInput ∧ self' = self ⦄ := by
  unfold Reader.skip
  step as ⟨ r, self1, r_post ⟩
  cases r
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at *
    simp [*]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at *
    agrind

/-- **Spec theorem for `untrusted::reader::Reader::read`**, for any `T`.

If `T::LEN` is `len` and `T::validate` satisfies `P` on every `len`-byte
slice, then `read` either fails with `EndOfInput` when fewer than `len` bytes
remain, or validates exactly the next `len` bytes. It advances only on
success. Concrete instances are below. -/
theorem Reader.read.spec {T : Type} (lenInst : bytes.FixedLen T)
    (valInst : Validate T (Slice U8) ValidationError) (self : Reader) (h : Reader.Inv self)
    (len : Usize) (hlen : lenInst.LEN = ok len)
    (P : List U8 → core.result.Result T ValidationError → Prop)
    (hval : ∀ s : Slice U8, s.length = len.val → valInst.validate s ⦃ r => P s.val r ⦄) :
    Reader.read lenInst valInst self
      ⦃ (res : core.result.Result T ValidationError) (self' : Reader) =>
        match res with
        | .Ok v => len.val ≤ (Reader.rest self).length ∧ P ((Reader.rest self).take len.val) (.Ok v) ∧
            self'.input = self.input ∧ self'.pos.val = self.pos.val + len.val ∧ Reader.Inv self'
        | .Err e => self' = self ∧
            ((Reader.rest self).length < len.val ∧ e = .EndOfInput ∨
              len.val ≤ (Reader.rest self).length ∧ P ((Reader.rest self).take len.val) (.Err e)) ⦄ := by
  unfold Reader.read
  step as ⟨ i, i_post ⟩
  rw [hlen, bind_ok]
  split
  · rename_i hgt
    simp only [WP.spec_ok, WP.uncurry'_pair, true_and]
    left
    simp only [gt_iff_lt, UScalar.lt_equiv] at hgt
    scalar_tac
  · rename_i hle
    simp only [Reader.Inv, Reader.rest, List.length_drop] at h i_post
    step as ⟨ «end», end_post ⟩
    step as ⟨ s, s_post, s_post1 ⟩
    have hs : s.val = (self.input.val.drop self.pos.val).take len.val := by
      rw [s_post, List.slice, end_post, Nat.add_sub_cancel_left]
    step with hval s (by simp only [gt_iff_lt, UScalar.lt_equiv, not_lt] at hle; scalar_tac) as ⟨ r, r_post ⟩
    rw [hs] at r_post
    cases r
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      simp only [gt_iff_lt, UScalar.lt_equiv, not_lt] at hle
      simp only [Reader.rest, Reader.Inv, List.length_drop]
      refine ⟨by scalar_tac, r_post, rfl, end_post, by scalar_tac⟩
    · simp only [gt_iff_lt, UScalar.lt_equiv, not_lt] at hle
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Reader.rest]
      exact Or.inr ⟨by scalar_tac, r_post⟩


/-- **Spec theorem for `untrusted::Untrusted::read_all`**, for any `P`.

If `P::decode`, run on a fresh reader over `self`, satisfies `Q` (and, like
every decoder built from the reader's methods, keeps the reader valid and on the
same input), then `read_all` succeeds exactly when decoding succeeded *and*
left no byte unread. A successful decode that leaves bytes over is turned into
`TrailingData`. -/
theorem UntrustedShared0SliceU8.read_all.spec {P : Type} (inst : Decode P)
    (self : Untrusted (Slice U8))
    (Q : core.result.Result P ValidationError → Reader → Prop)
    (hparse : inst.decode { input := self, pos := 0#usize }
      ⦃ (res : core.result.Result P ValidationError) (r' : Reader) =>
        Q res r' ∧ r'.input = self ∧ Reader.Inv r' ⦄) :
    UntrustedShared0SliceU8.read_all inst self
      ⦃ (res : core.result.Result P ValidationError) =>
        match res with
        | .Ok v => ∃ r', Q (.Ok v) r' ∧ r'.input = self ∧ Reader.rest r' = []
        | .Err e =>
            (e = .TrailingData ∧ ∃ v r', Q (.Ok v) r' ∧ r'.input = self ∧ Reader.rest r' ≠ []) ∨
            ∃ r', Q (.Err e) r' ⦄ := by
  unfold UntrustedShared0SliceU8.read_all
  step with hparse as ⟨ res, r', hQ, hin, hinv ⟩
  cases res
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨ f, f_post ⟩
    cases f
    · simp only [bind_ok, WP.spec_ok]
      exact ⟨r', hQ, hin, f_post⟩
    · obtain ⟨hne, rfl⟩ := f_post
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact Or.inl ⟨trivial, _, r', hQ, hin, hne⟩
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact Or.inr ⟨r', hQ⟩

end untrusted.reader
