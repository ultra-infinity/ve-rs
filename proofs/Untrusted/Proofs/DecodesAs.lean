/- `DecodesAs`: what it means for a `Decode` impl to decode a format, and the
   combinators used to describe derived (sequential) formats. -/
import Untrusted.Proofs.Reader

open Aeneas Aeneas.Std Result

namespace untrusted.reader

/-- `inst` decodes exactly the byte strings described by `D` and fails exactly
on those described by `F`.

From any valid reader whose unread bytes are `l`, `decode` never panics and
either succeeds with `v` after consuming `k` bytes, where `D l v k`, or fails
with `F l`. It always stays on the same input with a valid reader. `D` and `F`
exclude each other and `D` is functional, so together they determine the
result for every input. -/
class DecodesAs {T : Type} (inst : Decode T) (D : outParam (List U8 → T → Nat → Prop))
    (F : outParam (List U8 → Prop)) : Prop where
  spec : ∀ r : Reader, Reader.Inv r →
    inst.decode r ⦃ (res : core.result.Result T ValidationError) (r' : Reader) =>
      r'.input = r.input ∧ Reader.Inv r' ∧
      match res with
      | .Ok v => ∃ k, D (Reader.rest r) v k ∧ r'.pos.val = r.pos.val + k
      | .Err _ => F (Reader.rest r) ⦄
  disjoint : ∀ l v k, D l v k → ¬ F l
  functional : ∀ l v k v' k', D l v k → D l v' k' → v = v' ∧ k = k'

/-! ## Reader positions -/

theorem Reader.rest_advance (r r' : Reader) (k : Nat) (hin : r'.input = r.input)
    (hpos : r'.pos.val = r.pos.val + k) : Reader.rest r' = (Reader.rest r).drop k := by
  simp [Reader.rest, hin, hpos, List.drop_drop, Nat.add_comm]

/-! ## `Reader::decode` -/

/-- **Spec theorem for `untrusted::reader::Reader::decode`**: decodes like `P`,
    and on failure leaves the reader unchanged. -/
@[step]
theorem Reader.decode.spec {P : Type} (inst : Decode P) {D F} [h : DecodesAs inst D F]
    (self : Reader) (hinv : Reader.Inv self) :
    Reader.decode inst self ⦃ (res : core.result.Result P ValidationError) (self' : Reader) =>
      match res with
      | .Ok v => ∃ k, D (Reader.rest self) v k ∧ self'.input = self.input ∧
          self'.pos.val = self.pos.val + k ∧ Reader.Inv self'
      | .Err _ => F (Reader.rest self) ∧ self' = self ⦄ := by
  unfold Reader.decode
  step with h.spec self hinv as ⟨ res, r', hin, hinv', hpost ⟩
  cases res
  · obtain ⟨k, hD, hpos⟩ := hpost
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨k, hD, hin, hpos, hinv'⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    refine ⟨hpost, ?_⟩
    rw [hin]

/-! ## `Untrusted::read_all` -/

/-- `read_all` succeeds exactly on the inputs that `P` decodes *completely*. -/
theorem UntrustedShared0SliceU8.read_all.spec_of {P : Type} (inst : Decode P) {D F}
    [h : DecodesAs inst D F] (self : Untrusted (Slice U8)) :
    UntrustedShared0SliceU8.read_all inst self
      ⦃ (res : core.result.Result P ValidationError) =>
        match res with
        | .Ok v => D (self : Slice U8).val v (self : Slice U8).val.length
        | .Err _ => ∀ v, ¬ D (self : Slice U8).val v (self : Slice U8).val.length ⦄ := by
  have hinv0 : Reader.Inv { input := self, pos := 0#usize } := by simp [Reader.Inv]
  have hrest0 : Reader.rest { input := self, pos := 0#usize } = (self : Slice U8).val := by
    simp [Reader.rest]
  apply WP.spec_mono (UntrustedShared0SliceU8.read_all.spec inst self
    (fun res r' => Reader.Inv r' ∧ match res with
      | .Ok v => ∃ k, D (self : Slice U8).val v k ∧ r'.pos.val = k
      | .Err _ => F (self : Slice U8).val)
    (WP.spec_mono (h.spec _ hinv0) (by
      rintro ⟨_ | _, r'⟩ ⟨hin, hinv', hpost⟩
      · obtain ⟨k, hD, hpos⟩ := hpost
        exact ⟨⟨hinv', k, by simpa [hrest0] using hD, by simpa using hpos⟩, hin, hinv'⟩
      · exact ⟨⟨hinv', by simpa [hrest0] using hpost⟩, hin, hinv'⟩)))
  rintro (v | e) hpost
  · obtain ⟨r', ⟨hinv', k, hD, hpos⟩, hin, hdone⟩ := hpost
    simp only [Reader.rest, List.drop_eq_nil_iff, hin] at hdone
    simp only [Reader.Inv, hin] at hinv'
    have hk : k = (self : Slice U8).val.length := by
      simp only [Slice.length] at hinv'; scalar_tac
    simpa [hk] using hD
  · intro v hD
    rcases hpost with ⟨-, v0, r', ⟨hinv', k, hD0, hpos⟩, hin, hleft⟩ | ⟨r', -, hF⟩
    · simp only [Reader.rest, ne_eq, List.drop_eq_nil_iff, not_le, hin] at hleft
      have := (h.functional _ _ _ _ _ hD0 hD).2
      scalar_tac
    · exact h.disjoint _ _ _ hD hF

/-! ## Sequential formats

A derived decoder reads its fields one after another. Its format is described
with these combinators over the tuple of field values, e.g. for
`struct S { a: A, b: B }`, `Dseq DA (Dseq DB Dnil)` on `(s.a, s.b, ())`. -/

/-- The format that consumes nothing. -/
def Dnil : List U8 → Unit → Nat → Prop := fun _ _ k => k = 0

/-- The empty format never fails. -/
def Fnil : List U8 → Prop := fun _ => False

/-- `A` followed by `B`. -/
def Dseq {A B : Type} (DA : List U8 → A → Nat → Prop) (DB : List U8 → B → Nat → Prop) :
    List U8 → A × B → Nat → Prop :=
  fun l v k => ∃ ka kb, DA l v.1 ka ∧ DB (l.drop ka) v.2 kb ∧ k = ka + kb

/-- `A` followed by `B` fails if `A` fails, or `A` succeeds and `B` then fails. -/
def Fseq {A : Type} (DA : List U8 → A → Nat → Prop) (FA FB : List U8 → Prop) : List U8 → Prop :=
  fun l => FA l ∨ ∃ a ka, DA l a ka ∧ FB (l.drop ka)

/-- The laws making a format description determine the result. -/
structure Laws {T : Type} (D : List U8 → T → Nat → Prop) (F : List U8 → Prop) : Prop where
  disjoint : ∀ l v k, D l v k → ¬ F l
  functional : ∀ l v k v' k', D l v k → D l v' k' → v = v' ∧ k = k'

theorem DecodesAs.laws {T : Type} {inst : Decode T} {D F} (h : DecodesAs inst D F) : Laws D F :=
  ⟨h.disjoint, h.functional⟩

theorem Laws.nil : Laws Dnil Fnil :=
  ⟨fun _ _ _ _ hF => hF, fun _ _ _ _ _ h h' => ⟨rfl, h.trans h'.symm⟩⟩

theorem Laws.seq {A B : Type} {DA : List U8 → A → Nat → Prop} {FA} {DB : List U8 → B → Nat → Prop}
    {FB} (hA : Laws DA FA) (hB : Laws DB FB) : Laws (Dseq DA DB) (Fseq DA FA FB) where
  disjoint := by
    rintro l ⟨a, b⟩ k ⟨ka, kb, hDa, hDb, -⟩ (hFa | ⟨a', ka', hDa', hFb⟩)
    · exact hA.disjoint _ _ _ hDa hFa
    · obtain ⟨-, rfl⟩ := hA.functional _ _ _ _ _ hDa hDa'
      exact hB.disjoint _ _ _ hDb hFb
  functional := by
    rintro l ⟨a, b⟩ k ⟨a', b'⟩ k' ⟨ka, kb, hDa, hDb, rfl⟩ ⟨ka', kb', hDa', hDb', rfl⟩
    obtain ⟨rfl, rfl⟩ := hA.functional _ _ _ _ _ hDa hDa'
    obtain ⟨rfl, rfl⟩ := hB.functional _ _ _ _ _ hDb hDb'
    exact ⟨rfl, rfl⟩

/-- Transport laws along an injective view of the value, e.g. struct ↦ tuple. -/
theorem Laws.map {S T : Type} {D : List U8 → T → Nat → Prop} {F} (h : Laws D F) (f : S → T)
    (hf : Function.Injective f) : Laws (fun l s k => D l (f s) k) F where
  disjoint l s k hD := h.disjoint l (f s) k hD
  functional l s k s' k' hD hD' := by
    obtain ⟨he, rfl⟩ := h.functional _ _ _ _ _ hD hD'
    exact ⟨hf he, rfl⟩

/-- The success relation of `inst`'s format, found through its `DecodesAs` instance. -/
abbrev FmtD {T : Type} (inst : Decode T) {D : List U8 → T → Nat → Prop} {F : List U8 → Prop}
    [DecodesAs inst D F] : List U8 → T → Nat → Prop := D

/-- The failure set of `inst`'s format, found through its `DecodesAs` instance. -/
abbrev FmtF {T : Type} (inst : Decode T) {D : List U8 → T → Nat → Prop} {F : List U8 → Prop}
    [DecodesAs inst D F] : List U8 → Prop := F

/-! ## Building `Dseq`/`Fseq` facts field by field -/

theorem Dnil.intro (l : List U8) : Dnil l () 0 := rfl

theorem Dseq.intro {A B : Type} {DA : List U8 → A → Nat → Prop} {DB : List U8 → B → Nat → Prop}
    {l : List U8} {a : A} {b : B} {ka kb : Nat} (hA : DA l a ka) (hB : DB (l.drop ka) b kb) :
    Dseq DA DB l (a, b) (ka + kb) :=
  ⟨ka, kb, hA, hB, rfl⟩

theorem Fseq.here {A : Type} {DA : List U8 → A → Nat → Prop} {FA FB : List U8 → Prop}
    {l : List U8} (h : FA l) : Fseq DA FA FB l :=
  Or.inl h

theorem Fseq.later {A : Type} {DA : List U8 → A → Nat → Prop} {FA FB : List U8 → Prop}
    {l : List U8} {a : A} {ka : Nat} (hA : DA l a ka) (hB : FB (l.drop ka)) : Fseq DA FA FB l :=
  Or.inr ⟨a, ka, hA, hB⟩

/-- The laws of `inst`'s format, found through its `DecodesAs` instance. -/
theorem FmtLaws {T : Type} (inst : Decode T) {D : List U8 → T → Nat → Prop} {F : List U8 → Prop}
    [h : DecodesAs inst D F] : Laws (FmtD inst) (FmtF inst) :=
  h.laws

/-! ## Helpers for hand-written decoders -/

/-- `read_byte` in list form: on success the unread bytes were `b` followed by
    the new unread bytes. Convenient for chaining byte-by-byte decoders. -/
theorem Reader.read_byte.spec_cons (self : Reader) :
    Reader.read_byte self ⦃ (res : core.result.Result U8 ValidationError) (self' : Reader) =>
      match res with
      | .Ok b => Reader.rest self = b :: Reader.rest self' ∧ self'.input = self.input ∧
          self'.pos.val = self.pos.val + 1 ∧ Reader.Inv self'
      | .Err e => Reader.rest self = [] ∧ e = .EndOfInput ∧ self' = self ⦄ := by
  apply WP.spec_mono (Reader.read_byte.spec self)
  rintro ⟨_ | _, self'⟩ h
  · obtain ⟨hhead, hin, hpos, hinv⟩ := h
    refine ⟨?_, hin, hpos, hinv⟩
    rw [Reader.rest_advance self self' 1 hin hpos]
    match hl : Reader.rest self, hhead with
    | x :: t, hhead => simp_all
  · exact h

end untrusted.reader
