/- Specs for the `#[derive(...)]` impls on `BigEndian`, `LittleEndian` and
   `ValidationError`.

   `Copy` and `StructuralPartialEq` are marker traits: their translations are
   records with no code, so there is nothing to specify beyond the `Clone` impl
   that `Copy` points to.

   `Debug`: Aeneas models `core::fmt::Formatter` as an abstract type and its
   output-producing methods as always succeeding without recording any output.
   The strongest statement available is therefore that formatting never fails
   and leaves the formatter unchanged in the model; the produced text itself is
   outside what the model can express. -/
import Untrusted.Funs
import Untrusted.Spec

open Aeneas Aeneas.Std Result

namespace untrusted

/-! ## `ValidationError` -/

/-- **Spec theorem for `<ValidationError as Clone>::clone`** -/
@[step]
theorem ValidationError.Insts.CoreCloneClone.clone.spec (self : ValidationError) :
    ValidationError.Insts.CoreCloneClone.clone self ⦃ (r : ValidationError) => r = self ⦄ := by
  simp [ValidationError.Insts.CoreCloneClone.clone]

/-- **Spec theorem for `<ValidationError as PartialEq>::eq`**: structural equality. -/
@[step]
theorem ValidationError.Insts.CoreCmpPartialEqValidationError.eq.spec
    (self other : ValidationError) :
    ValidationError.Insts.CoreCmpPartialEqValidationError.eq self other
      ⦃ (b : Bool) => (b = true ↔ self = other) ⦄ := by
  unfold ValidationError.Insts.CoreCmpPartialEqValidationError.eq
  cases self <;> cases other <;> simp [read_discriminant, core.cmp.impls.PartialEqUsize.eq, lift]
  split <;> simp [*]

/-- **Spec theorem for `<ValidationError as Eq>::assert_fields_are_eq`** -/
@[step]
theorem ValidationError.Insts.CoreCmpEq.assert_fields_are_eq.spec (self : ValidationError) :
    ValidationError.Insts.CoreCmpEq.assert_fields_are_eq self ⦃ (_ : Unit) => True ⦄ := by
  simp [ValidationError.Insts.CoreCmpEq.assert_fields_are_eq]

/-- **Spec theorem for `<ValidationError as Debug>::fmt`**: never fails. -/
@[step]
theorem ValidationError.Insts.CoreFmtDebug.fmt.spec (self : ValidationError) (f : core.fmt.Formatter) :
    ValidationError.Insts.CoreFmtDebug.fmt self f
      ⦃ (r : core.result.Result Unit core.fmt.Error) (f' : core.fmt.Formatter) =>
        r = .Ok () ∧ f' = f ⦄ := by
  unfold ValidationError.Insts.CoreFmtDebug.fmt
  cases self <;> simp [core.fmt.Formatter.write_str]

/-- `Copy` reuses the derived `Clone`. -/
theorem ValidationError.Insts.CoreMarkerCopy.cloneInst_eq :
    ValidationError.Insts.CoreMarkerCopy.cloneInst = ValidationError.Insts.CoreCloneClone := rfl

/-! ## `EncodeError` -/

/-- **Spec theorem for `<EncodeError as Clone>::clone`** -/
@[step]
theorem writer.EncodeError.Insts.CoreCloneClone.clone.spec (self : writer.EncodeError) :
    writer.EncodeError.Insts.CoreCloneClone.clone self ⦃ (r : writer.EncodeError) => r = self ⦄ := by
  simp [writer.EncodeError.Insts.CoreCloneClone.clone]

/-- **Spec theorem for `<EncodeError as PartialEq>::eq`**: structural equality. -/
@[step]
theorem writer.EncodeError.Insts.CoreCmpPartialEqEncodeError.eq.spec
    (self other : writer.EncodeError) :
    writer.EncodeError.Insts.CoreCmpPartialEqEncodeError.eq self other
      ⦃ (b : Bool) => (b = true ↔ self = other) ⦄ := by
  cases self; cases other
  simp [writer.EncodeError.Insts.CoreCmpPartialEqEncodeError.eq]

/-- **Spec theorem for `<EncodeError as Debug>::fmt`**: never fails. -/
@[step]
theorem writer.EncodeError.Insts.CoreFmtDebug.fmt.spec (self : writer.EncodeError)
    (f : core.fmt.Formatter) :
    writer.EncodeError.Insts.CoreFmtDebug.fmt self f
      ⦃ (r : core.result.Result Unit core.fmt.Error) (f' : core.fmt.Formatter) =>
        r = .Ok () ∧ f' = f ⦄ := by
  unfold writer.EncodeError.Insts.CoreFmtDebug.fmt
  simp [core.fmt.Formatter.write_str]

/-! ## `BigEndian<T>` and `LittleEndian<T>`

These newtypes forward every derived method to `T`'s impl. -/

/-- **Spec theorem for `<BigEndian<T> as Clone>::clone`**: clones the wrapped value. -/
@[step]
theorem bytes.BigEndian.Insts.CoreCloneClone.clone.spec {T : Type} (inst : core.clone.Clone T)
    (self : bytes.BigEndian T) (post : T → Prop) (h : inst.clone self ⦃ (r : T) => post r ⦄) :
    bytes.BigEndian.Insts.CoreCloneClone.clone inst self ⦃ (r : bytes.BigEndian T) => post r ⦄ := by
  simpa [bytes.BigEndian.Insts.CoreCloneClone.clone] using h

/-- **Spec theorem for `<LittleEndian<T> as Clone>::clone`**: clones the wrapped value. -/
@[step]
theorem bytes.LittleEndian.Insts.CoreCloneClone.clone.spec {T : Type} (inst : core.clone.Clone T)
    (self : bytes.LittleEndian T) (post : T → Prop) (h : inst.clone self ⦃ (r : T) => post r ⦄) :
    bytes.LittleEndian.Insts.CoreCloneClone.clone inst self ⦃ (r : bytes.LittleEndian T) => post r ⦄ := by
  simpa [bytes.LittleEndian.Insts.CoreCloneClone.clone] using h

/-- **Spec theorem for `<BigEndian<T> as PartialEq>::eq`**: compares the wrapped values. -/
@[simp]
theorem bytes.BigEndian.Insts.CoreCmpPartialEqBigEndian.eq.spec {T : Type}
    (inst : core.cmp.PartialEq T T) (self other : bytes.BigEndian T) :
    bytes.BigEndian.Insts.CoreCmpPartialEqBigEndian.eq inst self other = inst.eq self other := rfl

/-- **Spec theorem for `<LittleEndian<T> as PartialEq>::eq`**: compares the wrapped values. -/
@[simp]
theorem bytes.LittleEndian.Insts.CoreCmpPartialEqLittleEndian.eq.spec {T : Type}
    (inst : core.cmp.PartialEq T T) (self other : bytes.LittleEndian T) :
    bytes.LittleEndian.Insts.CoreCmpPartialEqLittleEndian.eq inst self other = inst.eq self other :=
  rfl

/-- **Spec theorem for `<BigEndian<T> as Eq>::assert_fields_are_eq`** -/
@[step]
theorem bytes.BigEndian.Insts.CoreCmpEq.assert_fields_are_eq.spec {T : Type}
    (inst : core.cmp.Eq T) (self : bytes.BigEndian T) :
    bytes.BigEndian.Insts.CoreCmpEq.assert_fields_are_eq inst self ⦃ (_ : Unit) => True ⦄ := by
  simp [bytes.BigEndian.Insts.CoreCmpEq.assert_fields_are_eq]

/-- **Spec theorem for `<LittleEndian<T> as Eq>::assert_fields_are_eq`** -/
@[step]
theorem bytes.LittleEndian.Insts.CoreCmpEq.assert_fields_are_eq.spec {T : Type}
    (inst : core.cmp.Eq T) (self : bytes.LittleEndian T) :
    bytes.LittleEndian.Insts.CoreCmpEq.assert_fields_are_eq inst self ⦃ (_ : Unit) => True ⦄ := by
  simp [bytes.LittleEndian.Insts.CoreCmpEq.assert_fields_are_eq]

/-- **Spec theorem for `<BigEndian<T> as Debug>::fmt`**: never fails. -/
@[step]
theorem bytes.BigEndian.Insts.CoreFmtDebug.fmt.spec {T : Type} (inst : core.fmt.Debug T)
    (self : bytes.BigEndian T) (f : core.fmt.Formatter) :
    bytes.BigEndian.Insts.CoreFmtDebug.fmt inst self f
      ⦃ (r : core.result.Result Unit core.fmt.Error) (f' : core.fmt.Formatter) =>
        r = .Ok () ∧ f' = f ⦄ := by
  simp [bytes.BigEndian.Insts.CoreFmtDebug.fmt]

/-- **Spec theorem for `<LittleEndian<T> as Debug>::fmt`**: never fails. -/
@[step]
theorem bytes.LittleEndian.Insts.CoreFmtDebug.fmt.spec {T : Type} (inst : core.fmt.Debug T)
    (self : bytes.LittleEndian T) (f : core.fmt.Formatter) :
    bytes.LittleEndian.Insts.CoreFmtDebug.fmt inst self f
      ⦃ (r : core.result.Result Unit core.fmt.Error) (f' : core.fmt.Formatter) =>
        r = .Ok () ∧ f' = f ⦄ := by
  simp [bytes.LittleEndian.Insts.CoreFmtDebug.fmt]

/-- `Copy` reuses the derived `Clone`. -/
theorem bytes.BigEndian.Insts.CoreMarkerCopy.cloneInst_eq {T : Type} (inst : core.marker.Copy T) :
    (bytes.BigEndian.Insts.CoreMarkerCopy inst).cloneInst =
      bytes.BigEndian.Insts.CoreCloneClone inst.cloneInst := rfl

/-- `Copy` reuses the derived `Clone`. -/
theorem bytes.LittleEndian.Insts.CoreMarkerCopy.cloneInst_eq {T : Type} (inst : core.marker.Copy T) :
    (bytes.LittleEndian.Insts.CoreMarkerCopy inst).cloneInst =
      bytes.LittleEndian.Insts.CoreCloneClone inst.cloneInst := rfl

end untrusted
