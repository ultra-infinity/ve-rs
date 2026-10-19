import Untrusted.Funs
import Untrusted.Spec

open Aeneas Aeneas.Std Result

namespace untrusted

/-- **Spec theorem for `untrusted::Untrusted::new`** -/
@[step]
theorem Untrusted.new.spec {T : Type} (inner : T) :
    Untrusted.new inner ⦃ (r : Untrusted T) => r = inner ⦄ := by
  simp [Untrusted.new]

/-- `Untrusted::validate` is exactly the target type's `Validate::validate`, so
    every `validate` spec applies to it. -/
@[simp]
theorem Untrusted.validate_eq {T U E : Type} (inst : Validate U T E) (self : Untrusted T) :
    Untrusted.validate inst self = inst.validate self := rfl

/-- **Spec theorem for `untrusted::Untrusted::validate`**: whatever holds of the
    target's `Validate::validate` holds of `Untrusted::validate`. -/
@[step]
theorem Untrusted.validate.spec {T U E : Type} (inst : Validate U T E) (self : Untrusted T)
    (post : core.result.Result U E → Prop) (h : inst.validate self ⦃ r => post r ⦄) :
    Untrusted.validate inst self ⦃ r => post r ⦄ := h

/-- **Spec theorem for `untrusted::bytes::check_len`** -/
@[step]
theorem bytes.check_len.spec (input : Slice U8) (expected : Usize) :
    bytes.check_len input expected ⦃ (r : core.result.Result Unit ValidationError) =>
      match r with
      | .Ok _ => input.length = expected.val
      | .Err e => input.length ≠ expected.val ∧ e = .LengthMismatch expected input.len ⦄ := by
  unfold bytes.check_len
  step*

@[step]
theorem bytes.BigEndian.into_inner.spec {T : Type} (self : bytes.BigEndian T) :
    bytes.BigEndian.into_inner self ⦃ (r : T) => r = self ⦄ := by
  simp [bytes.BigEndian.into_inner]

@[step]
theorem bytes.LittleEndian.into_inner.spec {T : Type} (self : bytes.LittleEndian T) :
    bytes.LittleEndian.into_inner self ⦃ (r : T) => r = self ⦄ := by
  simp [bytes.LittleEndian.into_inner]

end untrusted
