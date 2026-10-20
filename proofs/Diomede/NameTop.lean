/- Specs of `diomede::name`: domain names lowercased, without a trailing
   dot. -/
import Diomede.Funs
import Untrusted

open Aeneas Aeneas.Std Result

namespace diomede.name

@[simp, scalar_tac_simps] theorem MAX_NAME_LEN_val : MAX_NAME_LEN.val = 253 := by
  simp [MAX_NAME_LEN]

/-- An ASCII capital letter made lowercase; other bytes unchanged. -/
def lowerN (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- The text of a name without one trailing dot. -/
def strip (t : List U8) : List U8 :=
  if t ≠ [] ∧ (t.getLast?.map (·.val)) = some 46 then t.dropLast else t

/-- A name is at most 253 bytes long: what `as_bytes` needs. -/
def Name.Inv (n : Name) : Prop := n.len.val ≤ 253

/-- The text of a name, as byte values. -/
def Name.text (n : Name) : List Nat := (n.bytes.val.take n.len.val).map (·.val)

/-- **Spec theorem for `lower`**. -/
@[step]
theorem lower.spec (b : U8) : lower b ⦃ (r : U8) => r.val = lowerN b.val ⦄ := by
  unfold lower lowerN
  split
  · split
    · step*
    · simp only [WP.spec_ok]
      have : ¬ b.val ≤ 90 := by scalar_tac
      simp [this]
  · simp only [WP.spec_ok]
    have : ¬ 65 ≤ b.val := by scalar_tac
    simp [this]

/-- **Spec theorem for `Name::from_text`'s loop**: lowercases `text[i..n]`
    into `bytes`. -/
@[step]
theorem Name.from_text_loop.spec (text : Slice U8) (n : Usize) (bytes : Array U8 253#usize)
    (i : Usize) (hn : n.val ≤ text.length) (h253 : n.val ≤ 253) (hi : i.val ≤ n.val)
    (hpre : (bytes.val.take i.val).map (·.val) = ((text.val.take i.val).map (·.val)).map lowerN) :
    Name.from_text_loop text n bytes i ⦃ (r : Array U8 253#usize) =>
      (r.val.take n.val).map (·.val) = ((text.val.take n.val).map (·.val)).map lowerN ⦄ := by
  unfold Name.from_text_loop
  split
  · step as ⟨c, hc⟩
    step as ⟨l, hl⟩
    step as ⟨a, ha⟩
    step as ⟨i1, hi1⟩
    apply Name.from_text_loop.spec text n a i1 hn h253 (by scalar_tac)
    rw [ha, Array.set_val_eq, hi1, List.take_add_one, List.take_add_one]
    rw [List.take_set_of_le (by omega)]
    have hib : i.val < bytes.val.length := by simp; scalar_tac
    have hit : i.val < text.val.length := by scalar_tac
    rw [List.getElem?_set_self hib, List.getElem?_eq_getElem hit]
    simp [hpre, hl, hc]
    rw [List.take_add_one]; simp [List.getElem?_eq_getElem hit]
  · simp only [WP.spec_ok]
    have : i.val = n.val := by scalar_tac
    rw [← this]; exact hpre
termination_by n.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `Name::from_text`**: the text without one trailing dot,
    lowercased, if it is not empty and at most 253 bytes. -/
@[step]
theorem Name.from_text.spec (text : Slice U8) :
    Name.from_text text ⦃ (r : Option Name) =>
      match r with
      | none => strip text.val = [] ∨ 253 < (strip text.val).length
      | some n => n.Inv ∧ 1 ≤ n.len.val ∧
          n.text = ((strip text.val).map (·.val)).map lowerN ⦄ := by
  unfold Name.from_text
  dsimp only
  -- The length without a trailing dot, and what it leaves.
  have key : (if text.len > 0#usize then (do
        let i ← text.len - 1#usize
        let i1 ← Slice.index_usize text i
        if i1 = 46#u8 then ok i else ok text.len) else ok text.len : Result Usize)
      ⦃ (n1 : Usize) => n1.val ≤ text.length ∧ strip text.val = text.val.take n1.val ⦄ := by
    split
    · rename_i hpos
      have hne : text.val ≠ [] := by
        intro h; have : text.length = 0 := by simp [Slice.length, h]
        scalar_tac
      step as ⟨i, hi⟩
      step as ⟨c, hc⟩
      have hlast : text.val.getLast? = some c := by
        rw [hc, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by scalar_tac)]
        simp [hi]
      split
      · simp only [WP.spec_ok]
        refine ⟨by scalar_tac, ?_⟩
        rename_i h46
        simp [strip, hne, hlast, h46, List.dropLast_eq_take, hi]
      · simp only [WP.spec_ok]
        refine ⟨by simp, ?_⟩
        rename_i h46
        have : c.val ≠ 46 := fun h => h46 (by scalar_tac)
        simp [strip, hlast, this]
    · simp only [WP.spec_ok]
      refine ⟨by simp, ?_⟩
      have : text.val = [] := by
        rename_i h; have : text.length = 0 := by scalar_tac
        simpa [Slice.length] using this
      simp [strip, this]
  step with key as ⟨n1, hn1l, hs⟩
  split
  · simp only [WP.spec_ok]
    left; rw [hs]; rename_i h; rw [show n1.val = 0 by scalar_tac]; simp
  split
  · simp only [WP.spec_ok]
    right; rw [hs]; simp; scalar_tac
  step with Name.from_text_loop.spec text n1 (Array.repeat 253#usize 0#u8) 0#usize hn1l
    (by scalar_tac) (Nat.zero_le _) (by rfl) as ⟨bytes1, hb⟩
  refine ⟨by unfold Name.Inv; scalar_tac, by scalar_tac, ?_⟩
  simp only [Name.text]
  rw [hb, hs]

/-- **Spec theorem for `Name::as_bytes`**. -/
@[step]
theorem Name.as_bytes.spec (n : Name) (h : n.Inv) :
    Name.as_bytes n ⦃ (r : Slice U8) => r.val.map (·.val) = n.text ⦄ := by
  unfold Name.as_bytes
  step*
  · simp; unfold Name.Inv at h; scalar_tac
  · rw [r_post]; simp [List.slice, Name.text]

end diomede.name
