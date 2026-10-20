/- Specs of `adfilter::blocklist`: a sorted list of names, binary search,
   and blocking of listed domains and their subdomains. -/
import Adfilter.NameTop

open Aeneas Aeneas.Std Result

namespace adfilter.blocklist

/-! ## Byte-string order -/

/-- Compares byte values lexicographically: -1, 0 or 1 as `a` comes before,
    equals, or comes after `b` (a proper prefix comes first). -/
def cmpN : List Nat → List Nat → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys => if x < y then -1 else if y < x then 1 else cmpN xs ys

theorem cmpN_cases (a b : List Nat) : cmpN a b = -1 ∨ cmpN a b = 0 ∨ cmpN a b = 1 := by
  induction a generalizing b with
  | nil => cases b <;> simp [cmpN]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpN]
    | cons y ys => simp only [cmpN]; split_ifs <;> simp [ih ys]

theorem cmpN_eq_zero {a b : List Nat} : cmpN a b = 0 ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [cmpN]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpN]
    | cons y ys =>
      simp only [cmpN, List.cons.injEq]
      split_ifs with h1 h2
      · simp; omega
      · simp; omega
      · rw [ih]; constructor
        · intro h; exact ⟨by omega, h⟩
        · intro h; exact h.2

theorem cmpN_swap (a b : List Nat) : cmpN b a = -cmpN a b := by
  induction a generalizing b with
  | nil => cases b <;> simp [cmpN]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpN]
    | cons y ys =>
      simp only [cmpN]
      split_ifs <;> first | omega | simp [ih ys]

theorem cmpN_trans {a b c : List Nat} (h1 : cmpN a b = -1) (h2 : cmpN b c = -1) :
    cmpN a c = -1 := by
  induction a generalizing b c with
  | nil => cases b <;> cases c <;> simp_all [cmpN]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpN] at h1
    | cons y ys =>
      cases c with
      | nil => simp [cmpN] at h2
      | cons z zs =>
        simp only [cmpN] at h1 h2 ⊢
        split_ifs at h1 h2 ⊢ <;> first | omega | exact ih h1 h2

theorem cmpN_cons_same (x : Nat) (xs ys : List Nat) : cmpN (x :: xs) (x :: ys) = cmpN xs ys := by
  simp [cmpN]

/-- The values of a byte string. -/
abbrev vals (l : List U8) : List Nat := l.map (·.val)

/-! ## `compare` -/

/-- **Spec theorem for `compare`'s loop**: skips the common part from `i`. -/
@[step]
theorem compare_loop.spec (a b : Slice U8) (i : Usize) (ha : i.val ≤ a.length)
    (hb : i.val ≤ b.length) :
    compare_loop a b i ⦃ (r : Usize) =>
      i.val ≤ r.val ∧ r.val ≤ a.length ∧ r.val ≤ b.length ∧
        cmpN ((vals a.val).drop i.val) ((vals b.val).drop i.val) =
          cmpN ((vals a.val).drop r.val) ((vals b.val).drop r.val) ∧
        (r.val = a.length ∨ r.val = b.length ∨ (vals a.val)[r.val]! ≠ (vals b.val)[r.val]!) ⦄ := by
  unfold compare_loop
  dsimp only
  split
  · split
    · step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      split
      · rename_i hxy
        step as ⟨i1, hi1⟩
        step as ⟨r, h1, h2, h3, h4, h5⟩
        refine ⟨by omega, h2, h3, ?_, h5⟩
        rw [← h4, hi1]
        have hla : i.val < (vals a.val).length := by simp; scalar_tac
        have hlb : i.val < (vals b.val).length := by simp; scalar_tac
        rw [List.drop_eq_getElem_cons hla, List.drop_eq_getElem_cons hlb]
        have : (vals a.val)[i.val] = (vals b.val)[i.val] := by
          simp [← hx, ← hy, hxy]
        rw [this, cmpN_cons_same]
      · simp only [WP.spec_ok]
        rename_i hxy
        refine ⟨le_refl _, ha, hb, trivial, Or.inr (Or.inr ?_)⟩
        have ea : (vals a.val)[i.val]! = (a.val[i.val]'(by scalar_tac)).val := by
          rw [getElem!_pos _ _ (by simp; scalar_tac)]; simp
        have eb : (vals b.val)[i.val]! = (b.val[i.val]'(by scalar_tac)).val := by
          rw [getElem!_pos _ _ (by simp; scalar_tac)]; simp
        rw [ea, eb]
        intro h; apply hxy; rw [hx, hy]; exact (UScalar.eq_equiv _ _).mpr h
    · simp only [WP.spec_ok]
      exact ⟨le_refl _, ha, hb, trivial, Or.inr (Or.inl (by scalar_tac))⟩
  · simp only [WP.spec_ok]
    exact ⟨le_refl _, ha, hb, trivial, Or.inl (by scalar_tac)⟩
termination_by a.length - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `compare`**: `cmpN` of the two byte strings. -/
@[step]
theorem compare.spec (a b : Slice U8) :
    compare a b ⦃ (r : I8) => r.val = cmpN (vals a.val) (vals b.val) ⦄ := by
  unfold compare
  step as ⟨k, _hk, hka, hkb, hc, hstop⟩
  simp only [List.drop_zero] at hc
  have hla : (vals a.val).length = a.length := by simp
  have hlb : (vals b.val).length = b.length := by simp
  split
  · split
    · step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      have hka' : k.val < (vals a.val).length := by rw [hla]; scalar_tac
      have hkb' : k.val < (vals b.val).length := by rw [hlb]; scalar_tac
      have ex : (vals a.val)[k.val] = x.val := by simp [hx]
      have ey : (vals b.val)[k.val] = y.val := by simp [hy]
      have hne : x.val ≠ y.val := by
        rcases hstop with h | h | h
        · scalar_tac
        · scalar_tac
        · rwa [getElem!_pos (vals a.val) k.val hka', getElem!_pos (vals b.val) k.val hkb', ex, ey] at h
      rw [hc, List.drop_eq_getElem_cons hka', List.drop_eq_getElem_cons hkb', ex, ey]
      split
      · simp only [WP.spec_ok]
        rename_i hxy
        have : x.val < y.val := by scalar_tac
        simp [cmpN, this]
      · simp only [WP.spec_ok]
        rename_i hxy
        have h1 : ¬ x.val < y.val := by scalar_tac
        have h2 : y.val < x.val := by omega
        simp [cmpN, h1, h2]
    · have hkb' : k.val = b.length := by scalar_tac
      have hka' : k.val < (vals a.val).length := by rw [hla]; scalar_tac
      have hdb : (vals b.val).drop k.val = [] := List.drop_eq_nil_of_le (by rw [hlb]; omega)
      rw [hc, List.drop_eq_getElem_cons hka', hdb]
      split
      · scalar_tac
      · split
        · simp [cmpN]
        · scalar_tac
  · have hka' : k.val = a.length := by scalar_tac
    have hda : (vals a.val).drop k.val = [] := List.drop_eq_nil_of_le (by rw [hla]; omega)
    rw [hc, hda]
    split
    · have hkb' : k.val < (vals b.val).length := by rw [hlb]; scalar_tac
      rw [List.drop_eq_getElem_cons hkb']
      simp [cmpN]
    · split
      · scalar_tac
      · have : k.val = b.length := by scalar_tac
        have hdb : (vals b.val).drop k.val = [] := List.drop_eq_nil_of_le (by rw [hlb]; omega)
        rw [hdb]
        simp [cmpN]

/-! ## The list's storage -/

/-- The values of the entry ends. -/
abbrev endsN (ends : Slice U32) : List Nat := ends.val.map (·.val)

/-- Where entry `i` starts. -/
def startN (e : List Nat) (i : Nat) : Nat := if i = 0 then 0 else e[i - 1]!

/-- Entry `i` of the list laid out as `d` and `e`. -/
def entryN (d e : List Nat) (i : Nat) : List Nat := (d.drop (startN e i)).take (e[i]! - startN e i)

/-- Entry `i` is non-empty, within `d`, and after the previous one. -/
def EntryOk (d e : List Nat) (i : Nat) : Prop :=
  startN e i < e[i]! ∧ e[i]! ≤ d.length ∧ (i = 0 ∨ cmpN (entryN d e (i - 1)) (entryN d e i) = -1)

/-- Every entry is valid: the list is non-empty-entried and strictly sorted. -/
def WellFormed (d e : List Nat) : Prop := ∀ i < e.length, EntryOk d e i

/-- `n` is an entry of the list. -/
def Mem (d e : List Nat) (n : List Nat) : Prop := ∃ i < e.length, entryN d e i = n

/-- `n` is blocked: it, or the part of it after one of its dots, is an
    entry. -/
def Blocked (d e : List Nat) (n : List Nat) : Prop :=
  Mem d e n ∨ ∃ j < n.length, n[j]! = 46 ∧ Mem d e (n.drop (j + 1))

/-- `Blocked`, as domains: `n` is a listed domain, or a subdomain of one. -/
theorem blocked_iff (d e n : List Nat) :
    Blocked d e n ↔ ∃ dom, Mem d e dom ∧ (n = dom ∨ ∃ p, n = p ++ [46] ++ dom) := by
  constructor
  · rintro (h | ⟨j, hj, hdot, hm⟩)
    · exact ⟨n, h, Or.inl rfl⟩
    · refine ⟨_, hm, Or.inr ⟨n.take j, ?_⟩⟩
      conv_lhs => rw [← List.take_append_drop j n]
      have hdot' : n[j] = 46 := by rwa [getElem!_pos n j hj] at hdot
      rw [List.drop_eq_getElem_cons hj, hdot']
      simp
  · rintro ⟨dom, hm, rfl | ⟨p, rfl⟩⟩
    · exact Or.inl hm
    · right
      refine ⟨p.length, by simp, by simp, ?_⟩
      simpa using hm

/-- **Spec theorem for `start_of`**. -/
@[step]
theorem start_of.spec (ends : Slice U32) (i : Usize) (h : i.val ≤ ends.length) :
    start_of ends i ⦃ (r : Usize) => r.val = startN (endsN ends) i.val ⦄ := by
  unfold start_of startN
  split
  · simp_all
  · step*
    rename_i hi0
    have : i.val ≠ 0 := by scalar_tac
    simp only [this, ↓reduceIte, U32.cast_Usize_val_eq]
    have hl : i.val - 1 < ends.val.length := by
      have := h; simp only [Slice.length] at this; omega
    rw [getElem!_pos _ _ (by simpa using hl)]
    simp [*]

theorem slice_vals (l : List U8) (a b : Nat) :
    vals (l.slice a b) = (vals l).slice a b := by
  simp [List.slice, List.map_take, List.map_drop]

theorem entryN_eq (d e : List Nat) (i : Nat) : entryN d e i = d.slice (startN e i) e[i]! := by
  simp [entryN, List.slice]

/-- **Spec theorem for `entry_ok`**: whether entry `i` is valid, given the
    previous one is. -/
@[step]
theorem entry_ok.spec (data : Slice U8) (ends : Slice U32) (i : Usize)
    (hi : i.val < ends.length)
    (hprev : i.val = 0 ∨ EntryOk (vals data.val) (endsN ends) (i.val - 1)) :
    entry_ok data ends i ⦃ (r : Bool) =>
      (r = true ↔ EntryOk (vals data.val) (endsN ends) i.val) ⦄ := by
  unfold entry_ok
  have hil : i.val < (endsN ends).length := by simpa using hi
  step as ⟨start, hstart⟩
  step as ⟨x, hx⟩
  step as ⟨en, hen⟩
  have hend : en.val = (endsN ends)[i.val]! := by
    rw [hen, U32.cast_Usize_val_eq, hx, getElem!_pos (endsN ends) i.val hil]; simp
  split
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rintro ⟨h1, -⟩; rw [← hstart, ← hend] at h1; scalar_tac
  split
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rintro ⟨-, h2, -⟩; rw [← hend] at h2; simp at h2; scalar_tac
  rename_i hlt hle
  have h1 : startN (endsN ends) i.val < (endsN ends)[i.val]! := by rw [← hstart, ← hend]; scalar_tac
  have h2 : (endsN ends)[i.val]! ≤ (vals data.val).length := by rw [← hend]; simp; scalar_tac
  split
  · simp only [WP.spec_ok, true_iff]
    exact ⟨h1, h2, Or.inl (by scalar_tac)⟩
  rename_i hi0
  have hi0' : i.val ≠ 0 := by scalar_tac
  have hp := hprev.resolve_left hi0'
  step as ⟨i3, hi3⟩
  step as ⟨s0, hs0⟩
  have hsi : startN (endsN ends) i.val = (endsN ends)[i.val - 1]! := by
    simp [startN, hi0']
  have hs0' : s0.val < start.val := by
    rw [hs0, hi3, hstart, hsi]; exact hp.1
  step as ⟨s, hs, hsl⟩
  step as ⟨s1, hs1, hs1l⟩
  step as ⟨c, hc⟩
  simp only [WP.spec_ok, decide_eq_true_eq]
  have hvs : vals s.val = entryN (vals data.val) (endsN ends) (i.val - 1) := by
    rw [hs, slice_vals, entryN_eq, ← hsi, hs0, hi3, hstart]
  have hvs1 : vals s1.val = entryN (vals data.val) (endsN ends) i.val := by
    rw [hs1, slice_vals, entryN_eq, ← hstart, ← hend]
  rw [hvs, hvs1] at hc
  constructor
  · intro hneg
    have hcases := cmpN_cases (entryN (vals data.val) (endsN ends) (i.val - 1))
      (entryN (vals data.val) (endsN ends) i.val)
    refine ⟨h1, h2, Or.inr ?_⟩
    rcases hcases with h | h | h <;> scalar_tac
  · rintro ⟨-, -, h | h⟩
    · exact absurd h hi0'
    · rw [← hc] at h; scalar_tac

/-- **Spec theorem for `well_formed`'s loop**: the first invalid entry from
    `i`, or the end. -/
@[step]
theorem well_formed_loop.spec (data : Slice U8) (ends : Slice U32) (i : Usize)
    (hi : i.val ≤ ends.length) (hpre : ∀ j < i.val, EntryOk (vals data.val) (endsN ends) j) :
    well_formed_loop data ends i ⦃ (r : Usize) =>
      r.val ≤ ends.length ∧ (∀ j < r.val, EntryOk (vals data.val) (endsN ends) j) ∧
        (r.val < ends.length → ¬ EntryOk (vals data.val) (endsN ends) r.val) ⦄ := by
  unfold well_formed_loop
  dsimp only
  split
  · step with entry_ok.spec data ends i (by scalar_tac)
        (by
          by_cases h0 : i.val = 0
          · exact Or.inl h0
          · exact Or.inr (hpre _ (by omega))) as ⟨b, hb⟩
    split
    · rename_i hbt
      step as ⟨i2, hi2⟩
      apply well_formed_loop.spec data ends i2 (by scalar_tac)
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (hi2 ▸ hj) with hj | rfl
      · exact hpre j hj
      · exact hb.mp hbt
    · simp only [WP.spec_ok]
      rename_i hbf
      exact ⟨by scalar_tac, hpre, fun _ h => hbf (hb.mpr h)⟩
  · simp only [WP.spec_ok]
    exact ⟨hi, hpre, fun h => absurd h (by scalar_tac)⟩
termination_by ends.length - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `well_formed`**. -/
@[step]
theorem well_formed.spec (data : Slice U8) (ends : Slice U32) :
    well_formed data ends ⦃ (r : Bool) =>
      (r = true ↔ WellFormed (vals data.val) (endsN ends)) ⦄ := by
  unfold well_formed
  step as ⟨k, hk, hall, hfirst⟩
  simp only [decide_eq_true_eq, WellFormed]
  constructor
  · intro h j hj
    apply hall
    have : k.val = ends.val.length := by scalar_tac
    simp at hj; omega
  · intro h
    by_contra hne
    have hlt : k.val < ends.length := by scalar_tac
    exact hfirst hlt (h _ (by simpa using hlt))

/-- In a well-formed list, entries are in strictly increasing order. -/
theorem WellFormed.lt {d e : List Nat} (hw : WellFormed d e) {i j : Nat} (hij : i < j)
    (hj : j < e.length) : cmpN (entryN d e i) (entryN d e j) = -1 := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep : cmpN (entryN d e j) (entryN d e (j + 1)) = -1 := by
      have := (hw (j + 1) hj).2.2
      simpa using this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | rfl
    · exact cmpN_trans (ih h (by omega)) hstep
    · exact hstep

/-! ## Lookups -/

/-- **Spec theorem for `search`'s loop**: a binary search between `lo` and
    `hi`, every entry before `lo` being smaller than `name` and every entry
    from `hi` on larger. -/
@[step]
theorem search_loop.spec (data : Slice U8) (ends : Slice U32) (nm : Slice U8)
    (lo hi : Usize) (found : Bool) (hw : WellFormed (vals data.val) (endsN ends))
    (hlo : lo.val ≤ hi.val) (hhi : hi.val ≤ ends.length)
    (hl : ∀ j < lo.val, cmpN (entryN (vals data.val) (endsN ends) j) (vals nm.val) = -1)
    (hh : ∀ j, hi.val ≤ j → j < ends.length →
      cmpN (entryN (vals data.val) (endsN ends) j) (vals nm.val) = 1)
    (hf : found = true → Mem (vals data.val) (endsN ends) (vals nm.val)) :
    search_loop data ends nm lo hi found ⦃ (r : Bool) =>
      (r = true ↔ Mem (vals data.val) (endsN ends) (vals nm.val)) ⦄ := by
  -- Nothing is found outside [lo, hi): if lo = hi, nothing is found at all.
  have hout : lo.val = hi.val → ¬ Mem (vals data.val) (endsN ends) (vals nm.val) := by
    rintro heq ⟨j, hj, hjn⟩
    have hjn' : cmpN (entryN (vals data.val) (endsN ends) j) (vals nm.val) = 0 :=
      cmpN_eq_zero.mpr hjn
    by_cases hjl : j < lo.val
    · rw [hl j hjl] at hjn'; omega
    · rw [hh j (by omega) (by simpa using hj)] at hjn'; omega
  unfold search_loop
  split
  · split
    · simp only [WP.spec_ok]; rename_i hft; exact ⟨fun _ => hf hft, fun _ => hft⟩
    rename_i hlohi hff
    step as ⟨d1, hd1⟩
    step as ⟨d2, hd2⟩
    step as ⟨mid, hmid⟩
    have hmidl : mid.val < ends.length := by scalar_tac
    have hmidl' : mid.val < (endsN ends).length := by simpa using hmidl
    have hok := hw mid.val hmidl'
    step as ⟨st, hst⟩
    step as ⟨x, hx⟩
    step as ⟨en, hen⟩
    have hend : en.val = (endsN ends)[mid.val]! := by
      rw [hen, U32.cast_Usize_val_eq, hx, getElem!_pos (endsN ends) mid.val hmidl']; simp
    step as ⟨s, hs, hsl⟩
    step as ⟨c, hc⟩
    have hvs : vals s.val = entryN (vals data.val) (endsN ends) mid.val := by
      rw [hs, slice_vals, entryN_eq, hst, hend]
    rw [hvs] at hc
    split
    · rename_i hc0
      apply search_loop.spec data ends nm lo hi true hw hlo hhi hl hh
      intro _; exact ⟨mid.val, hmidl', cmpN_eq_zero.mp (by scalar_tac)⟩
    split
    · rename_i hc0 hcneg
      have hlt : cmpN (entryN (vals data.val) (endsN ends) mid.val) (vals nm.val) = -1 := by
        rcases cmpN_cases (entryN (vals data.val) (endsN ends) mid.val) (vals nm.val)
          with h | h | h <;> scalar_tac
      step as ⟨lo1, hlo1⟩
      apply search_loop.spec data ends nm lo1 hi found hw (by scalar_tac) hhi ?_ hh hf
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (hlo1 ▸ hj) with hj | rfl
      · exact cmpN_trans (hw.lt hj hmidl') hlt
      · exact hlt
    · rename_i hc0 hcneg
      have hgt : cmpN (entryN (vals data.val) (endsN ends) mid.val) (vals nm.val) = 1 := by
        rcases cmpN_cases (entryN (vals data.val) (endsN ends) mid.val) (vals nm.val)
          with h | h | h <;> scalar_tac
      apply search_loop.spec data ends nm lo mid found hw (by scalar_tac) (by scalar_tac) hl ?_ hf
      intro j hj1 hj2
      rcases Nat.lt_or_eq_of_le hj1 with hj1 | rfl
      · -- nm < entry mid < entry j
        have h1 : cmpN (vals nm.val) (entryN (vals data.val) (endsN ends) mid.val) = -1 := by
          rw [cmpN_swap, hgt]
        have h2 := cmpN_trans h1 (hw.lt hj1 (by simpa using hj2))
        rw [cmpN_swap, h2]; rfl
      · exact hgt
  · simp only [WP.spec_ok]
    rename_i hnlt
    constructor
    · intro hft; exact hf hft
    · intro hm; exact absurd hm (hout (by scalar_tac))
termination_by (hi.val - lo.val) * 2 + (if found then 0 else 1)
decreasing_by
  all_goals (cases found <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false, not_true, not_false_eq_true] at * <;> scalar_tac)

/-- **Spec theorem for `search`**: whether `nm` is an entry. -/
@[step]
theorem search.spec (data : Slice U8) (ends : Slice U32) (nm : Slice U8)
    (hw : WellFormed (vals data.val) (endsN ends)) :
    search data ends nm ⦃ (r : Bool) =>
      (r = true ↔ Mem (vals data.val) (endsN ends) (vals nm.val)) ⦄ := by
  unfold search
  apply search_loop.spec data ends nm 0#usize ends.len false hw (by simp) (by simp)
    (by intro j hj; simp at hj) ?_ (by simp)
  intro j hj1 hj2; simp [Slice.length] at hj1 hj2; omega

/-- **Spec theorem for `search_suffixes`'s loop**: looks for the parts of
    `nm` after its dots from `i` on, unless something was found. -/
@[step]
theorem search_suffixes_loop.spec (data : Slice U8) (ends : Slice U32) (nm : Slice U8)
    (found : Bool) (i : Usize) (hw : WellFormed (vals data.val) (endsN ends))
    (hi : i.val ≤ nm.length)
    (hinv : found = true ↔ Mem (vals data.val) (endsN ends) (vals nm.val) ∨
      ∃ j < i.val, (vals nm.val)[j]! = 46 ∧
        Mem (vals data.val) (endsN ends) ((vals nm.val).drop (j + 1))) :
    search_suffixes_loop data ends nm found i ⦃ (r : Bool) =>
      (r = true ↔ Blocked (vals data.val) (endsN ends) (vals nm.val)) ⦄ := by
  unfold search_suffixes_loop
  dsimp only
  split
  · split
    · simp only [WP.spec_ok]
      rename_i hft
      refine ⟨fun _ => ?_, fun _ => hft⟩
      rcases hinv.mp hft with h | ⟨j, hj, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by simp; scalar_tac, h1, h2⟩
    rename_i hlt hff
    step as ⟨c, hc⟩
    have hci : (vals nm.val)[i.val]! = c.val := by
      rw [getElem!_pos _ _ (by simp; scalar_tac)]; simp [hc]
    -- The new `found`, and what it means.
    have key : (if c = 46#u8 then (do
          let i3 ← i + 1#usize
          let s ← core.slice.index.SliceIndexRangeFromUsizeSlice.index { start := i3 } nm
          search data ends s) else ok found : Result Bool)
        ⦃ (f1 : Bool) => (f1 = true ↔ Mem (vals data.val) (endsN ends) (vals nm.val) ∨
          ∃ j < i.val + 1, (vals nm.val)[j]! = 46 ∧
            Mem (vals data.val) (endsN ends) ((vals nm.val).drop (j + 1))) ⦄ := by
      split
      · rename_i hdot
        step as ⟨i3, hi3⟩
        step as ⟨s, hs, hsl⟩
        step as ⟨f1, hf1⟩
        rw [hf1, hs, hi3]
        simp only [List.map_drop]
        constructor
        · intro h; exact Or.inr ⟨i.val, by omega, by rw [hci, hdot]; rfl, h⟩
        · rintro (h | ⟨j, hj, h1, h2⟩)
          · exact absurd (hinv.mpr (Or.inl h)) hff
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
            · exact absurd (hinv.mpr (Or.inr ⟨j, hj, h1, h2⟩)) hff
            · exact h2
      · simp only [WP.spec_ok]
        rename_i hdot
        rw [hinv]
        constructor
        · rintro (h | ⟨j, hj, h1, h2⟩)
          · exact Or.inl h
          · exact Or.inr ⟨j, by omega, h1, h2⟩
        · rintro (h | ⟨j, hj, h1, h2⟩)
          · exact Or.inl h
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
            · exact Or.inr ⟨j, hj, h1, h2⟩
            · exfalso; apply hdot; rw [hci] at h1; scalar_tac
    step with key as ⟨f1, hf1⟩
    step as ⟨i4, hi4⟩
    apply search_suffixes_loop.spec data ends nm f1 i4 hw (by scalar_tac)
    rw [hi4]; exact hf1
  · simp only [WP.spec_ok]
    have hil : i.val = (vals nm.val).length := by simp; scalar_tac
    rw [hinv, Blocked, hil]
termination_by nm.length - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `search_suffixes`**: whether `nm` is blocked. -/
@[step]
theorem search_suffixes.spec (data : Slice U8) (ends : Slice U32) (nm : Slice U8)
    (hw : WellFormed (vals data.val) (endsN ends)) :
    search_suffixes data ends nm ⦃ (r : Bool) =>
      (r = true ↔ Blocked (vals data.val) (endsN ends) (vals nm.val)) ⦄ := by
  unfold search_suffixes
  step as ⟨f, hf⟩
  apply search_suffixes_loop.spec data ends nm f 0#usize hw (by simp)
  rw [hf]; simp

/-! ## `Blocklist` -/

/-- A list built by `Blocklist::new`: well formed. -/
def Blocklist.Inv (b : Blocklist) : Prop := WellFormed (vals b.data.val) (endsN b.ends)

/-- The entries of a list are its domains. -/
abbrev Blocklist.Mem (b : Blocklist) (n : List Nat) : Prop := blocklist.Mem (vals b.data.val) (endsN b.ends) n

/-- **Spec theorem for `Blocklist::new`**: the list, if well formed. -/
@[step]
theorem Blocklist.new.spec (data : Slice U8) (ends : Slice U32) :
    Blocklist.new data ends ⦃ (r : Option Blocklist) =>
      match r with
      | some b => b.data = data ∧ b.ends = ends ∧ b.Inv
      | none => ¬ WellFormed (vals data.val) (endsN ends) ⦄ := by
  unfold Blocklist.new
  step as ⟨w, hw⟩
  split
  · simp only [WP.spec_ok]; rename_i h; refine ⟨?_, ?_, hw.mp h⟩ <;> trivial
  · simp only [WP.spec_ok]; rename_i h; exact fun h' => h (hw.mpr h')

/-- **Spec theorem for `Blocklist::len`**. -/
@[step]
theorem Blocklist.len.spec (b : Blocklist) :
    Blocklist.len b ⦃ (r : Usize) => r.val = b.ends.length ⦄ := by
  unfold Blocklist.len; simp

/-- **Spec theorem for `Blocklist::is_empty`**. -/
@[step]
theorem Blocklist.is_empty.spec (b : Blocklist) :
    Blocklist.is_empty b ⦃ (r : Bool) => (r = true ↔ b.ends.length = 0) ⦄ := by
  unfold Blocklist.is_empty; step*

/-- **Spec theorem for `Blocklist::contains`**: whether `nm` is an entry. -/
@[step]
theorem Blocklist.contains.spec (b : Blocklist) (hb : b.Inv) (nm : Slice U8) :
    Blocklist.contains b nm ⦃ (r : Bool) =>
      (r = true ↔ blocklist.Mem (vals b.data.val) (endsN b.ends) (vals nm.val)) ⦄ := by
  unfold Blocklist.contains; unfold Blocklist.Inv at hb; step*

/-- **Spec theorem for `Blocklist::blocked`**: whether `nm` is a listed domain
    or a subdomain of one (see `blocked_iff`). -/
@[step]
theorem Blocklist.blocked.spec (b : Blocklist) (hb : b.Inv) (nm : Slice U8) :
    Blocklist.blocked b nm ⦃ (r : Bool) =>
      (r = true ↔ Blocked (vals b.data.val) (endsN b.ends) (vals nm.val)) ⦄ := by
  unfold Blocklist.blocked; unfold Blocklist.Inv at hb; step*

end adfilter.blocklist
