/- Specs of `wireguard::allowed_ips`: cryptokey routing. `lookup` returns the
   peer of the longest prefix matching an address; `insert` adds a prefix,
   or replaces the peer of an equal one, keeping each prefix unique. -/
import Wireguard.Funs
import Untrusted

open Aeneas Aeneas.Std Result

namespace wireguard.allowed_ips

/-! ## The specification -/

/-- The address width of a family. -/
def widthN (v6 : Bool) : Nat := if v6 then 128 else 32

/-- `ip` with its bits after the first `len` (of the family's width) cleared:
    the prefix of length `len` it belongs to. -/
def canon (v6 : Bool) (ip len : Nat) : Nat :=
  if 128 ≤ widthN v6 - len then 0 else ip / 2 ^ (widthN v6 - len) * 2 ^ (widthN v6 - len)

/-- The entry `e` is a prefix of `ip`, in the family `v6`. -/
def Matches (e : AllowedIp) (v6 : Bool) (ip : Nat) : Prop :=
  e.v6 = v6 ∧ canon v6 ip e.len.val = e.addr.val

/-- The entries in use. -/
def inUse (t : AllowedIps) : List AllowedIp := t.entries.val.take t.count.val

/-- An entry's key: its family, length and prefix. -/
def key (e : AllowedIp) : Bool × Nat × Nat := (e.v6, e.len.val, e.addr.val)

/-- The table's invariant: within capacity, prefixes valid and canonical, and
    no prefix twice. -/
def Inv (t : AllowedIps) : Prop :=
  t.count.val ≤ 1024 ∧
    (∀ e ∈ inUse t, e.len.val ≤ widthN e.v6 ∧ canon e.v6 e.addr.val e.len.val = e.addr.val) ∧
    (inUse t).Pairwise (fun a b => key a ≠ key b)

/-- `e` is a longest prefix of `ip` in the table. -/
def Longest (t : AllowedIps) (v6 : Bool) (ip : Nat) (e : AllowedIp) : Prop :=
  e ∈ inUse t ∧ Matches e v6 ip ∧ ∀ e' ∈ inUse t, Matches e' v6 ip → e'.len.val ≤ e.len.val

instance : Std.Symm (fun a b : AllowedIp => key a ≠ key b) := ⟨fun _ _ h => Ne.symm h⟩

/-- There is at most one longest prefix: two of the same length are the same
    prefix, and prefixes are unique. -/
theorem Longest.unique {t : AllowedIps} (hinv : Inv t) {v6 : Bool} {ip : Nat} {e e' : AllowedIp}
    (h : Longest t v6 ip e) (h' : Longest t v6 ip e') : e = e' := by
  have hlen : e.len.val = e'.len.val := le_antisymm (h'.2.2 e h.1 h.2.1) (h.2.2 e' h'.1 h'.2.1)
  have hkey : key e = key e' := by
    simp only [key, Prod.mk.injEq]
    exact ⟨h.2.1.1.trans h'.2.1.1.symm, hlen, by rw [← h.2.1.2, ← h'.2.1.2, hlen]⟩
  by_contra hne
  exact hinv.2.2.forall h.1 h'.1 hne hkey

/-! ## Scanning for the longest match -/

/-- After scanning the entries `l`, `best` is none if none matched, else a
    matching entry of `l` of greatest length. -/
def Best (l : List AllowedIp) (v6 : Bool) (ip : Nat) (best : Option AllowedIp) : Prop :=
  (best = none → ∀ e ∈ l, ¬ Matches e v6 ip) ∧
    ∀ b, best = some b → b ∈ l ∧ Matches b v6 ip ∧ ∀ e ∈ l, Matches e v6 ip → e.len.val ≤ b.len.val

open Classical in
/-- One step of the scan, as `lookup` takes it. -/
noncomputable def scanStep (v6 : Bool) (ip : Nat) (best : Option AllowedIp) (e : AllowedIp) :
    Option AllowedIp :=
  if Matches e v6 ip then
    match best with
    | some b => if e.len.val ≤ b.len.val then some b else some e
    | none => some e
  else best

theorem Best.nil (v6 : Bool) (ip : Nat) : Best [] v6 ip none :=
  ⟨fun _ e he => absurd he (List.not_mem_nil), fun _ h => (by cases h)⟩

theorem Best.step {l : List AllowedIp} {v6 : Bool} {ip : Nat} {best : Option AllowedIp}
    (h : Best l v6 ip best) (e : AllowedIp) : Best (l ++ [e]) v6 ip (scanStep v6 ip best e) := by
  unfold scanStep
  by_cases hm : Matches e v6 ip
  · simp only [hm, ↓reduceIte]
    rcases best with _ | b
    · refine ⟨fun h => (by cases h), fun b' hb' => ?_⟩
      cases hb'
      refine ⟨by simp, hm, fun e' he' hm' => ?_⟩
      rcases List.mem_append.mp he' with h1 | h1
      · exact absurd hm' (h.1 rfl e' h1)
      · simp at h1; rw [h1]
    · obtain ⟨hbl, hbm, hbmax⟩ := h.2 b rfl
      by_cases hle : e.len.val ≤ b.len.val
      · simp only [hle, ↓reduceIte]
        refine ⟨fun h => (by cases h), fun b' hb' => ?_⟩
        cases hb'
        refine ⟨by simp [hbl], hbm, fun e' he' hm' => ?_⟩
        rcases List.mem_append.mp he' with h1 | h1
        · exact hbmax e' h1 hm'
        · simp at h1; rw [h1]; exact hle
      · simp only [hle, ↓reduceIte]
        refine ⟨fun h => (by cases h), fun b' hb' => ?_⟩
        cases hb'
        refine ⟨by simp, hm, fun e' he' hm' => ?_⟩
        rcases List.mem_append.mp he' with h1 | h1
        · have := hbmax e' h1 hm'; omega
        · simp at h1; rw [h1]
  · simp only [hm, ↓reduceIte]
    refine ⟨fun hn e' he' => ?_, fun b hb => ?_⟩
    · rcases List.mem_append.mp he' with h1 | h1
      · exact h.1 hn e' h1
      · simp at h1; rw [h1]; exact hm
    · obtain ⟨hbl, hbm, hbmax⟩ := h.2 b hb
      refine ⟨by simp [hbl], hbm, fun e' he' hm' => ?_⟩
      rcases List.mem_append.mp he' with h1 | h1
      · exact hbmax e' h1 hm'
      · simp at h1; rw [h1] at hm'; exact absurd hm' hm

/-! ## Specs -/

@[simp, scalar_tac_simps] theorem MAX_ALLOWED_IPS_val : MAX_ALLOWED_IPS.val = 1024 := by
  simp [MAX_ALLOWED_IPS]

theorem widthN_le (v6 : Bool) : widthN v6 ≤ 128 := by cases v6 <;> simp [widthN]

/-- **Spec theorem for `width`**. -/
@[step]
theorem width.spec (v6 : Bool) : width v6 ⦃ (r : U32) => r.val = widthN v6 ⦄ := by
  unfold width
  cases v6 <;> simp [widthN]

/-- **Spec theorem for `block`**: `2^(width - len)`, if below `2^128`. -/
@[step]
theorem block.spec (v6 : Bool) (len : U32) (h : len.val ≤ widthN v6) :
    block v6 len ⦃ (r : Option U128) =>
      match r with
      | none => 128 ≤ widthN v6 - len.val
      | some b => widthN v6 - len.val < 128 ∧ b.val = 2 ^ (widthN v6 - len.val) ⦄ := by
  unfold block
  step*
  have hh : host_bits.val = widthN v6 - len.val := by scalar_tac
  have hlt : host_bits.val < 128 := by scalar_tac
  refine ⟨by omega, ?_⟩
  rw [i1_post, Nat.one_shiftLeft, Nat.mod_eq_of_lt, hh]
  simp only [U128.size, U128.numBits]
  exact Nat.pow_lt_pow_right (by omega) hlt

/-- **Spec theorem for `canonical`**: the prefix of length `len` of `addr`. -/
@[step]
theorem canonical.spec (v6 : Bool) (addr : U128) (len : U32) (h : len.val ≤ widthN v6) :
    canonical v6 addr len ⦃ (r : U128) => r.val = canon v6 addr.val len.val ⦄ := by
  unfold canonical
  step as ⟨ o, ho ⟩
  rcases o with _ | b
  · simp only [WP.spec_ok, canon]
    simp only at ho
    simp [ho]
  · obtain ⟨hlt, hb⟩ := ho
    have hb0 : 0 < b.val := by rw [hb]; exact Nat.two_pow_pos _
    have hle : addr.val / b.val * b.val ≤ addr.val := Nat.div_mul_le_self _ _
    step*
    simp only [canon, show ¬ 128 ≤ widthN v6 - len.val by omega, ↓reduceIte]
    rw [r_post, i_post, hb]

/-- **Spec theorem for `matches`**. -/
@[step]
theorem matches.spec (v6 : Bool) (addr : U128) (len : U32) (ip : U128) (h : len.val ≤ widthN v6) :
    allowed_ips.matches v6 addr len ip ⦃ (r : Bool) => r = decide (canon v6 ip.val len.val = addr.val) ⦄ := by
  unfold allowed_ips.matches
  step*

theorem length_inUse (t : AllowedIps) (h : t.count.val ≤ 1024) : (inUse t).length = t.count.val := by
  simp [inUse]; omega

/-- **Spec theorem for the loop of `lookup`**: scans the entries from `i`. -/
@[step]
theorem AllowedIps.lookup_loop.spec (t : AllowedIps) (hinv : Inv t) (v6 : Bool) (ip : U128)
    (best : Option AllowedIp) (i : Usize) (hi : i.val ≤ t.count.val)
    (hb : Best ((inUse t).take i.val) v6 ip.val best) :
    AllowedIps.lookup_loop t v6 ip best i ⦃ (r : Option AllowedIp) =>
      Best (inUse t) v6 ip.val r ⦄ := by
  unfold AllowedIps.lookup_loop
  split
  · have hlt : i.val < (inUse t).length := by rw [length_inUse t hinv.1]; scalar_tac
    step as ⟨ e, he ⟩
    have heq : e = (inUse t)[i.val] := by
      simp only [inUse, List.getElem_take]; rw [he]
    have hmem : e ∈ inUse t := by rw [heq]; exact List.getElem_mem hlt
    have htake : (inUse t).take (i.val + 1) = (inUse t).take i.val ++ [e] := by
      rw [heq]; exact List.take_succ_eq_append_getElem hlt
    have hstep := hb.step e
    rw [← htake] at hstep
    have hw := (hinv.2.1 e hmem).1
    -- The entry rebuilt field by field (with `v6` for `e.v6`) is `e`.
    have hre : e.v6 = v6 →
        ({ v6 := v6, addr := e.addr, len := e.len, peer := e.peer } : AllowedIp) = e := by
      intro h; cases e; simp_all
    by_cases hv : e.v6 = v6
    · simp only [hv, ↓reduceIte]
      have hw' : e.len.val ≤ widthN v6 := hv ▸ hw
      step as ⟨ b, hbm ⟩
      by_cases hm : canon v6 ip.val e.len.val = e.addr.val
      · have hM : Matches e v6 ip.val := ⟨hv, hm⟩
        simp only [hbm, hm, decide_true, ↓reduceIte]
        rcases best with _ | b2
        · simp only [bind_ok]
          step as ⟨ i1, hi1 ⟩
          apply AllowedIps.lookup_loop.spec t hinv v6 ip _ i1 (by scalar_tac)
          rw [hi1, hre hv]; simpa [scanStep, hM] using hstep
        · by_cases hle : e.len.val ≤ b2.len.val
          · have hge : b2.len ≥ e.len := by scalar_tac
            simp only [hge, ↓reduceIte, bind_ok]
            step as ⟨ i1, hi1 ⟩
            apply AllowedIps.lookup_loop.spec t hinv v6 ip _ i1 (by scalar_tac)
            rw [hi1]; simpa [scanStep, hM, hle] using hstep
          · have hge : ¬ b2.len ≥ e.len := by scalar_tac
            simp only [hge, ↓reduceIte, bind_ok]
            step as ⟨ i1, hi1 ⟩
            apply AllowedIps.lookup_loop.spec t hinv v6 ip _ i1 (by scalar_tac)
            rw [hi1, hre hv]; simpa [scanStep, hM, hle] using hstep
      · have hM : ¬ Matches e v6 ip.val := fun h => hm h.2
        simp only [hbm, hm, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
        step as ⟨ i1, hi1 ⟩
        apply AllowedIps.lookup_loop.spec t hinv v6 ip _ i1 (by scalar_tac)
        rw [hi1]; simpa [scanStep, hM] using hstep
    · have hM : ¬ Matches e v6 ip.val := fun h => hv h.1
      simp only [hv, ↓reduceIte, bind_ok]
      step as ⟨ i1, hi1 ⟩
      apply AllowedIps.lookup_loop.spec t hinv v6 ip _ i1 (by scalar_tac)
      rw [hi1]; simpa [scanStep, hM] using hstep
  · simp only [WP.spec_ok]
    have : i.val = (inUse t).length := by rw [length_inUse t hinv.1]; scalar_tac
    rw [this, List.take_length] at hb
    exact hb
termination_by t.count.val - i.val
decreasing_by all_goals scalar_tac


/-- **Spec theorem for `lookup`**: the peer of the longest prefix matching
    `ip` (unique, by `Longest.unique`), or none if no prefix matches. -/
@[step]
theorem AllowedIps.lookup.spec (t : AllowedIps) (hinv : Inv t) (v6 : Bool) (ip : U128) :
    AllowedIps.lookup t v6 ip ⦃ (r : Option U16) =>
      match r with
      | none => ∀ e ∈ inUse t, ¬ Matches e v6 ip.val
      | some p => ∃ e, Longest t v6 ip.val e ∧ e.peer = p ⦄ := by
  unfold AllowedIps.lookup
  step with AllowedIps.lookup_loop.spec t hinv v6 ip none 0#usize (by simp)
    (by simpa using Best.nil v6 ip.val) as ⟨ best, hbest ⟩
  rcases best with _ | b
  · simpa using hbest.1 rfl
  · obtain ⟨h1, h2, h3⟩ := hbest.2 b rfl
    simpa using ⟨b, ⟨h1, h2, h3⟩, rfl⟩


/-- **Spec theorem for the loop of `find`**: the first index from `i` holding
    the key `(v6, len, addr)`, or `count`. -/
@[step]
theorem AllowedIps.find_loop.spec (t : AllowedIps) (hc : t.count.val ≤ 1024) (v6 : Bool) (addr : U128)
    (len : U32) (i : Usize) (hi : i.val ≤ t.count.val)
    (hpre : ∀ j (h : j < i.val), key ((inUse t)[j]'(by rw [length_inUse t hc]; omega)) ≠
      (v6, len.val, addr.val)) :
    AllowedIps.find_loop t v6 addr len i ⦃ (r : Usize) =>
      ∃ hr : r.val ≤ t.count.val,
        (∀ j (h : j < r.val), key ((inUse t)[j]'(by rw [length_inUse t hc]; omega)) ≠
          (v6, len.val, addr.val)) ∧
        ∀ h : r.val < t.count.val,
          key ((inUse t)[r.val]'(by rw [length_inUse t hc]; omega)) = (v6, len.val, addr.val) ⦄ := by
  unfold AllowedIps.find_loop
  split
  · have hlt : i.val < (inUse t).length := by rw [length_inUse t hc]; scalar_tac
    step as ⟨ e, he ⟩
    have heq : e = (inUse t)[i.val] := by simp only [inUse, List.getElem_take]; rw [he]
    by_cases hk : key e = (v6, len.val, addr.val)
    · have h1 : e.v6 = v6 := by simp [key] at hk; exact hk.1
      have h2 : e.len = len := (UScalar.eq_equiv _ _).mpr (by simp [key] at hk; exact hk.2.1)
      have h3 : e.addr = addr := (UScalar.eq_equiv _ _).mpr (by simp [key] at hk; exact hk.2.2)
      simp only [h1, h2, h3, ↓reduceIte, WP.spec_ok]
      exact ⟨by scalar_tac, hpre, fun _ => by rw [← heq]; exact hk⟩
    · have hnext : ∀ j (h : j < i.val + 1), key ((inUse t)[j]'(by omega)) ≠ (v6, len.val, addr.val) := by
        intro j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
        · exact hpre j h
        · subst h; rw [← heq]; exact hk
      have hcases : ¬ (e.v6 = v6 ∧ e.len = len ∧ e.addr = addr) := by
        rintro ⟨a, b, c⟩; apply hk; simp [key, a, b, c]
      split
      · split
        · split
          · exact absurd ⟨‹_›, ‹_›, ‹_›⟩ hcases
          · step as ⟨ i1, hi1 ⟩
            apply AllowedIps.find_loop.spec t hc v6 addr len i1 (by scalar_tac)
            intro j hj; exact hnext j (by omega)
        · step as ⟨ i1, hi1 ⟩
          apply AllowedIps.find_loop.spec t hc v6 addr len i1 (by scalar_tac)
          intro j hj; exact hnext j (by omega)
      · step as ⟨ i1, hi1 ⟩
        apply AllowedIps.find_loop.spec t hc v6 addr len i1 (by scalar_tac)
        intro j hj; exact hnext j (by omega)
  · simp only [WP.spec_ok]
    exact ⟨hi, hpre, fun h => by scalar_tac⟩
termination_by t.count.val - i.val
decreasing_by all_goals scalar_tac


/-- **Spec theorem for `find`**. -/
@[step]
theorem AllowedIps.find.spec (t : AllowedIps) (hc : t.count.val ≤ 1024) (v6 : Bool) (addr : U128)
    (len : U32) :
    AllowedIps.find t v6 addr len ⦃ (r : Usize) =>
      ∃ hr : r.val ≤ t.count.val,
        (∀ j (h : j < r.val), key ((inUse t)[j]'(by rw [length_inUse t hc]; omega)) ≠
          (v6, len.val, addr.val)) ∧
        ∀ h : r.val < t.count.val,
          key ((inUse t)[r.val]'(by rw [length_inUse t hc]; omega)) = (v6, len.val, addr.val) ⦄ := by
  unfold AllowedIps.find
  exact AllowedIps.find_loop.spec t hc v6 addr len 0#usize (by simp) (fun j h => by simp at h)

/-- A valid prefix: its length within the family's width, and an IPv4
    address within 32 bits. -/
def Valid (v6 : Bool) (addr len : Nat) : Prop :=
  len ≤ widthN v6 ∧ (v6 = false → addr < 2 ^ 32)

/-- **Spec theorem for `valid`**. -/
@[step]
theorem valid.spec (v6 : Bool) (addr : U128) (len : U32) :
    valid v6 addr len ⦃ (r : Bool) => (r = true ↔ Valid v6 addr.val len.val) ⦄ := by
  unfold valid
  step*
  all_goals simp_all [Valid, U32.rMax, U32.numBits] <;> omega

open Classical in
/-- The entries after allowing the prefix of `e` for `e.peer`: the peer of an
    equal prefix replaced, or `e` appended. -/
noncomputable def insertSpec (l : List AllowedIp) (e : AllowedIp) : List AllowedIp :=
  if ∃ x ∈ l, key x = key e then
    l.map (fun x => if key x = key e then { x with peer := e.peer } else x)
  else l ++ [e]

/-- Replacing the peer at the index of a key is replacing it at that key,
    since keys are unique. -/
theorem set_peer_eq_map (l : List AllowedIp) (hl : l.Pairwise (fun a b => key a ≠ key b))
    (i : Nat) (hi : i < l.length) (p : U16) :
    l.set i { l[i] with peer := p } =
      l.map (fun x => if key x = key l[i] then { x with peer := p } else x) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_set, List.getElem_map]
  by_cases hij : i = j
  · subst hij; simp
  · have hj : j < l.length := by simpa using h1
    have hk : key l[j] ≠ key l[i] := by
      rw [List.pairwise_iff_getElem] at hl
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact Ne.symm (hl i j hi hj h)
      · exact hl j i hj hi h
    simp [hij, hk]


theorem canon_idem (v6 : Bool) (x len : Nat) : canon v6 (canon v6 x len) len = canon v6 x len := by
  by_cases hc : 128 ≤ widthN v6 - len <;> simp [canon, hc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem take_set_succ'' {α : Type} (l : List α) (i : Nat) (x : α) (h : i < l.length) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, List.getElem?_set_self h]
  simp [List.take_set_of_le]

/-- **Spec theorem for `insert`**: on a valid prefix, replaces the peer of
    the equal prefix if there is one, else appends it if there is room; the
    result says whether it did. The invariant is kept. -/
@[step]
theorem AllowedIps.insert.spec (t : AllowedIps) (hinv : Inv t) (v6 : Bool) (addr : U128) (len : U32)
    (peer : U16) :
    AllowedIps.insert t v6 addr len peer ⦃ (b : Bool) (t' : AllowedIps) =>
      Inv t' ∧ (b = false → t' = t) ∧
      (b = true ↔ Valid v6 addr.val len.val ∧
        ((∃ x ∈ inUse t, key x = (v6, len.val, canon v6 addr.val len.val)) ∨ t.count.val < 1024)) ∧
      (b = true → ∃ a : U128, a.val = canon v6 addr.val len.val ∧
        inUse t' = insertSpec (inUse t) { v6, addr := a, len, peer }) ⦄ := by
  unfold AllowedIps.insert
  step as ⟨ ok, hok ⟩
  by_cases hV : Valid v6 addr.val len.val
  swap
  · have hf : ok = false := by
      cases ok
      · rfl
      · exact absurd (hok.mp rfl) hV
    simp only [hf, Bool.false_eq_true, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
    refine ⟨hinv, fun _ => trivial, ?_, ?_⟩
    · simp only [Bool.false_eq_true, false_iff, not_and]; exact fun h => absurd h hV
    · simp
  · have ht : ok = true := hok.mpr hV
    simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    step as ⟨ ca, hca ⟩
    step as ⟨ i, hi, hbefore, hat ⟩
    split
    · step*
      have hlt : i.val < t.count.val := by scalar_tac
      have hl : i.val < (inUse t).length := by rw [length_inUse t hinv.1]; exact hlt
      have hai : ai = (inUse t)[i.val] := by rw [ai_post]; simp [inUse]
      have hkey : key (inUse t)[i.val] = (v6, len.val, ca.val) := hat hlt
      have hkf : ∀ x : AllowedIp, key (if key x = (v6, len.val, ca.val) then { x with peer := peer } else x)
          = key x := by intro x; split <;> rfl
      have hnew : inUse ⟨index_mut_back ⟨ai.v6, ai.addr, ai.len, peer⟩, t.count⟩ =
          (inUse t).map (fun x => if key x = (v6, len.val, ca.val) then { x with peer := peer } else x) := by
        rw [index_mut_back_post]
        simp only [inUse, Array.set_val_eq, List.take_set]
        rw [show ({ v6 := ai.v6, addr := ai.addr, len := ai.len, peer := peer } : AllowedIp) =
          { (inUse t)[i.val] with peer := peer } by rw [hai]]
        rw [show t.entries.val.take t.count.val = inUse t from rfl,
          set_peer_eq_map _ hinv.2.2 _ hl, hkey]
      have hex : ∃ x ∈ inUse t, key x = key ({ v6, addr := ca, len, peer } : AllowedIp) :=
        ⟨_, List.getElem_mem hl, hkey⟩
      refine ⟨⟨hinv.1, ?_, ?_⟩, by simp, ?_, ?_⟩
      · rw [hnew]
        intro e he
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
        have := hinv.2.1 x hx
        split <;> exact this
      · rw [hnew, List.pairwise_map]
        exact hinv.2.2.imp (fun {x y} hxy => by rw [hkf x, hkf y]; exact hxy)
      · simp only [true_iff]
        exact ⟨hV, Or.inl ⟨_, List.getElem_mem hl, by rw [hkey, hca]⟩⟩
      · intro _
        exact ⟨ca, hca, by rw [hnew, insertSpec, if_pos hex]; rfl⟩
    · have hic : i.val = t.count.val := by scalar_tac
      have hnone : ∀ x ∈ inUse t, key x ≠ (v6, len.val, ca.val) := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
        rw [length_inUse t hinv.1] at hj
        exact hbefore j (by omega)
      split
      · simp only [WP.spec_ok, WP.uncurry'_pair]
        refine ⟨hinv, fun _ => trivial, ?_, ?_⟩
        · simp only [Bool.false_eq_true, false_iff, not_and, not_or]
          intro _
          refine ⟨fun ⟨x, hx, hk⟩ => hnone x hx (by rw [hk, hca]), by scalar_tac⟩
        · simp
      · step*
        have hc64 := hinv.1
        have hcl : t.count.val < 1024 := by scalar_tac
        have hnew : inUse { entries := a, count := i1 } = inUse t ++ [{ v6, addr := ca, len, peer }] := by
          simp only [inUse]
          rw [a_post, Array.set_val_eq, i1_post, take_set_succ'' _ _ _ (by simp; omega)]
        have hnex : ¬ ∃ x ∈ inUse t, key x = key ({ v6, addr := ca, len, peer } : AllowedIp) :=
          fun ⟨x, hx, hk⟩ => hnone x hx hk
        refine ⟨⟨by scalar_tac, ?_, ?_⟩, by simp, ?_, ?_⟩
        · rw [hnew]
          intro e he
          rcases List.mem_append.mp he with h | h
          · exact hinv.2.1 e h
          · simp at h; subst h
            exact ⟨hV.1, by simp only; rw [hca, canon_idem]⟩
        · rw [hnew, List.pairwise_append]
          refine ⟨hinv.2.2, List.pairwise_singleton _ _, ?_⟩
          intro x hx y hy
          simp at hy; subst hy
          exact hnone x hx
        · simp only [true_iff]; exact ⟨hV, Or.inr hcl⟩
        · intro _
          exact ⟨ca, hca, by rw [hnew, insertSpec, if_neg hnex]⟩


/-- **Spec theorem for `AllowedIps::new`**: an empty table. -/
@[step]
theorem AllowedIps.new.spec : AllowedIps.new ⦃ (t : AllowedIps) => Inv t ∧ inUse t = [] ⦄ := by
  unfold AllowedIps.new
  simp [Inv, inUse]

/-- **Spec theorem for `<AllowedIps as Default>::default`**. -/
@[step]
theorem AllowedIps.Insts.CoreDefaultDefault.default.spec :
    AllowedIps.Insts.CoreDefaultDefault.default ⦃ (t : AllowedIps) => Inv t ∧ inUse t = [] ⦄ := by
  unfold AllowedIps.Insts.CoreDefaultDefault.default
  step*

/-! ## Removing a peer -/

deriving instance Inhabited for AllowedIp

/-- The prefixes not of `peer`. -/
def keep (peer : U16) (l : List AllowedIp) : List AllowedIp := l.filter (fun e => e.peer != peer)

theorem set_ne! {α : Type} [Inhabited α] (l : List α) (i j : Nat) (v : α) (h : j ≠ i) :
    (l.set i v)[j]! = l[j]! := by simp [Ne.symm h]

theorem inUse_getElem! (t : AllowedIps) (j : Nat) (hj : j < t.count.val) (hc : t.count.val ≤ 1024) :
    (inUse t)[j]! = t.entries.val[j]! := by
  unfold inUse
  rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega)]
  simp

/-- **Spec theorem for `AllowedIps::remove_peer`'s loop**: `entries[..kept]`
    holds the prefixes not of `peer` among the first `i` of `orig`, and the
    rest of `orig` is still in place. -/
@[step]
theorem AllowedIps.remove_peer_loop.spec (t : AllowedIps) (peer : U16) (kept i : Usize)
    (orig : List AllowedIp) (hc : t.count.val ≤ 1024) (hlen : orig.length = t.count.val)
    (hk : kept.val ≤ i.val) (hi : i.val ≤ t.count.val)
    (hpre : t.entries.val.take kept.val = keep peer (orig.take i.val))
    (hrest : ∀ j, i.val ≤ j → j < t.count.val → t.entries.val[j]! = orig[j]!) :
    AllowedIps.remove_peer_loop t peer kept i ⦃ (r : Array AllowedIp 1024#usize × Usize) =>
      r.2.val ≤ t.count.val ∧ r.1.val.take r.2.val = keep peer orig ⦄ := by
  unfold AllowedIps.remove_peer_loop
  have hel : t.entries.val.length = 1024 := by simp
  split
  · step as ⟨e, he⟩
    have hic : i.val < t.count.val := by scalar_tac
    have heo : e = orig[i.val]! := by
      rw [he, ← hrest i.val (le_refl _) (by scalar_tac), getElem!_pos _ _ (by omega)]
    have htake : orig.take (i.val + 1) = orig.take i.val ++ [e] := by
      rw [heo, getElem!_pos _ _ (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    split
    · rename_i hne
      step as ⟨a, ha⟩
      step as ⟨k1, hk1⟩
      step as ⟨i1, hi1⟩
      have hpre' : a.val.take k1.val = keep peer (orig.take i1.val) := by
        rw [ha, Array.set_val_eq, hk1, take_set_succ'' _ _ _ (by omega), hpre, hi1, htake]
        simp [keep, hne]
      have hrest' : ∀ j, i1.val ≤ j → j < t.count.val → a.val[j]! = orig[j]! := by
        intro j hj1 hj2
        rw [ha, Array.set_val_eq, set_ne! _ _ _ _ (by omega)]
        exact hrest j (by omega) hj2
      exact AllowedIps.remove_peer_loop.spec { t with entries := a } peer k1 i1 orig hc hlen
        (by scalar_tac) (by simp only; scalar_tac) hpre' hrest'
    · rename_i heq
      step as ⟨i1, hi1⟩
      have hpre' : t.entries.val.take kept.val = keep peer (orig.take i1.val) := by
        rw [hpre, hi1, htake]
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
        simp [keep, heq]
      exact AllowedIps.remove_peer_loop.spec t peer kept i1 orig hc hlen (by scalar_tac)
        (by scalar_tac) hpre' (fun j hj1 hj2 => hrest j (by omega) hj2)
  · simp only [WP.spec_ok]
    have : i.val = t.count.val := by scalar_tac
    refine ⟨by omega, ?_⟩
    rw [hpre, this, ← hlen, List.take_length]
termination_by t.count.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `AllowedIps::remove_peer`**: the prefixes of `peer`
    go, the others stay, in order. -/
@[step]
theorem AllowedIps.remove_peer.spec (t : AllowedIps) (hinv : Inv t) (peer : U16) :
    AllowedIps.remove_peer t peer ⦃ (t' : AllowedIps) =>
      Inv t' ∧ inUse t' = keep peer (inUse t) ⦄ := by
  unfold AllowedIps.remove_peer
  have hc := hinv.1
  step with AllowedIps.remove_peer_loop.spec t peer 0#usize 0#usize (inUse t) hc
    (length_inUse t hc) (by simp) (by simp) (by simp [keep])
    (fun j _ hj => (inUse_getElem! t j hj hc).symm)
    as ⟨a, kept, hk, hka⟩
  have hu : inUse { entries := a, count := kept } = keep peer (inUse t) := hka
  refine ⟨⟨by simp only; omega, fun e he => ?_, ?_⟩, hu⟩
  · rw [hu] at he
    exact hinv.2.1 e (List.mem_of_mem_filter he)
  · rw [hu]; exact hinv.2.2.filter _

end wireguard.allowed_ips
