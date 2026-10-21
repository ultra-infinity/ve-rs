/- Specs of `diomede::stream`: the start of TCP connections to port 443,
   reassembled. Every connection in use carries the decision on the bytes
   collected for it (`Decided`), so a connection is blocked only when its
   first record is a ClientHello for a blocked name. -/
import Diomede.FilterTop

open Aeneas Aeneas.Std Result untrusted

namespace diomede.stream

open filter

deriving instance Inhabited for Key
deriving instance Inhabited for Flow

@[simp, scalar_tac_simps] theorem MAX_FLOWS_val : MAX_FLOWS.val = 256 := by simp [MAX_FLOWS]
@[simp, scalar_tac_simps] theorem MAX_RECORD_val : MAX_RECORD.val = 8192 := by simp [MAX_RECORD]
@[simp, scalar_tac_simps] theorem FREE_val : FREE.val = 0 := by simp [FREE]
@[simp, scalar_tac_simps] theorem COLLECTING_val : COLLECTING.val = 1 := by simp [COLLECTING]
@[simp, scalar_tac_simps] theorem PASSED_val : PASSED.val = 2 := by simp [PASSED]
@[simp, scalar_tac_simps] theorem BLOCKED_val : BLOCKED.val = 3 := by simp [BLOCKED]

/-! ## Decisions -/

/-- The length of the first TLS record of `b`, from its header. -/
def needOf (b : List U8) : Nat := 5 + b[3]!.val * 256 + b[4]!.val

/-- The state `st` is the decision on the first bytes `b` of a connection:
    collecting (1) until the first record is complete; then blocked (3) if
    it is a ClientHello for a name `list` blocks, else passed (2). A first
    record that is not a handshake record, or longer than 8192 bytes,
    passes. -/
def Decided (list : blocklist.Blocklist) (b : List U8) (st : Nat) : Prop :=
  if b.length < 5 then st = 1
  else if b[0]!.val ≠ 22 then st = 2
  else if 8192 < needOf b then st = 2
  else if b.length < needOf b then st = 1
  else (st = 2 ∨ st = 3) ∧ (st = 3 ↔ HelloBlocked list (b.take (needOf b)))

/-- A blocked decision carries its evidence. -/
theorem Decided.blocked {list : blocklist.Blocklist} {b : List U8} (h : Decided list b 3) :
    5 ≤ b.length ∧ b[0]!.val = 22 ∧ needOf b ≤ b.length ∧ HelloBlocked list (b.take (needOf b)) := by
  unfold Decided at h
  split at h
  · omega
  split at h
  · omega
  split at h
  · omega
  split at h
  · omega
  rename_i h1 h2 h3 h4
  exact ⟨by omega, by omega, by omega, h.2.1 rfl⟩

/-- The bytes collected for the flow `f`, held in `buf`. -/
def bytesOf (f : Flow) (buf : Array U8 8192#usize) : List U8 := buf.val.take f.len.val

/-- The flow `f` with buffer `buf` is consistent: its length fits, and if
    in use, its state is the decision on its bytes. -/
def FlowOk (list : blocklist.Blocklist) (f : Flow) (buf : Array U8 8192#usize) : Prop :=
  f.len.val ≤ 8192 ∧ (f.state.val = 0 ∨ Decided list (bytesOf f buf) f.state.val)

/-- `f` tracks the connection `k`. -/
def Tracks (f : Flow) (k : Key) : Prop := f.state.val ≠ 0 ∧ f.key = k

/-- The invariant of the table: every flow is consistent. -/
def Streams.Inv (list : blocklist.Blocklist) (s : Streams) : Prop :=
  ∀ i < 256, FlowOk list s.flows.val[i]! s.data.val[i]!

theorem set_self! {α : Type} [Inhabited α] (l : List α) (i : Nat) (v : α) (h : i < l.length) :
    (l.set i v)[i]! = v := by simp [h]

theorem set_other! {α : Type} [Inhabited α] (l : List α) (i j : Nat) (v : α) (h : j ≠ i) :
    (l.set i v)[j]! = l[j]! := by simp [Ne.symm h]

/-- Replacing flow `i` keeps the invariant if the new flow is consistent
    with its buffer. -/
theorem Streams.Inv.set_flow {list : blocklist.Blocklist} {s : Streams} (h : s.Inv list)
    (i : Usize) (hi : i.val < 256) (f : Flow) (hf : FlowOk list f s.data.val[i.val]!) :
    Streams.Inv list { s with flows := s.flows.set i f } := by
  intro j hj
  simp only [Array.set_val_eq]
  by_cases e : j = i.val
  · subst e; rw [set_self! _ _ _ (by simp; omega)]; exact hf
  · rw [set_other! _ _ _ _ e]; exact h j hj

/-- Replacing flow `i` and its buffer keeps the invariant if they are
    consistent. -/
theorem Streams.Inv.set_both {list : blocklist.Blocklist} {s : Streams} (h : s.Inv list)
    (i : Usize) (hi : i.val < 256) (f : Flow) (b : Array U8 8192#usize) (hf : FlowOk list f b) :
    Streams.Inv list { flows := s.flows.set i f, data := s.data.set i b } := by
  intro j hj
  simp only [Array.set_val_eq]
  by_cases e : j = i.val
  · subst e
    rw [set_self! _ _ _ (by simp; omega), set_self! _ _ _ (by simp; omega)]; exact hf
  · rw [set_other! _ _ _ _ e, set_other! _ _ _ _ e]; exact h j hj

theorem FlowOk.fresh (list : blocklist.Blocklist) (k : Key) (first : U32) (now : U64)
    (b : Array U8 8192#usize) : FlowOk list ⟨k, COLLECTING, first, 0#usize, now⟩ b := by
  refine ⟨by simp, Or.inr ?_⟩
  simp [Decided, bytesOf]

theorem FlowOk.touched {list : blocklist.Blocklist} {f : Flow} {b : Array U8 8192#usize}
    (h : FlowOk list f b) (st : U8) (hst : st.val = 0 ∨ st = f.state) (now : U64) :
    FlowOk list { f with state := st, last := now } b := by
  refine ⟨h.1, ?_⟩
  rcases hst with h0 | rfl
  · exact Or.inl h0
  · exact h.2

/-- The connection `k` is tracked in `s`, blocked. -/
def BlockedIn (s : Streams) (k : Key) : Prop :=
  ∃ i < 256, Tracks s.flows.val[i]! k ∧ (s.flows.val[i]!).state.val = 3

/-- A blocked connection's first record, collected, is a ClientHello for a
    blocked name. -/
theorem BlockedIn.hello {list : blocklist.Blocklist} {s : Streams} {k : Key} (h : s.Inv list)
    (hb : BlockedIn s k) :
    ∃ i < 256, Tracks s.flows.val[i]! k ∧
      HelloBlocked list ((bytesOf s.flows.val[i]! s.data.val[i]!).take
        (needOf (bytesOf s.flows.val[i]! s.data.val[i]!))) := by
  obtain ⟨i, hi, ht, h3⟩ := hb
  refine ⟨i, hi, ht, ?_⟩
  rcases (h i hi).2 with h0 | hd
  · omega
  · rw [h3] at hd; exact hd.blocked.2.2.2

/-! ## Small functions -/

/-- **Spec theorem for `same`**. -/
@[step]
theorem same.spec (a b : Key) : same a b ⦃ (r : Bool) => (r = true ↔ a = b) ⦄ := by
  unfold same
  cases a; cases b
  simp only [Key.mk.injEq]
  split
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rename_i h; simp only [bne_iff_ne, ne_eq] at h; tauto
  split
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rename_i h1 h; simp only [bne_iff_ne, ne_eq] at h; tauto
  split
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rename_i h1 h2 h; simp only [bne_iff_ne, ne_eq] at h; tauto
  split
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    rename_i h1 h2 h3 h; simp only [bne_iff_ne, ne_eq] at h; tauto
  · simp only [WP.spec_ok, decide_eq_true_eq]
    rename_i h1 h2 h3 h4
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h1 h2 h3 h4
    simp [h1, h2, h3, h4]

/-- **Spec theorem for `tracks`**. -/
@[step]
theorem tracks.spec (f : Flow) (k : Key) : tracks f k ⦃ (r : Bool) => (r = true ↔ Tracks f k) ⦄ := by
  unfold tracks Tracks
  split
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
    rename_i h; intro h'; exact absurd (by scalar_tac) h'
  · apply WP.spec_mono (same.spec f.key k)
    intro r hr
    rename_i h
    have : f.state.val ≠ 0 := fun h' => h (by scalar_tac)
    simp [hr, this]

/-- **Spec theorem for `ends`**. -/
@[step]
theorem ends.spec (flags : U8) :
    ends flags ⦃ (r : Bool) => (r = true ↔ (flags.val % 2 = 1 ∨ flags.val / 4 % 2 = 1)) ⦄ := by
  unfold ends
  step*

/-- **Spec theorem for `data_start`**. -/
@[step]
theorem data_start.spec (seq : U32) (syn : Bool) :
    data_start seq syn ⦃ (r : U32) => r.val = (seq.val + if syn then 1 else 0) % 4294967296 ⦄ := by
  unfold data_start
  split
  · step*; simp [*, UScalar.size_UScalarTyU32, U32.size, U32.numBits]
  · simp only [WP.spec_ok]; simp

/-- **Spec theorem for `fresh`**. -/
@[step]
theorem fresh.spec (k : Key) (first : U32) (now : U64) :
    fresh k first now ⦃ (r : Flow) => r = ⟨k, COLLECTING, first, 0#usize, now⟩ ⦄ := by
  unfold fresh; simp

/-- **Spec theorem for `touched`**. -/
@[step]
theorem touched.spec (f : Flow) (state : U8) (now : U64) :
    touched f state now ⦃ (r : Flow) => r = { f with state, last := now } ⦄ := by
  unfold touched; simp

/-! ## Finding slots -/

theorem getElem!_eq {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! = l[i] := getElem!_pos l i h

/-- **Spec theorem for `find`'s loop**. -/
@[step]
theorem find_loop.spec (flows : Array Flow 256#usize) (k : Key) (found i : Usize)
    (hi : i.val ≤ 256)
    (hf : (found.val = 256 ∧ ∀ j < i.val, ¬ Tracks flows.val[j]! k) ∨
      (found.val < i.val ∧ Tracks flows.val[found.val]! k)) :
    find_loop flows k found i ⦃ (r : Usize) =>
      (r.val = 256 ∧ ∀ j < 256, ¬ Tracks flows.val[j]! k) ∨
        (r.val < 256 ∧ Tracks flows.val[r.val]! k) ⦄ := by
  unfold find_loop
  split
  · step as ⟨f, hfv⟩
    have hl : i.val < flows.val.length := by simp; scalar_tac
    have hfi : flows.val[i.val]! = f := by rw [getElem!_eq _ _ hl, hfv]
    have key : (if found = MAX_FLOWS then (do
          let b ← tracks f k
          if b then ok i else ok found) else ok found : Result Usize) ⦃ (found1 : Usize) =>
        (found1.val = 256 ∧ ∀ j < i.val + 1, ¬ Tracks flows.val[j]! k) ∨
          (found1.val < i.val + 1 ∧ Tracks flows.val[found1.val]! k) ⦄ := by
      split
      · rename_i h256
        have h256' : found.val = 256 := by scalar_tac
        step with tracks.spec f k as ⟨b, hb⟩
        split
        · simp only [WP.spec_ok]
          right; exact ⟨by omega, by rw [hfi]; exact hb.1 ‹_›⟩
        · simp only [WP.spec_ok]
          left
          refine ⟨h256', fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · rcases hf with ⟨-, h⟩ | ⟨h, -⟩
            · exact h j hj
            · omega
          · rw [hfi]; exact fun h => ‹¬b = true› (hb.2 h)
      · simp only [WP.spec_ok]
        rename_i hne
        rcases hf with ⟨h, -⟩ | ⟨h1, h2⟩
        · exact absurd (by scalar_tac) hne
        · right; exact ⟨by omega, h2⟩
    step with key as ⟨found1, h1⟩
    step as ⟨i1, hi1⟩
    apply find_loop.spec flows k found1 i1 (by scalar_tac)
    rw [hi1]; exact h1
  · simp only [WP.spec_ok]
    have : i.val = 256 := by scalar_tac
    rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, fun j hj => h2 j (by omega)⟩
    · right; exact ⟨by omega, h2⟩
termination_by 256 - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `find`**: the slot of the connection `k`, if tracked. -/
@[step]
theorem find.spec (flows : Array Flow 256#usize) (k : Key) :
    find flows k ⦃ (r : Usize) =>
      (r.val = 256 ∧ ∀ j < 256, ¬ Tracks flows.val[j]! k) ∨
        (r.val < 256 ∧ Tracks flows.val[r.val]! k) ⦄ := by
  unfold find
  exact find_loop.spec flows k _ _ (by simp) (Or.inl ⟨by simp, fun j hj => by simp at hj⟩)

/-- **Spec theorem for `first_free`'s loop**. -/
@[step]
theorem first_free_loop.spec (flows : Array Flow 256#usize) (free i : Usize) (hi : i.val ≤ 256)
    (hf : free.val ≤ 256) :
    first_free_loop flows free i ⦃ (r : Usize) => r.val ≤ 256 ⦄ := by
  unfold first_free_loop
  split
  · step as ⟨f, hfv⟩
    obtain ⟨free1, hfree1, h1⟩ : ∃ free1 : Usize, (if free = MAX_FLOWS then
        (if f.state = FREE then ok i else ok free) else ok free : Result Usize) = ok free1 ∧
        free1.val ≤ 256 := by
      split
      · split
        · exact ⟨i, rfl, by scalar_tac⟩
        · exact ⟨free, rfl, hf⟩
      · exact ⟨free, rfl, hf⟩
    rw [hfree1]
    simp only [bind_ok]
    step as ⟨i1, hi1⟩
    exact first_free_loop.spec flows free1 i1 (by scalar_tac) h1
  · simp only [WP.spec_ok]; exact hf
termination_by 256 - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `first_free`**. -/
@[step]
theorem first_free.spec (flows : Array Flow 256#usize) :
    first_free flows ⦃ (r : Usize) => r.val ≤ 256 ⦄ := by
  unfold first_free
  exact first_free_loop.spec flows _ _ (by simp) (by simp)

/-- **Spec theorem for `least_recent`'s loop**. -/
@[step]
theorem least_recent_loop.spec (flows : Array Flow 256#usize) (oldest i : Usize)
    (ho : oldest.val < 256) (hi : i.val ≤ 256) :
    least_recent_loop flows oldest i ⦃ (r : Usize) => r.val < 256 ⦄ := by
  unfold least_recent_loop
  split
  · step as ⟨f, hfv⟩
    step as ⟨f1, hf1⟩
    obtain ⟨o1, ho1, h1⟩ : ∃ o1 : Usize, (if f.last < f1.last then ok i else ok oldest :
        Result Usize) = ok o1 ∧ o1.val < 256 := by
      split
      · exact ⟨i, rfl, by scalar_tac⟩
      · exact ⟨oldest, rfl, ho⟩
    rw [ho1]
    simp only [bind_ok]
    step as ⟨i1, hi1⟩
    exact least_recent_loop.spec flows o1 i1 h1 (by scalar_tac)
  · simp only [WP.spec_ok]; exact ho
termination_by 256 - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `least_recent`**. -/
@[step]
theorem least_recent.spec (flows : Array Flow 256#usize) :
    least_recent flows ⦃ (r : Usize) => r.val < 256 ⦄ := by
  unfold least_recent
  exact least_recent_loop.spec flows _ _ (by simp) (by simp)

/-- **Spec theorem for `slot`**: a slot in range. -/
@[step]
theorem slot.spec (flows : Array Flow 256#usize) : slot flows ⦃ (r : Usize) => r.val < 256 ⦄ := by
  unfold slot
  step*

/-! ## Collecting bytes -/

/-- **Spec theorem for `append`'s loop**: copies `data[j..]` after the
    `n` bytes of `buf`, as much as fits in 8192. -/
@[step]
theorem append_loop.spec (buf : Array U8 8192#usize) (data : Slice U8) (n j : Usize)
    (hn : n.val ≤ 8192) (hj : j.val ≤ data.length) :
    append_loop buf data n j ⦃ (r : Usize × Array U8 8192#usize) =>
      r.1.val = min (n.val + (data.length - j.val)) 8192 ∧
        r.2.val.take r.1.val = (buf.val.take n.val ++ data.val.drop j.val).take 8192 ⦄ := by
  unfold append_loop
  dsimp only
  have hdl : data.length = data.val.length := rfl
  split
  · split
    · step as ⟨c, hc⟩
      step as ⟨a, ha⟩
      step as ⟨n1, hn1⟩
      step as ⟨j1, hj1⟩
      apply WP.spec_mono (append_loop.spec a data n1 j1 (by scalar_tac) (by scalar_tac))
      rintro ⟨m, b⟩ ⟨hm, hb⟩
      have hjl0 : j.val < data.length := by scalar_tac
      refine ⟨by rw [hm, hn1, hj1]; omega, ?_⟩
      rw [hb, ha, Array.set_val_eq, hn1, hj1]
      have hlt : n.val < buf.val.length := by simp; scalar_tac
      have hjl : j.val < data.val.length := by scalar_tac
      rw [dns.take_set_succ _ _ _ hlt, List.drop_eq_getElem_cons hjl, hc]
      simp
    · simp only [WP.spec_ok]
      have h8 : n.val = 8192 := by scalar_tac
      refine ⟨by omega, ?_⟩
      rw [h8, List.take_append_of_le_length (by simp)]
      simp
  · simp only [WP.spec_ok]
    have hjd : j.val = data.length := by scalar_tac
    refine ⟨by omega, ?_⟩
    rw [hjd, hdl, List.drop_length, List.append_nil, List.take_take]
    congr 1; omega
termination_by data.length - j.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `append`**. -/
@[step]
theorem append.spec (buf : Array U8 8192#usize) (len : Usize) (data : Slice U8) (from' : Usize)
    (hn : len.val ≤ 8192) (hj : from'.val ≤ data.length) :
    append buf len data from' ⦃ (r : Usize × Array U8 8192#usize) =>
      r.1.val = min (len.val + (data.length - from'.val)) 8192 ∧
        r.2.val.take r.1.val = (buf.val.take len.val ++ data.val.drop from'.val).take 8192 ⦄ := by
  unfold append
  exact append_loop.spec buf data len from' hn hj

theorem take_getElem! (l : List U8) (n i : Nat) (hi : i < n) (hl : n ≤ l.length) :
    (l.take n)[i]! = l[i]! := by
  rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
  simp

/-- **Spec theorem for `decide`**: the decision on the first `len` bytes of
    `buf`. -/
@[step]
theorem decide.spec (buf : Array U8 8192#usize) (len : Usize) (list : blocklist.Blocklist)
    (hb : list.Inv) (hl : len.val ≤ 8192) :
    decide buf len list ⦃ (st : U8) => Decided list (buf.val.take len.val) st.val ⦄ := by
  unfold decide
  have hbl : buf.val.length = 8192 := by simp
  have hlen : (buf.val.take len.val).length = len.val := by simp; omega
  split
  · simp only [WP.spec_ok]
    unfold Decided
    rw [hlen, if_pos (by scalar_tac)]
    simp
  have h5 : 5 ≤ len.val := by scalar_tac
  have g : ∀ i < 5, (buf.val.take len.val)[i]! = buf.val[i]! := fun i hi =>
    take_getElem! _ _ _ (by omega) (by omega)
  step as ⟨b0, hb0⟩
  have e0 : (buf.val.take len.val)[0]!.val = b0.val := by
    rw [g 0 (by omega), getElem!_pos _ _ (by omega), hb0]
  split
  · simp only [WP.spec_ok]
    unfold Decided
    rename_i hne
    have : b0.val ≠ 22 := by simp only [bne_iff_ne, ne_eq] at hne; exact fun h => hne (by scalar_tac)
    rw [hlen, if_neg (by omega), e0, if_pos this]
    simp
  rename_i h22
  have h22' : b0.val = 22 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h22; rw [h22]; rfl
  step as ⟨b3, hb3⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  step as ⟨b4, hb4⟩
  step as ⟨i6, hi6⟩
  step as ⟨need, hneed⟩
  have eneed : needOf (buf.val.take len.val) = need.val := by
    unfold needOf
    rw [g 3 (by omega), g 4 (by omega), getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega),
      ← hb3, ← hb4, hneed, hi4, hi3, hi6, hi2]
    simp
  have hD : ∀ st : Nat, Decided list (buf.val.take len.val) st ↔
      (if 8192 < need.val then st = 2 else if len.val < need.val then st = 1
        else (st = 2 ∨ st = 3) ∧ (st = 3 ↔ HelloBlocked list ((buf.val.take len.val).take need.val))) := by
    intro st
    unfold Decided
    rw [hlen, if_neg (by omega), e0, h22', if_neg (by simp), eneed]
  split
  · simp only [WP.spec_ok]
    rw [hD, if_pos (by scalar_tac)]
    simp
  split
  · simp only [WP.spec_ok]
    rw [hD, if_neg (by scalar_tac), if_pos (by scalar_tac)]
    simp
  step as ⟨s, hs, hsl⟩
  step with filter.classify_stream.spec s list hb as ⟨b, hb'⟩
  have hsv : s.val = (buf.val.take len.val).take need.val := by
    rw [hs, List.take_take, show min need.val len.val = need.val by scalar_tac]
    simp [List.slice]
  rw [hsv] at hb'
  split
  · simp only [WP.spec_ok]
    rw [hD, if_neg (by scalar_tac), if_neg (by scalar_tac)]
    rename_i hbt
    simp only [BLOCKED_val]
    exact ⟨Or.inr trivial, by simp only [true_iff]; exact hb'.1 hbt⟩
  · simp only [WP.spec_ok]
    rw [hD, if_neg (by scalar_tac), if_neg (by scalar_tac)]
    rename_i hbf
    simp only [PASSED_val]
    exact ⟨Or.inl trivial, by simp only [show (2 : Nat) ≠ 3 by decide, false_iff]; exact fun h => hbf (hb'.2 h)⟩

/-! ## Updating flows -/

/-- **Spec theorem for `next_flow`**. -/
@[step]
theorem next_flow.spec (f : Flow) (first : U32) (syn end' : Bool) (now : U64) :
    next_flow f first syn end' now ⦃ (r : Flow) =>
      r = if end' then { f with state := FREE, last := now }
        else if f.state = BLOCKED then { f with state := BLOCKED, last := now }
        else if syn then ⟨f.key, COLLECTING, first, 0#usize, now⟩
        else { f with state := f.state, last := now } ⦄ := by
  unfold next_flow
  split
  · rename_i h; step*
  split
  · rename_i h1 h2; step*
  split
  · rename_i h1 h2 h3; step*
  · rename_i h1 h2 h3; step*

/-- The flow `next_flow` gives stays consistent with the buffer. -/
theorem next_flow_ok {list : blocklist.Blocklist} {f : Flow} {b : Array U8 8192#usize}
    (h : FlowOk list f b) (first : U32) (syn end' : Bool) (now : U64) :
    FlowOk list (if end' then { f with state := FREE, last := now }
        else if f.state = BLOCKED then { f with state := BLOCKED, last := now }
        else if syn then ⟨f.key, COLLECTING, first, 0#usize, now⟩
        else { f with state := f.state, last := now }) b := by
  split
  · exact h.touched _ (Or.inl (by simp)) now
  split
  · rename_i _ h3; exact h.touched _ (Or.inr h3.symm) now
  split
  · exact FlowOk.fresh list f.key first now b
  · exact h.touched _ (Or.inr rfl) now

/-- **Spec theorem for `place`**: the slot of a tracked connection, or a
    fresh one for a new connection. -/
@[step]
theorem place.spec (flows : Array Flow 256#usize) (found : Usize) (k : Key) (first : U32)
    (now : U64) (hf : found.val ≤ 256) :
    place flows found k first now ⦃ (r : Usize × Flow) =>
      r.1.val < 256 ∧
        (found.val = 256 → r.2 = ⟨k, COLLECTING, first, 0#usize, now⟩) ∧
        (found.val < 256 → r.1 = found ∧ r.2 = flows.val[found.val]!) ⦄ := by
  unfold place
  split
  · step*
  · step as ⟨f, hfv⟩
    have hlt : found.val < 256 := by scalar_tac
    refine ⟨hlt, fun h => absurd h (by omega), fun _ => ?_⟩
    rw [hfv, getElem!_pos _ _ (by simp; omega)]

/-- How far into a segment starting at `first` the byte `next` is, modulo
    2^32. -/
def offsetN (next first : U32) : Nat := (next.val + 4294967296 - first.val) % 4294967296

/-- **Spec theorem for `Streams::collect`**: keeps the invariant; when it
    takes the segment's new bytes, they are appended in order to those
    collected; a reset means the flow is now blocked. -/
@[step]
theorem Streams.collect.spec (s : Streams) (slot : Usize) (first : U32) (data : Slice U8)
    (list : blocklist.Blocklist) (hb : list.Inv) (hs : s.Inv list) (hi : slot.val < 256) :
    Streams.collect s slot first data list ⦃ (r : Step × Streams) =>
      r.2.Inv list ∧ (r.2.flows.val[slot.val]!).key = (s.flows.val[slot.val]!).key ∧
        (r.1 = .Reset → (r.2.flows.val[slot.val]!).state.val = 3) ∧
        (r.2 = s ∨ bytesOf r.2.flows.val[slot.val]! r.2.data.val[slot.val]! =
          (bytesOf s.flows.val[slot.val]! s.data.val[slot.val]! ++
            data.val.drop (offsetN (s.flows.val[slot.val]!).next_seq first)).take 8192) ⦄ := by
  unfold Streams.collect
  step*
  all_goals have hfo := hs slot.val hi
  all_goals have hfl : flow = s.flows.val[slot.val]! := by rw [flow_post, getElem!_pos _ _ (by simp; omega)]
  all_goals have hsz : UScalar.size UScalarTy.U32 = 4294967296 := (by
    simp [UScalar.size_UScalarTyU32, U32.size, U32.numBits])
  all_goals have hoff : offset.val = offsetN flow.next_seq first := (by
    rw [offset_post, core.num.U32.wrapping_sub_val_eq, hsz]
    unfold offsetN
    have := first.hBounds; simp only [UScalarTy.U32_numBits_eq] at this
    omega)
  all_goals first
    | (rw [hfl]; exact hfo.1)
    | skip
  all_goals (
    have ha : a = s.data.val[slot.val]! := by rw [a_post, getElem!_pos _ _ (by simp; omega)]
    have hi2 : i2.val = offsetN flow.next_seq first := by
      rw [i2_post, U32.cast_Usize_val_eq, hoff]
    have ha3 : a3 = a1 := by
      rw [a3_post, index_mut_back_post]; simp
    rw [ha3] at state_post
    try (rename_i hst; rw [hst] at state_post)
    rw [index_mut_back1_post, index_mut_back_post]
    have hok : ∀ st : U8, Decided list (a1.val.take len.val) st.val →
        FlowOk list ⟨flow.key, st, i5, len, flow.last⟩ a1 := fun st h =>
      ⟨by rw [len_post]; omega, Or.inr h⟩
    have hset : ∀ st : U8, (s.flows.set slot ⟨flow.key, st, i5, len, flow.last⟩).val[slot.val]! =
        ⟨flow.key, st, i5, len, flow.last⟩ := fun st => by
      rw [Array.set_val_eq, set_self! _ _ _ (by simp; omega)]
    have hdset : (s.data.set slot a1).val[slot.val]! = a1 := by
      rw [Array.set_val_eq, set_self! _ _ _ (by simp; omega)]
    refine ⟨hs.set_both slot hi _ a1 (hok _ state_post), by rw [hset, hfl], ?_, Or.inr ?_⟩
    · intro _; rw [hset]; simp_all
    · rw [hset, hdset]
      unfold bytesOf
      simp only
      rw [len_post1, ha, ← hfl, hi2])


/-- **Spec theorem for `Streams::track`**: keeps the invariant and the key of
    the slot; a reset means the flow was or is now blocked. -/
@[step]
theorem Streams.track.spec (s : Streams) (slot : Usize) (first : U32) (syn rst end' : Bool)
    (data : Slice U8) (now : U64) (list : blocklist.Blocklist) (hb : list.Inv)
    (hs : s.Inv list) (hi : slot.val < 256) :
    Streams.track s slot first syn rst end' data now list ⦃ (r : Step × Streams) =>
      r.2.Inv list ∧ (r.2.flows.val[slot.val]!).key = (s.flows.val[slot.val]!).key ∧
        (r.1 = .Reset →
          (s.flows.val[slot.val]!).state.val = 3 ∨ (r.2.flows.val[slot.val]!).state.val = 3) ⦄ := by
  unfold Streams.track
  step as ⟨flow, hflow⟩
  have hfl : flow = s.flows.val[slot.val]! := by rw [hflow, getElem!_pos _ _ (by simp; omega)]
  step as ⟨next, hnext⟩
  have hok : FlowOk list next s.data.val[slot.val]! := by
    rw [hnext]; exact next_flow_ok (by rw [hfl]; exact hs _ hi) _ _ _ _
  have hs1 := hs.set_flow slot hi next hok
  have hkey : next.key = flow.key := by rw [hnext]; split <;> (try split) <;> (try split) <;> rfl
  have hset : (s.flows.set slot next).val[slot.val]! = next := by
    rw [Array.set_val_eq, set_self! _ _ _ (by simp; omega)]
  step as ⟨x, back, hx, hback⟩
  rw [hback]
  split
  · rename_i h3
    have h3' : (s.flows.val[slot.val]!).state.val = 3 := by rw [← hfl, h3]; simp
    split
    · simp only [WP.spec_ok]
      exact ⟨hs1, by rw [hset, hkey, hfl], fun h => by cases h⟩
    · simp only [WP.spec_ok]
      exact ⟨hs1, by rw [hset, hkey, hfl], fun _ => Or.inl h3'⟩
  split
  · simp only [WP.spec_ok]
    exact ⟨hs1, by rw [hset, hkey, hfl], fun h => by cases h⟩
  apply WP.spec_mono (Streams.collect.spec _ slot first data list hb hs1 hi)
  rintro ⟨st, s'⟩ ⟨hinv, hk, hr, -⟩
  refine ⟨hinv, by rw [hk]; simp only; rw [hset, hkey, hfl], fun h => Or.inr (hr h)⟩

/-- What `segment` needs of the flow `f` it places in slot `i`: consistent,
    of the connection `k`, and blocked only if `k` was. -/
theorem segment_post {list : blocklist.Blocklist} {s : Streams} {k : Key} (hs : s.Inv list)
    (i : Usize) (hi : i.val < 256) (f : Flow) (hok : FlowOk list f s.data.val[i.val]!)
    (hk : f.key = k) (h3 : f.state.val = 3 → BlockedIn s k) :
    Streams.Inv list { flows := s.flows.set i f, data := s.data } ∧
      ∀ r : Step × Streams, r.2.Inv list →
        (r.2.flows.val[i.val]!).key = ((s.flows.set i f).val[i.val]!).key →
        (r.1 = .Reset → ((s.flows.set i f).val[i.val]!).state.val = 3 ∨
          (r.2.flows.val[i.val]!).state.val = 3) →
        r.2.Inv list ∧ (r.1 = .Reset → BlockedIn s k ∨ BlockedIn r.2 k) := by
  have hset : (s.flows.set i f).val[i.val]! = f := by
    rw [Array.set_val_eq, set_self! _ _ _ (by simp; omega)]
  refine ⟨hs.set_flow i hi f hok, fun r hinv hkey hres => ⟨hinv, fun hR => ?_⟩⟩
  rw [hset] at hkey hres
  rcases hres hR with h | h
  · exact Or.inl (h3 h)
  · exact Or.inr ⟨i.val, hi, ⟨by omega, by rw [hkey, hk]⟩, h⟩

/-- **Spec theorem for `Streams::segment`**: keeps the invariant; a reset
    means the connection `k` was or is now tracked as blocked, so (by
    `BlockedIn.hello`) its first record, collected in order, is a
    ClientHello for a blocked name. -/
@[step]
theorem Streams.segment.spec (s : Streams) (k : Key) (seq : U32) (flags : U8) (data : Slice U8)
    (now : U64) (list : blocklist.Blocklist) (hb : list.Inv) (hs : s.Inv list) :
    Streams.segment s k seq flags data now list ⦃ (r : Step × Streams) =>
      r.2.Inv list ∧ (r.1 = .Reset → BlockedIn s k ∨ BlockedIn r.2 k) ⦄ := by
  unfold Streams.segment
  step*
  all_goals (
    subst a_post
    have hfacts : FlowOk list f s.data.val[i4.val]! ∧ f.key = k ∧
        (f.state.val = 3 → BlockedIn s k) := by
      first
        | (have e := i4_post1 (by simp)
           rw [e]
           exact ⟨FlowOk.fresh _ _ _ _ _, rfl, by simp⟩)
        | (rcases found_post with ⟨h256, -⟩ | ⟨hlt, htr⟩
           · exact absurd h256 (by scalar_tac)
           · obtain ⟨e1, e2⟩ := i4_post2 hlt
             subst e1
             rw [e2]
             exact ⟨hs _ hlt, htr.2, fun h => ⟨_, hlt, htr, h⟩⟩)
    obtain ⟨hok, hk, h3⟩ := hfacts
    have P := segment_post hs i4 i4_post f hok hk h3
    first
      | exact P.1
      | exact P.2 r r_post r_post1 r_post2)

end diomede.stream

namespace diomede.filter

open stream

/-- The verdict on a TCP segment to port 443 tracked by the stream table: a
    reset (`reset n` describes it) only if the connection is, or was before
    the segment, tracked as blocked (`blocked`). -/
def StreamVerdict (blocked : Prop) (reset : Nat → Prop) : Verdict → Prop
  | .Reset n => blocked ∧ reset n.val
  | .Reply _ => False
  | _ => True

/-- The connection key of a segment over IPv4. -/
def Key4 (t : net.tcp.Ipv4Tcp) (k : Key) : Prop :=
  k.v6 = false ∧ k.src.val = (t.ip.header.src : U32).val ∧ k.dst.val = (t.ip.header.dst : U32).val ∧
    k.src_port = t.header.src_port ∧ k.dst_port = t.header.dst_port

/-- The connection key of a segment over IPv6. -/
def Key6 (t : net.tcp.Ipv6Tcp) (k : Key) : Prop :=
  k.v6 = true ∧ k.src = t.ip.header.src ∧ k.dst = t.ip.header.dst ∧
    k.src_port = t.header.src_port ∧ k.dst_port = t.header.dst_port

/-- **Spec theorem for `stream_ipv4`**. -/
@[step]
theorem stream_ipv4.spec (t : net.tcp.Ipv4Tcp) (s : Streams) (now : U64)
    (list : blocklist.Blocklist) (out : Slice U8) (hb : list.Inv) (hs : s.Inv list) :
    stream_ipv4 t s now list out ⦃ (r : Verdict × Streams × Slice U8) =>
      r.2.1.Inv list ∧ r.2.2.length = out.length ∧
        StreamVerdict (∃ k, Key4 t k ∧ (BlockedIn s k ∨ BlockedIn r.2.1 k))
          (Reset4 t (t.payload : Slice U8).length r.2.2.val) r.1 ⦄ := by
  unfold stream_ipv4
  simp only [Untrusted.validate_eq]
  step*
  all_goals have hd : d = t.payload := (by
    have h1 := ‹r = core.result.Result.Ok d›
    rw [r_post] at h1
    injection h1 with h1
    exact h1.symm)
  all_goals subst hd
  · exact ⟨s_post, by simp [StreamVerdict]⟩
  · exact ⟨s_post, by simp [StreamVerdict]⟩
  · exact ⟨s_post, o_post, by simp [StreamVerdict]⟩
  · have hn : o = some n := ‹_›
    rw [hn] at o_post1
    obtain ⟨-, r, hr, hsrc, hdst, hhdr, hpay⟩ := o_post1
    refine ⟨s_post, o_post, ⟨_, ⟨rfl, by rw [i1_post]; simp, by rw [i3_post]; simp, rfl, rfl⟩, s_post1 ‹_›⟩, r, hr, hsrc, hdst, ack, ?_, hpay, ?_⟩
    · rw [seq_post1, Slice.len_val]
    · rw [hhdr, seq_post, RST_ACK_eq]; rfl

/-- **Spec theorem for `stream_ipv6`**. -/
@[step]
theorem stream_ipv6.spec (t : net.tcp.Ipv6Tcp) (s : Streams) (now : U64)
    (list : blocklist.Blocklist) (out : Slice U8) (hb : list.Inv) (hs : s.Inv list) :
    stream_ipv6 t s now list out ⦃ (r : Verdict × Streams × Slice U8) =>
      r.2.1.Inv list ∧ r.2.2.length = out.length ∧
        StreamVerdict (∃ k, Key6 t k ∧ (BlockedIn s k ∨ BlockedIn r.2.1 k))
          (Reset6 t (t.payload : Slice U8).length r.2.2.val) r.1 ⦄ := by
  unfold stream_ipv6
  simp only [Untrusted.validate_eq]
  step*
  all_goals have hd : d = t.payload := (by
    have h1 := ‹r = core.result.Result.Ok d›
    rw [r_post] at h1
    injection h1 with h1
    exact h1.symm)
  all_goals subst hd
  · exact ⟨s_post, by simp [StreamVerdict]⟩
  · exact ⟨s_post, by simp [StreamVerdict]⟩
  · exact ⟨s_post, o_post, by simp [StreamVerdict]⟩
  · have hn : o = some n := ‹_›
    rw [hn] at o_post1
    obtain ⟨-, r, hr, hsrc, hdst, hhdr, hpay⟩ := o_post1
    refine ⟨s_post, o_post, ⟨_, ⟨rfl, rfl, rfl, rfl, rfl⟩, s_post1 ‹_›⟩, r, hr, hsrc, hdst, ack, ?_, hpay, ?_⟩
    · rw [seq_post1, Slice.len_val]
    · rw [hhdr, seq_post, RST_ACK_eq]; rfl

/-- What `filter` does with the packet `p`, the table going from `s` to
    `s'`: a TCP segment to port 443 goes through the stream table (which
    resets it only for a connection tracked as blocked); anything else gets
    `classify`'s verdict, the table unchanged. -/
def Filter (list : blocklist.Blocklist) (policy : Policy) (s s' : Streams) (p out : List U8)
    (v : Verdict) : Prop :=
  (∃ t, net.tcp.Ipv4Tcp.Spec p t ∧ (t.header.dst_port : U16).val = 443 ∧
    StreamVerdict (∃ k, Key4 t k ∧ (BlockedIn s k ∨ BlockedIn s' k))
      (Reset4 t (t.payload : Slice U8).length out) v) ∨
  (∃ t, net.tcp.Ipv6Tcp.Spec p t ∧ (t.header.dst_port : U16).val = 443 ∧
    StreamVerdict (∃ k, Key6 t k ∧ (BlockedIn s k ∨ BlockedIn s' k))
      (Reset6 t (t.payload : Slice U8).length out) v) ∨
  (s' = s ∧ Classify list policy p out v)

/-- **Spec theorem for `filter`**: keeps the table's invariant. -/
@[step]
theorem filter.spec (packet : Slice U8) (s : Streams) (now : U64) (list : blocklist.Blocklist)
    (policy : Policy) (out : Slice U8) (hb : list.Inv) (hs : s.Inv list) :
    filter packet s now list policy out ⦃ (r : Verdict × Streams × Slice U8) =>
      r.2.1.Inv list ∧ r.2.2.length = out.length ∧
        Filter list policy s r.2.1 packet.val r.2.2.val r.1 ⦄ := by
  unfold filter
  step as ⟨u, hu⟩
  simp only [Untrusted.validate_eq]
  step as ⟨r, hr⟩
  rw [hu] at hr
  cases r with
  | Ok it =>
    simp only
    split
    · rename_i h443
      apply WP.spec_mono (stream_ipv4.spec it s now list out hb hs)
      rintro ⟨v, s', o⟩ ⟨h1, h2, h3⟩
      exact ⟨h1, h2, Or.inl ⟨it, hr, by rw [h443]; simp, h3⟩⟩
    step as ⟨r1, hr1⟩
    rw [hu] at hr1
    cases r1 with
    | Ok it1 =>
      simp only
      split
      · rename_i h443
        apply WP.spec_mono (stream_ipv6.spec it1 s now list out hb hs)
        rintro ⟨v, s', o⟩ ⟨h1, h2, h3⟩
        exact ⟨h1, h2, Or.inr (Or.inl ⟨it1, hr1, by rw [h443]; simp, h3⟩)⟩
      step*
      exact ⟨hs, v_post, Or.inr (Or.inr ⟨rfl, v_post1⟩)⟩
    | Err _ =>
      simp only
      step*
      exact ⟨hs, v_post, Or.inr (Or.inr ⟨rfl, v_post1⟩)⟩
  | Err _ =>
    simp only
    step as ⟨r1, hr1⟩
    rw [hu] at hr1
    cases r1 with
    | Ok it1 =>
      simp only
      split
      · rename_i h443
        apply WP.spec_mono (stream_ipv6.spec it1 s now list out hb hs)
        rintro ⟨v, s', o⟩ ⟨h1, h2, h3⟩
        exact ⟨h1, h2, Or.inr (Or.inl ⟨it1, hr1, by rw [h443]; simp, h3⟩)⟩
      step*
      exact ⟨hs, v_post, Or.inr (Or.inr ⟨rfl, v_post1⟩)⟩
    | Err _ =>
      simp only
      step*
      exact ⟨hs, v_post, Or.inr (Or.inr ⟨rfl, v_post1⟩)⟩

end diomede.filter
