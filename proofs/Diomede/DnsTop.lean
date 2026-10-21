/- Specs of `diomede::dns`: DNS queries (RFC 1035 §4.1) and the NXDOMAIN
   answers to them. -/
import Diomede.NameTop
import Diomede.Specs.DnsHeader
import Diomede.Specs.Answer

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace diomede.dns

@[simp, scalar_tac_simps] theorem HEADER_LEN_val : HEADER_LEN.val = 12 := by simp [HEADER_LEN]
@[simp, scalar_tac_simps] theorem MAX_LABEL_LEN_val : MAX_LABEL_LEN.val = 63 := by
  simp [MAX_LABEL_LEN]
@[simp, scalar_tac_simps] theorem NXDOMAIN_val : NXDOMAIN.val = 3 := by simp [NXDOMAIN]

/-- Writing `v` at `i` and taking `i + 1` elements. -/
theorem take_set_succ {α : Type} (l : List α) (i : Nat) (v : α) (h : i < l.length) :
    (l.set i v).take (i + 1) = l.take i ++ [v] := by
  rw [List.take_add_one, List.take_set_of_le (Nat.le_refl _), List.getElem?_set_self h]
  rfl

/-- The `m + 1` elements from `i`, when `i` is in range: `l[i]` and the `m`
    after it. -/
theorem drop_take_succ {α : Type} (l : List α) (i m : Nat) (h : i < l.length) :
    (l.drop i).take (m + 1) = l[i] :: (l.drop (i + 1)).take m := by
  rw [List.drop_eq_getElem_cons h]; rfl

/-! ## Copying labels -/

/-- **Spec theorem for `copy_label`'s loop**: writes `msg[from + j..from + len]`
    at `text[at + j..]`. -/
@[step]
theorem copy_label_loop.spec (text : Array U8 253#usize) (at' : Usize) (msg : Slice U8)
    (from' len j : Usize) (hj : j.val ≤ len.val) (hat : at'.val + len.val ≤ 253)
    (hfrom : from'.val + len.val ≤ msg.length) :
    copy_label_loop text at' msg from' len j ⦃ (r : Array U8 253#usize) =>
      r.val.take (at'.val + len.val) =
        text.val.take (at'.val + j.val) ++ (msg.val.drop (from'.val + j.val)).take (len.val - j.val) ⦄ := by
  unfold copy_label_loop
  split
  · step as ⟨i, hi⟩
    step as ⟨c, hc⟩
    step as ⟨i2, hi2⟩
    step as ⟨a, ha⟩
    step as ⟨j1, hj1⟩
    apply WP.spec_mono (copy_label_loop.spec a at' msg from' len j1 (by scalar_tac) hat hfrom)
    intro r hr
    rw [hr, ha, Array.set_val_eq, hi2, hj1]
    have hlt : at'.val + j.val < text.val.length := by simp; scalar_tac
    have hfrom' : from'.val + len.val ≤ msg.val.length := hfrom
    have hjl : j.val < len.val := by scalar_tac
    have hlt' : from'.val + j.val < msg.val.length := by omega
    rw [show at'.val + (j.val + 1) = at'.val + j.val + 1 by omega, take_set_succ _ _ _ hlt,
      show len.val - j.val = (len.val - (j.val + 1)) + 1 by omega, drop_take_succ _ _ _ hlt',
      show from'.val + (j.val + 1) = from'.val + j.val + 1 by omega]
    simp [hc, hi]
  · simp only [WP.spec_ok]
    have : j.val = len.val := by scalar_tac
    rw [this]; simp
termination_by len.val - j.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `copy_label`**: `text[at..at + len]` becomes
    `msg[from..from + len]`; the bytes before `at` are kept. -/
@[step]
theorem copy_label.spec (text : Array U8 253#usize) (at' : Usize) (msg : Slice U8)
    (from' len : Usize) (hat : at'.val + len.val ≤ 253) (hfrom : from'.val + len.val ≤ msg.length) :
    copy_label text at' msg from' len ⦃ (r : Array U8 253#usize) =>
      r.val.take (at'.val + len.val) =
        text.val.take at'.val ++ (msg.val.drop from'.val).take len.val ⦄ := by
  unfold copy_label
  apply WP.spec_mono (copy_label_loop.spec text at' msg from' len 0#usize (by simp) hat hfrom)
  intro r hr; simpa using hr

/-! ## Names on the wire -/

/-- The labels of the name at the start of `d` (RFC 1035 §3.1, without
    compression) and the number of bytes it takes: per label a length byte
    from 1 to 63 and that many bytes, then a zero byte. `none` if `d` does not
    start with such a name. -/
def labelsN : List U8 → Option (List (List U8) × Nat)
  | [] => none
  | b :: rest =>
    if b.val = 0 then some ([], 1)
    else if b.val ≤ 63 ∧ b.val ≤ rest.length then
      (labelsN (rest.drop b.val)).map fun p => (rest.take b.val :: p.1, 1 + b.val + p.2)
    else none
termination_by d => d.length
decreasing_by simp

theorem labelsN_nil : labelsN [] = none := by rw [labelsN]

theorem labelsN_cons (b : U8) (rest : List U8) :
    labelsN (b :: rest) =
      if b.val = 0 then some ([], 1)
      else if b.val ≤ 63 ∧ b.val ≤ rest.length then
        (labelsN (rest.drop b.val)).map fun p => (rest.take b.val :: p.1, 1 + b.val + p.2)
      else none := by
  rw [labelsN]

/-- Labels joined by dots. -/
def dotted : List (List U8) → List U8
  | [] => []
  | l :: ls => l ++ ls.flatMap (fun m => 46#u8 :: m)

theorem dotted_snoc (acc : List (List U8)) (l : List U8) :
    dotted (acc ++ [l]) = dotted acc ++ (if acc = [] then [] else [46#u8]) ++ l := by
  cases acc <;> simp [dotted, List.flatMap_append]

theorem dotted_le (acc ls : List (List U8)) :
    (dotted acc).length ≤ (dotted (acc ++ ls)).length := by
  cases acc <;> simp [dotted, List.flatMap_append]

/-- The name at the start of `d` has the labels `ls` and takes `k` bytes, and
    as text after the labels `acc` it stays within 253 characters. -/
def Found (d : List U8) (acc ls : List (List U8)) (k : Nat) : Prop :=
  labelsN d = some (ls, k) ∧ (dotted (acc ++ ls)).length ≤ 253

theorem Found.unique {d : List U8} {acc acc' ls ls' : List (List U8)} {k k' : Nat}
    (h : Found d acc ls k) (h' : Found d acc' ls' k') : ls = ls' ∧ k = k' := by
  have := h.1.symm.trans h'.1
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

/-- A name takes at most the bytes there are. -/
theorem labelsN_le (d : List U8) (ls : List (List U8)) (k : Nat) (h : labelsN d = some (ls, k)) :
    k ≤ d.length := by
  match d with
  | [] => simp [labelsN_nil] at h
  | b :: rest =>
    rw [labelsN_cons] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      simp; omega
    split at h
    · cases hl : labelsN (rest.drop b.val) with
      | none => simp [hl] at h
      | some p =>
        obtain ⟨ls', k'⟩ := p
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        have := labelsN_le _ _ _ hl
        simp at this ⊢; omega
    · simp at h
termination_by d.length
decreasing_by simp

theorem bne_false {x y : U16} (h : ¬ (x != y) = true) : x.val = y.val := by
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h; rw [h]

theorem strip_length_le (t : List U8) : (name.strip t).length ≤ t.length := by
  unfold name.strip; split <;> simp

theorem found_nil (acc ls : List (List U8)) (k : Nat) : ¬ Found [] acc ls k := by
  simp [Found, labelsN_nil]

theorem found_zero (b : U8) (rest : List U8) (acc ls : List (List U8)) (k : Nat)
    (h0 : b.val = 0) : Found (b :: rest) acc ls k ↔ ls = [] ∧ k = 1 ∧ (dotted acc).length ≤ 253 := by
  simp only [Found, labelsN_cons, h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨rfl, rfl⟩, h⟩; exact ⟨rfl, rfl, by simpa using h⟩
  · rintro ⟨rfl, rfl, h⟩; exact ⟨⟨rfl, rfl⟩, by simpa using h⟩

theorem found_bad (b : U8) (rest : List U8) (acc ls : List (List U8)) (k : Nat)
    (h0 : b.val ≠ 0) (hb : ¬ (b.val ≤ 63 ∧ b.val ≤ rest.length)) : ¬ Found (b :: rest) acc ls k := by
  simp only [Found, labelsN_cons, h0, hb, ↓reduceIte]
  simp

theorem found_cons (b : U8) (rest : List U8) (acc ls : List (List U8)) (k : Nat)
    (h0 : b.val ≠ 0) (h63 : b.val ≤ 63) (hr : b.val ≤ rest.length) :
    Found (b :: rest) acc ls k ↔ ∃ ls' k', ls = rest.take b.val :: ls' ∧ k = 1 + b.val + k' ∧
      Found (rest.drop b.val) (acc ++ [rest.take b.val]) ls' k' := by
  have hb : b.val ≤ 63 ∧ b.val ≤ rest.length := ⟨h63, hr⟩
  simp only [Found, labelsN_cons]
  simp only [h0, hb, ↓reduceIte, and_self]
  cases labelsN (rest.drop b.val) with
  | none => simp
  | some p =>
    obtain ⟨ls', k'⟩ := p
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_assoc,
      List.singleton_append]
    constructor
    · rintro ⟨⟨rfl, rfl⟩, h⟩; exact ⟨ls', k', rfl, rfl, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨ls'', k'', rfl, rfl, ⟨rfl, rfl⟩, h⟩; exact ⟨⟨rfl, rfl⟩, h⟩

theorem read_name_loop_bad (msg : Slice U8) (text : Array U8 253#usize) (pos n : Usize) :
    read_name_loop msg text pos n false true = ok (text, pos, n, true) := by
  rw [read_name_loop]; simp

theorem read_name_loop_done (msg : Slice U8) (text : Array U8 253#usize) (pos n : Usize) :
    read_name_loop msg text pos n true false = ok (text, pos, n, false) := by
  rw [read_name_loop]; simp

/-- **Spec theorem for `read_name`'s loop**: after the labels `acc` (whose
    text is `text[..n]`), reads the rest of the name at `msg[pos..]`. -/
@[step]
theorem read_name_loop.spec (msg : Slice U8) (text : Array U8 253#usize) (pos n : Usize)
    (acc : List (List U8)) (hpos : pos.val ≤ msg.length) (hn : n.val = (dotted acc).length)
    (hn253 : n.val ≤ 253) (hacc : acc = [] ↔ n.val = 0) (htext : text.val.take n.val = dotted acc) :
    read_name_loop msg text pos n false false ⦃ (r : Array U8 253#usize × Usize × Usize × Bool) =>
      if r.2.2.2 then ∀ ls k, ¬ Found (msg.val.drop pos.val) acc ls k
      else ∃ ls k, Found (msg.val.drop pos.val) acc ls k ∧ r.2.1.val = pos.val + k ∧
        r.2.2.1.val = (dotted (acc ++ ls)).length ∧ r.1.val.take r.2.2.1.val = dotted (acc ++ ls) ⦄ := by
  rw [read_name_loop]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hpos' : pos.val ≤ msg.val.length := hpos
  split
  · rw [read_name_loop_bad]
    simp only [WP.spec_ok, ↓reduceIte]
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    exact found_nil acc
  step as ⟨b, hb⟩
  step as ⟨l, hl⟩
  have hlt : pos.val < msg.val.length := by scalar_tac
  have hd : msg.val.drop pos.val = b :: msg.val.drop (pos.val + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hb]
  have hlb : l.val = b.val := by rw [hl]; simp
  obtain ⟨sep, hsep, hsepv⟩ : ∃ sep : Usize,
      (if n > 0#usize then ok 1#usize else ok 0#usize : Result Usize) = ok sep ∧
        sep.val = if acc = [] then 0 else 1 := by
    split
    · refine ⟨_, rfl, ?_⟩
      have : acc ≠ [] := fun h => by have := hacc.1 h; scalar_tac
      simp [this]
    · refine ⟨_, rfl, ?_⟩
      have : acc = [] := hacc.2 (by scalar_tac)
      simp [this]
  rw [hsep]
  simp only [bind_ok]
  rw [hd]
  have hrest : (msg.val.drop (pos.val + 1)).length = msg.val.length - pos.val - 1 := by simp; omega
  split
  · step as ⟨pos1, hpos1⟩
    rw [read_name_loop_done]
    simp only [WP.spec_ok, Bool.false_eq_true, ↓reduceIte]
    refine ⟨[], 1, (found_zero _ _ _ _ _ (by scalar_tac)).2 ⟨rfl, rfl, by omega⟩, by scalar_tac,
      by simp [hn], by simp [htext]⟩
  split
  · rw [read_name_loop_bad]
    simp only [WP.spec_ok, ↓reduceIte]
    intro ls k
    exact found_bad _ _ _ _ _ (by scalar_tac) (by scalar_tac)
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  split
  · rw [read_name_loop_bad]
    simp only [WP.spec_ok, ↓reduceIte]
    intro ls k
    exact found_bad _ _ _ _ _ (by scalar_tac) (by rw [hrest]; scalar_tac)
  have h0 : b.val ≠ 0 := by scalar_tac
  have h63 : b.val ≤ 63 := by scalar_tac
  have hr : b.val ≤ (msg.val.drop (pos.val + 1)).length := by rw [hrest]; scalar_tac
  -- The label, and the text with it.
  let lab := (msg.val.drop (pos.val + 1)).take b.val
  have hlab : lab.length = b.val := by simp [lab]; omega
  have hsnoc : (dotted (acc ++ [lab])).length = n.val + sep.val + l.val := by
    rw [dotted_snoc]; split <;> simp_all; omega
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  split
  · rw [read_name_loop_bad]
    simp only [WP.spec_ok, ↓reduceIte]
    intro ls k hf
    obtain ⟨ls', k', rfl, rfl, -⟩ := (found_cons _ _ _ _ _ h0 h63 hr).1 hf
    have h1 := dotted_le (acc ++ [lab]) ls'
    have h2 : (dotted (acc ++ lab :: ls')).length ≤ 253 := hf.2
    rw [List.append_assoc, List.singleton_append] at h1
    scalar_tac
  have hlt253 : n.val < 253 := by scalar_tac
  -- The separating dot, then the label.
  have key : (if sep = 1#usize then text.update n 46#u8 else ok text) ⦃ (t1 : Array U8 253#usize) =>
      t1.val.take (n.val + sep.val) = dotted acc ++ (if acc = [] then [] else [46#u8]) ⦄ := by
    split
    · rename_i hs
      have hne : acc ≠ [] := by
        intro h; simp only [h, ↓reduceIte] at hsepv; scalar_tac
      step as ⟨t1, ht1⟩
      have hs1 : sep.val = 1 := by scalar_tac
      have hlen : n.val < text.val.length := by simp; scalar_tac
      rw [ht1, Array.set_val_eq, hs1, take_set_succ _ _ _ hlen, htext]
      simp [hne]
    · rename_i hs
      have he : acc = [] := by
        by_contra hne; simp only [hne, ↓reduceIte] at hsepv; exact hs (by scalar_tac)
      have hs0 : sep.val = 0 := by simp [he] at hsepv; exact hsepv
      simp only [WP.spec_ok]
      rw [hs0, Nat.add_zero, htext]; simp [he]
  step with key as ⟨text1, ht1⟩
  step as ⟨i7, hi7⟩
  step as ⟨text2, ht2⟩
  step as ⟨i8, hi8⟩
  step as ⟨n1, hn1⟩
  step as ⟨i9, hi9⟩
  step as ⟨pos1, hpos1⟩
  have hlabv : (msg.val.drop i7.val).take l.val = lab := by simp only [lab, hi7, hlb]
  have hacc' : acc ++ [lab] = [] ↔ n1.val = 0 := by
    simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_iff]; scalar_tac
  have htext2 : text2.val.take n1.val = dotted (acc ++ [lab]) := by
    rw [dotted_snoc, show n1.val = i5.val + l.val by scalar_tac, ht2,
      show i5.val = n.val + sep.val by scalar_tac, ht1, hlabv]
  have hdrop : msg.val.drop pos1.val = (msg.val.drop (pos.val + 1)).drop b.val := by
    rw [List.drop_drop]; congr 1; scalar_tac
  apply WP.spec_mono (read_name_loop.spec msg text2 pos1 n1 (acc ++ [lab]) (by scalar_tac)
    (by rw [hsnoc]; scalar_tac) (by scalar_tac) hacc' htext2)
  intro q hq
  rw [hdrop] at hq
  split
  · rename_i hbad
    simp only [hbad, ↓reduceIte] at hq
    intro ls k hf
    obtain ⟨ls', k', rfl, rfl, hf'⟩ := (found_cons _ _ _ _ _ h0 h63 hr).1 hf
    exact hq ls' k' hf'
  · rename_i hgood
    simp only [hgood, Bool.false_eq_true, ↓reduceIte] at hq
    obtain ⟨ls', k', hf', hp, hn', ht'⟩ := hq
    refine ⟨lab :: ls', 1 + b.val + k', (found_cons _ _ _ _ _ h0 h63 hr).2 ⟨ls', k', rfl, rfl, hf'⟩,
      by scalar_tac, ?_, ?_⟩
    · rw [hn']; simp
    · rw [ht']; simp
termination_by msg.length - pos.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `read_name`**: the name after the header as dotted
    text in `text[..n]`, and the position after it; `None` if there is no
    valid name of at most 253 characters there, or it is the root. -/
@[step]
theorem read_name.spec (msg : Slice U8) (text : Array U8 253#usize) (h12 : 12 ≤ msg.length) :
    read_name msg text ⦃ (r : Option (Usize × Usize) × Array U8 253#usize) =>
      match r.1 with
      | none => ∀ ls k, Found (msg.val.drop 12) [] ls k → dotted ls = []
      | some (n, pos) => ∃ ls k, Found (msg.val.drop 12) [] ls k ∧ dotted ls ≠ [] ∧
          pos.val = 12 + k ∧ n.val = (dotted ls).length ∧ r.2.val.take n.val = dotted ls ⦄ := by
  unfold read_name
  step with read_name_loop.spec msg text HEADER_LEN 0#usize [] (by scalar_tac)
    (by simp [dotted]) (by simp) (by simp) (by simp [dotted]) as ⟨text1, pos, n, bad, hr⟩
  cases bad
  · simp only [Bool.false_eq_true, ↓reduceIte, HEADER_LEN_val, List.nil_append] at hr ⊢
    obtain ⟨ls, k, hf, hp, hn, ht⟩ := hr
    split
    · simp only [WP.spec_ok]
      intro ls' k' hf'
      obtain ⟨rfl, -⟩ := hf.unique hf'
      rw [← List.length_eq_zero_iff]; scalar_tac
    · simp only [WP.spec_ok]
      refine ⟨ls, k, hf, fun h => ?_, hp, hn, ht⟩
      simp only [h, List.length_nil] at hn; scalar_tac
  · simp only [↓reduceIte, HEADER_LEN_val, WP.spec_ok] at hr ⊢
    intro ls k hf; exact absurd hf (hr ls k)

/-! ## Queries -/

/-- `m` is a standard query (QR = 0, opcode 0) with one question and no
    answer or authority records, which decodes as `q`: the header is the
    first 12 bytes; the question name follows, as labels, its text at most
    253 characters and not empty (once a trailing dot is dropped); then 4
    bytes of QTYPE and QCLASS. `q.name` is that text, lowercased. -/
def DnsQuery.Spec (m : List U8) (q : DnsQuery) : Prop :=
  12 ≤ m.length ∧ FmtD DnsHeader.Insts.UntrustedReaderDecode (m.take 12) q.header 12 ∧
    (q.header.flags : U16).val / 2048 = 0 ∧ (q.header.qdcount : U16).val = 1 ∧
    (q.header.ancount : U16).val = 0 ∧ (q.header.nscount : U16).val = 0 ∧
    ∃ ls k, Found (m.drop 12) [] ls k ∧ 12 + k + 4 ≤ m.length ∧
      name.strip (dotted ls) ≠ [] ∧ q.name.Inv ∧
      q.name.text = ((name.strip (dotted ls)).map (·.val)).map name.lowerN ∧
      q.qtype.val = m[12 + k]!.val * 256 + m[13 + k]!.val ∧
      q.qclass.val = m[14 + k]!.val * 256 + m[15 + k]!.val ∧
      q.question_len.val = k + 4

/-- **Spec theorem for `<DnsQuery as Validate<&[u8]>>::validate`**: accepts
    exactly the standard queries with one question. -/
@[step]
theorem DnsQuery.Insts.UntrustedValidateShared0SliceU8ValidationError.validate.spec
    (msg : Slice U8) :
    DnsQuery.Insts.UntrustedValidateShared0SliceU8ValidationError.validate msg
      ⦃ (r : core.result.Result DnsQuery ValidationError) =>
        match r with
        | .Ok q => DnsQuery.Spec msg.val q
        | .Err _ => ∀ q, ¬ DnsQuery.Spec msg.val q ⦄ := by
  unfold DnsQuery.Insts.UntrustedValidateShared0SliceU8ValidationError.validate
  dsimp only
  split
  · simp only [WP.spec_ok]
    rintro q ⟨h12, -⟩; scalar_tac
  rename_i h12
  have h12' : 12 ≤ msg.val.length := by scalar_tac
  step as ⟨s, hs, hsl⟩
  step as ⟨u, hu⟩
  have hus : (u : Slice U8).val = msg.val.take 12 := by rw [hu, hs]; simp [List.slice]
  have hlen : (msg.val.take 12).length = 12 := by simp; omega
  apply WP.spec_bind (UntrustedShared0SliceU8.read_all.spec_of DnsHeader.Insts.UntrustedReaderDecode u)
  rintro (h | e) hres
  · simp only [hus, hlen] at hres
    have huniq : ∀ q, DnsQuery.Spec msg.val q → q.header = h := fun q hq =>
      ((FmtLaws DnsHeader.Insts.UntrustedReaderDecode).functional _ _ _ _ _ hq.2.1 hres).1
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step*
    -- The header checks.
    all_goals try (
      intro q hq
      have he := huniq q hq
      obtain ⟨-, -, hf, hqd, han, hns, -⟩ := hq
      rw [he] at hf hqd han hns
      simp only [bne_iff_ne, ne_eq] at *
      scalar_tac)
    -- No name.
    · rintro q ⟨-, -, -, -, -, -, ls, k, hfd, -, hstr, -⟩
      subst_vars
      have := o_post ls k hfd
      rw [this] at hstr; exact hstr (by simp [name.strip])
    rename_i r1 ho
    obtain ⟨n, e⟩ := r1
    subst ho
    obtain ⟨ls, k, hf, hne, hp, hn, ht⟩ := o_post
    have hk : 12 + k ≤ msg.val.length := by
      have := labelsN_le _ _ _ hf.1; simp at this; omega
    have hdl : (dotted ls).length ≤ 253 := by simpa using hf.2
    step*
    -- No room for QTYPE and QCLASS.
    · rintro q ⟨-, -, -, -, -, -, ls', k', hf', h4, -⟩
      obtain ⟨rfl, rfl⟩ := hf.unique hf'
      scalar_tac
    -- The name is empty once a trailing dot is dropped.
    · rintro q ⟨-, -, -, -, -, -, ls', k', hf', -, hstr, -⟩
      obtain ⟨hl, hk'⟩ := hf.unique hf'
      subst hl hk'
      have hs1 : s1.val = dotted ls := by rw [s1_post, ← ht]; simp [List.slice]
      subst_vars
      dsimp only at o1_post
      rw [hs1] at o1_post
      have := strip_length_le (dotted ls)
      rcases o1_post with h0 | h0
      · exact hstr h0
      · omega
    -- The query.
    have hs1 : s1.val = dotted ls := by rw [s1_post, ← ht]; simp [List.slice]
    have h4 : 12 + k + 4 ≤ msg.val.length := by
      have h7 := ‹¬i7 < 4#usize›
      simp only [UScalar.lt_equiv, not_lt] at h7
      have hml : msg.len.val = msg.val.length := by simp
      have h4v : (4#usize : Usize).val = 4 := by simp
      omega
    have e0 : (h.flags : U16).val / 2048 = 0 := by
      rw [← i2_post, bne_false ‹¬(i2 != 0#u16) = true›]; rfl
    have e1 : (h.qdcount : U16).val = 1 := bne_false ‹¬(h.qdcount != 1#u16) = true›
    have e2 : (h.ancount : U16).val = 0 := bne_false ‹¬(h.ancount != 0#u16) = true›
    have e3 : (h.nscount : U16).val = 0 := bne_false ‹¬(h.nscount != 0#u16) = true›
    have hql : i24.val = k + 4 := by simp only [i24_post, i23_post, HEADER_LEN_val]; omega
    subst_vars
    dsimp only at o1_post
    rw [hs1] at o1_post
    obtain ⟨hinv, hlen1, htext⟩ := o1_post
    refine ⟨h12', hres, e0, e1, e2, e3, ls, k, hf, h4, ?_, hinv, htext, ?_, ?_, hql⟩
    · intro h0
      have := congrArg List.length htext
      simp only [diomede.name.Name.text, h0, List.map_nil, List.length_map, List.length_take,
        List.length_nil] at this
      simp only [diomede.name.Name.Inv] at hinv
      simp at this
      omega
    · rw [getElem!_pos msg.val (12 + k) (by omega), getElem!_pos msg.val (13 + k) (by omega)]
      simp +arith [i14_post, i10_post, i11_post, hp]
    · rw [getElem!_pos msg.val (14 + k) (by omega), getElem!_pos msg.val (15 + k) (by omega)]
      simp +arith [i22_post, i18_post, i15_post, i19_post, hp]
  · simp only [hus, hlen] at hres
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    rintro q ⟨-, hD, -⟩
    exact hres q.header hD

/-! ## NXDOMAIN answers -/

/-- The answer with response code `rcode` to the query `q` decoded from `m`,
    as byte values: the ID; QR = 1, opcode 0, AA = TC = 0, RD as asked;
    RA = 1, Z = 0, RCODE; one question and no records; then the question, as
    asked. -/
def answerN (m : List U8) (q : DnsQuery) (rcode : Nat) : List Nat :=
  [(q.header.id : U16).val / 256, (q.header.id : U16).val % 256,
    128 + (q.header.flags : U16).val / 256 % 2, 128 + rcode % 16, 0, 1, 0, 0, 0, 0, 0, 0] ++
    ((m.drop 12).take q.question_len.val).map (·.val)

/-- **Spec theorem for `answer`**: writes the answer to the start of `out`,
    if both `msg` and `out` hold `12 + question_len` bytes; the rest of `out`
    is kept. -/
@[step]
theorem answer.spec (msg : Slice U8) (q : DnsQuery) (rcode : U8) (out : Slice U8)
    (hq : 12 + q.question_len.val ≤ Usize.max) :
    answer msg q rcode out ⦃ (r : Option Usize × Slice U8) =>
      match r.1 with
      | none => (msg.length < 12 + q.question_len.val ∨ out.length < 12 + q.question_len.val) ∧
          r.2 = out
      | some n => n.val = 12 + q.question_len.val ∧ n.val ≤ out.length ∧ r.2.length = out.length ∧
          (r.2.val.take n.val).map (·.val) = answerN msg.val q rcode.val ∧
          r.2.val.drop n.val = out.val.drop n.val ⦄ := by
  unfold answer
  step as ⟨n, hn⟩
  split
  · simp only [WP.spec_ok]; exact ⟨Or.inl (by scalar_tac), trivial⟩
  split
  · simp only [WP.spec_ok]; exact ⟨Or.inr (by scalar_tac), trivial⟩
  step*
  apply WP.spec_bind (untrusted.writer.encode_into.spec Answer.Insts.UntrustedWriterEncode _ out)
  rintro ⟨r, out1⟩ ⟨hl, h⟩
  simp only [uncurry]
  have h12 : 12 ≤ n.val := by scalar_tac
  have hql : n.val - 12 = q.question_len.val := by scalar_tac
  have hs : s.val = (msg.val.drop 12).take q.question_len.val := by
    rw [s_post, List.slice, HEADER_LEN_val, hql]
  have hsl : s.val.length = q.question_len.val := by
    simp only [Slice.length] at s_post1; rw [s_post1, HEADER_LEN_val, hql]
  cases r
  · rename_i a
    obtain ⟨hm, hroom, hout⟩ := h
    simp only [WP.spec_ok]
    simp only [untrusted.writer.FmtE, untrusted.writer.Eseq, untrusted.writer.Enil, Answer.fields, DnsHeader.fields,
      List.length_append, untrusted.writer.beBytes_length, List.append_nil, hsl] at hm hout
    have ha : a.val = n.val := by omega
    rw [ha]
    refine ⟨by omega, by scalar_tac, hl, ?_, ?_⟩
    · rw [hout, List.take_left' (by simp [hsl]; scalar_tac)]
      have hid : (q.header.id : U16).val < 65536 := by scalar_tac
      have hi8 : i8.val < 65536 := by scalar_tac
      simp only [answerN, List.map_append, hs, untrusted.writer.beBytes, List.map_cons,
        List.map_nil, untrusted.writer.byte_val, List.cons_append, List.nil_append]
      simp only [i8_post, i5_post, i4_post, rd_post, i3_post, i7_post, i6_post,
        UScalar.cast_val_eq] at hi8 ⊢
      simp only [List.cons.injEq]
      simp at hi8 ⊢
      omega
    · rw [hout, List.drop_left' (by simp [hsl]; scalar_tac)]
      rw [show 2 + (2 + (2 + (2 + (2 + 2)))) + q.question_len.val = n.val by scalar_tac]
  · exfalso
    simp only [untrusted.writer.FmtE, untrusted.writer.Eseq, untrusted.writer.Enil, Answer.fields, DnsHeader.fields,
      List.length_append, untrusted.writer.beBytes_length, List.length_nil, hsl] at h
    scalar_tac

end diomede.dns
