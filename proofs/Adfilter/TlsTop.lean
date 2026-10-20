/- Specs of `adfilter::tls`: the server name of a TLS ClientHello
   (RFC 8446 §4.1.2, RFC 6066 §3). -/
import Adfilter.NameTop

open Aeneas Aeneas.Std Result untrusted

namespace adfilter.tls

@[simp, scalar_tac_simps] theorem RECORD_HEADER_LEN_val : RECORD_HEADER_LEN.val = 5 := by
  simp [RECORD_HEADER_LEN]
@[simp, scalar_tac_simps] theorem HANDSHAKE_HEADER_LEN_val : HANDSHAKE_HEADER_LEN.val = 4 := by
  simp [HANDSHAKE_HEADER_LEN]
@[simp, scalar_tac_simps] theorem VERSION_RANDOM_LEN_val : VERSION_RANDOM_LEN.val = 34 := by
  simp [VERSION_RANDOM_LEN]
@[simp, scalar_tac_simps] theorem EXT_SERVER_NAME_val : EXT_SERVER_NAME.val = 0 := by
  simp [EXT_SERVER_NAME]
@[simp, scalar_tac_simps] theorem HOST_NAME_val : HOST_NAME.val = 0 := by simp [HOST_NAME]
@[simp, scalar_tac_simps] theorem CONTENT_HANDSHAKE_val : CONTENT_HANDSHAKE.val = 22 := by
  simp [CONTENT_HANDSHAKE]
@[simp, scalar_tac_simps] theorem CLIENT_HELLO_val : CLIENT_HELLO.val = 1 := by simp [CLIENT_HELLO]

/-! ## The wire format, on lists -/

/-- The big-endian 16-bit number at `l[i..i + 2]`. -/
def be16N (l : List U8) (i : Nat) : Nat := l[i]!.val * 256 + l[i + 1]!.val

/-- A vector with a 1-byte length at the start of `l`: its contents and the
    rest. -/
def vec8N : List U8 → Option (List U8 × List U8)
  | [] => none
  | n :: rest => if n.val ≤ rest.length then some (rest.take n.val, rest.drop n.val) else none

/-- A vector with a 2-byte length at the start of `l`: its contents and the
    rest. -/
def vec16N : List U8 → Option (List U8 × List U8)
  | a :: b :: rest =>
    if a.val * 256 + b.val ≤ rest.length then
      some (rest.take (a.val * 256 + b.val), rest.drop (a.val * 256 + b.val))
    else none
  | _ => none

/-- The extensions filling `l` exactly: the type and data of each. -/
def extsN : List U8 → Option (List (Nat × List U8))
  | [] => some []
  | a :: b :: c :: d :: rest =>
    if c.val * 256 + d.val ≤ rest.length then
      (extsN (rest.drop (c.val * 256 + d.val))).map
        ((a.val * 256 + b.val, rest.take (c.val * 256 + d.val)) :: ·)
    else none
  | _ => none
termination_by l => l.length
decreasing_by simp; omega

/-- The host name in the data `d` of a server_name extension: the list fills
    `d`, and its first entry is a host name. -/
def hostN : List U8 → Option (List U8)
  | l1 :: l2 :: t :: rest =>
    if l1.val * 256 + l2.val = rest.length + 1 ∧ t.val = 0 then (vec16N rest).map (·.1) else none
  | _ => none

/-- The server name from the optional extensions `l` ending a ClientHello:
    `some none` if there are none, or no server_name extension. -/
def extensionsN (l : List U8) : Option (Option (List U8)) :=
  if l = [] then some none else
  match vec16N l with
  | none => none
  | some (e, rest) => if rest ≠ [] then none else
    match extsN e with
    | none => none
    | some exts => match exts.find? (fun x => x.1 = 0) with
      | none => some none
      | some x => (hostN x.2).map some

/-- The server name from the ClientHello `l` after its version and random:
    the session ID, cipher suites and compression methods, then the
    extensions. -/
def afterRandomN (l : List U8) : Option (Option (List U8)) :=
  match vec8N l with
  | none => none
  | some (_, r1) => match vec16N r1 with
    | none => none
    | some (_, r2) => match vec8N r2 with
      | none => none
      | some (_, r3) => extensionsN r3

/-- The server name of the ClientHello `body`, if it has one: `none` if
    `body` is not a well-formed ClientHello, `some none` if it has no
    server_name extension. -/
def helloN (body : List U8) : Option (Option (List U8)) :=
  if body.length < 34 then none else afterRandomN (body.drop 34)

/-- The fragment of the record at the start of `r`, if it is a handshake
    record of versions 3.0 to 3.4. -/
def fragmentN : List U8 → Option (List U8)
  | t :: v1 :: v2 :: l1 :: l2 :: rest =>
    if t.val = 22 ∧ v1.val = 3 ∧ v2.val ≤ 4 ∧ l1.val * 256 + l2.val ≤ rest.length then
      some (rest.take (l1.val * 256 + l2.val))
    else none
  | _ => none

/-- The body of the handshake message at the start of `f`, if it is a
    ClientHello. -/
def bodyN : List U8 → Option (List U8)
  | t :: a :: b :: c :: rest =>
    if t.val = 1 ∧ a.val * 65536 + b.val * 256 + c.val ≤ rest.length then
      some (rest.take (a.val * 65536 + b.val * 256 + c.val))
    else none
  | _ => none

/-- The server name of the ClientHello at the start of the TLS stream `r`. -/
def serverNameN (r : List U8) : Option (Option (List U8)) :=
  match fragmentN r with
  | none => none
  | some f => match bodyN f with
    | none => none
    | some body => helloN body

/-- `r` starts with a ClientHello (in one record) asking for the server name
    of `c`: none, or a host name that is not empty and at most 253
    characters once a trailing dot is dropped, lowercased. -/
def ClientHello.Spec (r : List U8) (c : ClientHello) : Prop :=
  match serverNameN r, c.server_name with
  | some none, none => True
  | some (some h), some n =>
    name.strip h ≠ [] ∧ (name.strip h).length ≤ 253 ∧ n.Inv ∧
      n.text = ((name.strip h).map (·.val)).map name.lowerN
  | _, _ => False

theorem be16N_lt (l : List U8) (i : Nat) : be16N l i < 65536 := by
  unfold be16N; scalar_tac

/-! ## Windows -/

/-- The bytes `b[p..e]`. -/
def win (b : List U8) (p e : Nat) : List U8 := (b.drop p).take (e - p)

theorem win_length (b : List U8) (p e : Nat) (h : e ≤ b.length) : (win b p e).length = e - p := by
  simp [win]; omega

theorem win_nil (b : List U8) (p : Nat) : win b p p = [] := by simp [win]

theorem win_cons (b : List U8) (p e : Nat) (hp : p < e) (he : e ≤ b.length) :
    win b p e = b[p]! :: win b (p + 1) e := by
  unfold win
  rw [List.drop_eq_getElem_cons (by omega), show e - p = (e - (p + 1)) + 1 by omega,
    List.take_succ_cons, getElem!_pos b p (by omega)]

theorem win_take (b : List U8) (p e n : Nat) (h : p + n ≤ e) :
    (win b p e).take n = win b p (p + n) := by
  simp only [win, List.take_take]; congr 1; omega

theorem win_drop (b : List U8) (p e n : Nat) (_h : p + n ≤ e) :
    (win b p e).drop n = win b (p + n) e := by
  simp only [win, List.drop_take, List.drop_drop]; congr 1; omega

theorem vec8N_win (b : List U8) (p e : Nat) (hp : p < e) (he : e ≤ b.length) :
    vec8N (win b p e) =
      if b[p]!.val ≤ e - p - 1 then
        some (win b (p + 1) (p + 1 + b[p]!.val), win b (p + 1 + b[p]!.val) e)
      else none := by
  rw [win_cons b p e hp he]
  simp only [vec8N, win_length b _ _ he]
  by_cases hc : b[p]!.val ≤ e - p - 1
  · have hc' : b[p]!.val ≤ e - (p + 1) := by omega
    simp only [hc, hc', ↓reduceIte]
    rw [win_take _ _ _ _ (by omega), win_drop _ _ _ _ (by omega)]
  · have hc' : ¬ b[p]!.val ≤ e - (p + 1) := by omega
    simp only [hc, hc', ↓reduceIte]

theorem vec16N_win (b : List U8) (p e : Nat) (hp : p + 2 ≤ e) (he : e ≤ b.length) :
    vec16N (win b p e) =
      if be16N b p ≤ e - p - 2 then
        some (win b (p + 2) (p + 2 + be16N b p), win b (p + 2 + be16N b p) e)
      else none := by
  rw [win_cons b p e (by omega) he, win_cons b (p + 1) e (by omega) he]
  simp only [vec16N, win_length b _ _ he, show p + 1 + 1 = p + 2 from rfl]
  unfold be16N
  by_cases hc : b[p]!.val * 256 + b[p + 1]!.val ≤ e - p - 2
  · have hc' : b[p]!.val * 256 + b[p + 1]!.val ≤ e - (p + 2) := by omega
    simp only [hc, hc', ↓reduceIte]
    rw [win_take _ _ _ _ (by omega), win_drop _ _ _ _ (by omega)]
  · have hc' : ¬ b[p]!.val * 256 + b[p + 1]!.val ≤ e - (p + 2) := by omega
    simp only [hc, hc', ↓reduceIte]

theorem vec16N_short (b : List U8) (p e : Nat) (hp : e < p + 2) (he : e ≤ b.length) :
    vec16N (win b p e) = none := by
  have : (win b p e).length < 2 := by rw [win_length b _ _ he]; omega
  match h : win b p e with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rw [h] at this; simp at this

/-! ## Reading lengths -/

/-- **Spec theorem for `be16`**. -/
@[step]
theorem be16.spec (b : Slice U8) (at' : Usize) (h : at'.val + 1 < b.length) :
    be16 b at' ⦃ (r : Usize) => r.val = be16N b.val at'.val ⦄ := by
  unfold be16
  have h' : at'.val + 1 < b.val.length := h
  step*
  unfold be16N
  rw [getElem!_pos b.val at'.val (by omega), getElem!_pos b.val (at'.val + 1) (by omega)]
  simp [r_post, i2_post, i5_post, i1_post, i_post, i4_post, i3_post]

/-- **Spec theorem for `skip_vector8`**: the end of the vector at
    `b[pos..end]`. -/
@[step]
theorem skip_vector8.spec (b : Slice U8) (pos end' : Usize) (hp : pos.val ≤ end'.val)
    (he : end'.val ≤ b.length) :
    skip_vector8 b pos end' ⦃ (r : Option Usize) =>
      match r with
      | none => vec8N (win b.val pos.val end'.val) = none
      | some p => pos.val < p.val ∧ p.val ≤ end'.val ∧
          vec8N (win b.val pos.val end'.val) =
            some (win b.val (pos.val + 1) p.val, win b.val p.val end'.val) ⦄ := by
  unfold skip_vector8
  have he' : end'.val ≤ b.val.length := he
  split
  · simp only [WP.spec_ok]
    rw [show pos.val = end'.val by scalar_tac, win_nil]; rfl
  step as ⟨c, hc⟩
  step as ⟨n, hn⟩
  have hcv : b.val[pos.val]! = c := by rw [getElem!_pos b.val pos.val (by scalar_tac), hc]
  have hnv : n.val = c.val := by rw [hn]; simp
  rw [vec8N_win _ _ _ (by scalar_tac) he', hcv]
  step*
  refine ⟨by scalar_tac, by scalar_tac, ?_⟩
  have hc' : c.val ≤ end'.val - pos.val - 1 := by scalar_tac
  have hi4 : i4.val = pos.val + 1 + c.val := by scalar_tac
  simp only [hc', ↓reduceIte, hi4]

/-- **Spec theorem for `skip_vector16`**: the end of the vector at
    `b[pos..end]`. -/
@[step]
theorem skip_vector16.spec (b : Slice U8) (pos end' : Usize) (hp : pos.val ≤ end'.val)
    (he : end'.val ≤ b.length) :
    skip_vector16 b pos end' ⦃ (r : Option Usize) =>
      match r with
      | none => vec16N (win b.val pos.val end'.val) = none
      | some p => pos.val + 2 ≤ p.val ∧ p.val ≤ end'.val ∧
          vec16N (win b.val pos.val end'.val) =
            some (win b.val (pos.val + 2) p.val, win b.val p.val end'.val) ⦄ := by
  unfold skip_vector16
  have he' : end'.val ≤ b.val.length := he
  step as ⟨i, hi⟩
  split
  · simp only [WP.spec_ok]
    exact vec16N_short _ _ _ (by scalar_tac) he'
  step as ⟨n, hn⟩
  rw [vec16N_win _ _ _ (by scalar_tac) he']
  step*
  · have hc : ¬ be16N b.val pos.val ≤ end'.val - pos.val - 2 := by scalar_tac
    simp only [hc, ↓reduceIte]
  · refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    have hc : be16N b.val pos.val ≤ end'.val - pos.val - 2 := by scalar_tac
    have hi3 : i3.val = pos.val + 2 + be16N b.val pos.val := by scalar_tac
    simp only [hc, ↓reduceIte, hi3]

/-! ## Extensions -/

theorem extsN_nil (b : List U8) (p : Nat) : extsN (win b p p) = some [] := by
  rw [win_nil, extsN]

theorem extsN_short (b : List U8) (p e : Nat) (hp : p < e) (h4 : e < p + 4) (he : e ≤ b.length) :
    extsN (win b p e) = none := by
  have hl := win_length b p e he
  match h : win b p e with
  | [] => rw [h] at hl; simp at hl; omega
  | [_] => rw [extsN] <;> simp
  | [_, _] => rw [extsN] <;> simp
  | [_, _, _] => rw [extsN] <;> simp
  | _ :: _ :: _ :: _ :: _ => rw [h] at hl; simp at hl; omega

theorem extsN_win (b : List U8) (p e : Nat) (hp : p + 4 ≤ e) (he : e ≤ b.length) :
    extsN (win b p e) =
      if be16N b (p + 2) ≤ e - p - 4 then
        (extsN (win b (p + 4 + be16N b (p + 2)) e)).map
          ((be16N b p, win b (p + 4) (p + 4 + be16N b (p + 2))) :: ·)
      else none := by
  rw [win_cons b p e (by omega) he, win_cons b (p + 1) e (by omega) he,
    win_cons b (p + 1 + 1) e (by omega) he, win_cons b (p + 1 + 1 + 1) e (by omega) he, extsN]
  simp only [win_length b _ _ he, show p + 1 + 1 = p + 2 from rfl, show p + 2 + 1 = p + 3 from rfl,
    show p + 3 + 1 = p + 4 from rfl]
  unfold be16N
  simp only [show p + 2 + 1 = p + 3 from rfl]
  by_cases hc : b[p + 2]!.val * 256 + b[p + 3]!.val ≤ e - p - 4
  · have hc' : b[p + 2]!.val * 256 + b[p + 3]!.val ≤ e - (p + 4) := by omega
    simp only [hc, hc', ↓reduceIte]
    rw [win_take _ _ _ _ (by omega), win_drop _ _ _ _ (by omega)]
  · have hc' : ¬ b[p + 2]!.val * 256 + b[p + 3]!.val ≤ e - (p + 4) := by omega
    simp only [hc, hc', ↓reduceIte]

theorem find_server_name_loop_bad (b : Slice U8) (end' pos : Usize) (found : Bool) (at' len : Usize) :
    find_server_name_loop b end' pos found at' len true = ok (found, at', len, true) := by
  rw [find_server_name_loop]; split <;> rfl

/-- **Spec theorem for `find_server_name`'s loop**: walks the extensions
    filling `b[pos..end]`; if no server_name extension was `found` before,
    finds the first. -/
@[step]
theorem find_server_name_loop.spec (b : Slice U8) (end' pos : Usize) (found : Bool)
    (at' len : Usize) (hp : pos.val ≤ end'.val) (he : end'.val ≤ b.length)
    (hat : found = true → at'.val + len.val ≤ end'.val) :
    find_server_name_loop b end' pos found at' len false
      ⦃ (r : Bool × Usize × Usize × Bool) =>
        if r.2.2.2 then extsN (win b.val pos.val end'.val) = none
        else ∃ exts, extsN (win b.val pos.val end'.val) = some exts ∧
          if found then r.1 = true ∧ r.2.1 = at' ∧ r.2.2.1 = len
          else match exts.find? (fun x => x.1 = 0) with
            | none => r.1 = false
            | some x => r.1 = true ∧ r.2.1.val + r.2.2.1.val ≤ end'.val ∧
                win b.val r.2.1.val (r.2.1.val + r.2.2.1.val) = x.2 ⦄ := by
  rw [find_server_name_loop]
  have he' : end'.val ≤ b.val.length := he
  split
  swap
  · simp only [WP.spec_ok, Bool.false_eq_true, ↓reduceIte]
    rw [show pos.val = end'.val by scalar_tac]
    refine ⟨[], extsN_nil _ _, ?_⟩
    cases found <;> simp
  simp only [Bool.false_eq_true, ↓reduceIte]
  step as ⟨i, hi⟩
  split
  · rw [find_server_name_loop_bad]
    simp only [WP.spec_ok, ↓reduceIte]
    exact extsN_short _ _ _ (by scalar_tac) (by scalar_tac) he'
  step as ⟨ty, hty⟩
  step as ⟨i1, hi1⟩
  step as ⟨n, hn⟩
  step as ⟨i2, hi2⟩
  have hx := extsN_win b.val pos.val end'.val (by scalar_tac) he'
  rw [← hi1, ← hn, ← hty] at hx
  split
  · rw [find_server_name_loop_bad]
    simp only [WP.spec_ok, ↓reduceIte]
    rw [hx, if_neg (by scalar_tac)]
  rw [if_pos (by scalar_tac)] at hx
  have key : (if found = true then ok (found, at', len)
      else if ty = EXT_SERVER_NAME then do
        let at2 ← pos + 4#usize
        ok (true, at2, n)
      else ok (found, at', len) : Result (Bool × Usize × Usize)) ⦃ (t : Bool × Usize × Usize) =>
        if found then t = (found, at', len)
        else if ty.val = 0 then t.1 = true ∧ t.2.1.val = pos.val + 4 ∧ t.2.2 = n
        else t = (false, at', len) ⦄ := by
    cases found
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · have : ty.val = 0 := by scalar_tac
        simp only [this, ↓reduceIte]
        step*
      · have : ¬ ty.val = 0 := fun h => by rename_i hne; exact hne (by scalar_tac)
        simp only [this, ↓reduceIte, WP.spec_ok]
    · simp only [↓reduceIte, WP.spec_ok]
  step with key as ⟨found1, at1, len1, hk⟩
  step as ⟨i3, hi3⟩
  step as ⟨pos1, hpos1⟩
  have hat1 : found1 = true → at1.val + len1.val ≤ end'.val := by
    intro h1
    split at hk
    · obtain ⟨rfl, rfl, rfl⟩ := hk; exact hat h1
    split at hk
    · obtain ⟨-, h2, rfl⟩ := hk; scalar_tac
    · obtain ⟨rfl, -⟩ := hk; cases h1
  apply WP.spec_mono (find_server_name_loop.spec b end' pos1 found1 at1 len1 (by scalar_tac) he hat1)
  intro r hr
  rw [show pos1.val = pos.val + 4 + n.val by scalar_tac] at hr
  split
  · rename_i hbad
    simp only [hbad, ↓reduceIte] at hr
    rw [hx, hr]; rfl
  rename_i hbad
  simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hr ⊢
  obtain ⟨exts', hex', hc⟩ := hr
  refine ⟨_, by rw [hx, hex']; rfl, ?_⟩
  cases found
  · simp only [Bool.false_eq_true, ↓reduceIte] at hk ⊢
    by_cases h0 : ty.val = 0
    · simp only [h0, ↓reduceIte] at hk
      obtain ⟨h1, h2, h3⟩ := hk
      rw [h1] at hc
      simp only [↓reduceIte] at hc
      obtain ⟨hr1, hr2, hr3⟩ := hc
      simp only [List.find?_cons, h0, decide_true]
      refine ⟨hr1, ?_, ?_⟩
      · rw [hr2, hr3]; scalar_tac
      · rw [hr2, hr3, h2, h3]
    · simp only [h0, ↓reduceIte] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      simp only [Bool.false_eq_true, ↓reduceIte] at hc
      simp only [List.find?_cons, h0, decide_false]
      exact hc
  · simp only [↓reduceIte] at hk ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hk
    simpa using hc
termination_by end'.val - pos.val
decreasing_by scalar_tac

/-- **Spec theorem for `find_server_name`**: the data of the first
    server_name extension among those filling `b[start..end]`. -/
@[step]
theorem find_server_name.spec (b : Slice U8) (start end' : Usize) (hs : start.val ≤ end'.val)
    (he : end'.val ≤ b.length) :
    find_server_name b start end' ⦃ (r : Option (Bool × Usize × Usize)) =>
      match r with
      | none => extsN (win b.val start.val end'.val) = none
      | some (found, at', len) => ∃ exts, extsN (win b.val start.val end'.val) = some exts ∧
          match exts.find? (fun x => x.1 = 0) with
          | none => found = false
          | some x => found = true ∧ at'.val + len.val ≤ end'.val ∧
              win b.val at'.val (at'.val + len.val) = x.2 ⦄ := by
  unfold find_server_name
  step with find_server_name_loop.spec b end' start false 0#usize 0#usize hs he (by simp)
    as ⟨found, at', len, bad, hr⟩
  cases bad
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok] at hr ⊢
    exact hr
  · simp only [↓reduceIte, WP.spec_ok] at hr ⊢
    exact hr

/-! ## Host names -/

theorem hostN_short (b : List U8) (at' len : Nat) (hl : len < 5) (he : at' + len ≤ b.length) :
    hostN (win b at' (at' + len)) = none := by
  have hw := win_length b at' (at' + len) he
  match h : win b at' (at' + len) with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => simp [hostN, vec16N]
  | [_, _, _, _] => simp [hostN, vec16N]
  | _ :: _ :: _ :: _ :: _ :: _ => rw [h] at hw; simp at hw; omega

theorem hostN_win (b : List U8) (at' len : Nat) (hl : 5 ≤ len) (he : at' + len ≤ b.length) :
    hostN (win b at' (at' + len)) =
      if be16N b at' = len - 2 ∧ b[at' + 2]!.val = 0 then
        if be16N b (at' + 3) ≤ len - 5 then
          some (win b (at' + 5) (at' + 5 + be16N b (at' + 3)))
        else none
      else none := by
  rw [win_cons b at' _ (by omega) he, win_cons b (at' + 1) _ (by omega) he,
    win_cons b (at' + 1 + 1) _ (by omega) he]
  simp only [hostN, win_length b _ _ he, show at' + 1 + 1 = at' + 2 from rfl,
    show at' + 2 + 1 = at' + 3 from rfl]
  rw [vec16N_win b (at' + 3) (at' + len) (by omega) he]
  unfold be16N
  by_cases hc : b[at']!.val * 256 + b[at' + 1]!.val = len - 2 ∧ b[at' + 2]!.val = 0
  · have e1 : len - 2 = at' + len - (at' + 3) + 1 := by omega
    have e2 : at' + len - (at' + 3) - 2 = len - 5 := by omega
    simp only [hc, e1, e2, and_self, ↓reduceIte, show at' + 3 + 1 = at' + 4 from rfl,
      show at' + 3 + 2 = at' + 5 from rfl]
    split <;> simp
  · have hc' : ¬ (b[at']!.val * 256 + b[at' + 1]!.val = at' + len - (at' + 3) + 1 ∧
        b[at' + 2]!.val = 0) := fun h => hc ⟨by omega, h.2⟩
    simp only [hc, hc', ↓reduceIte]

/-- **Spec theorem for `host_name`**: the host name in the server_name
    extension data `b[at..at + len]`, if it is valid. -/
@[step]
theorem host_name.spec (b : Slice U8) (at' len : Usize) (h : at'.val + len.val ≤ b.length) :
    host_name b at' len ⦃ (r : Option name.Name) =>
      match r with
      | none => ∀ hn, hostN (win b.val at'.val (at'.val + len.val)) = some hn →
          name.strip hn = [] ∨ 253 < (name.strip hn).length
      | some n => ∃ hn, hostN (win b.val at'.val (at'.val + len.val)) = some hn ∧
          name.strip hn ≠ [] ∧ (name.strip hn).length ≤ 253 ∧ n.Inv ∧
          n.text = ((name.strip hn).map (·.val)).map name.lowerN ⦄ := by
  unfold host_name
  have hb : at'.val + len.val ≤ b.val.length := h
  split
  · simp only [WP.spec_ok]
    intro hn hh
    rw [hostN_short _ _ _ (by scalar_tac) hb] at hh
    cases hh
  have hw := hostN_win b.val at'.val len.val (by scalar_tac) hb
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  split
  · simp only [WP.spec_ok]
    rename_i hne
    have hc : ¬ (be16N b.val at'.val = len.val - 2 ∧ b.val[at'.val + 2]!.val = 0) := by
      simp only [bne_iff_ne, ne_eq] at hne
      exact fun h => hne (by scalar_tac)
    simp only [hc, ↓reduceIte] at hw
    intro hn hh; rw [hw] at hh; cases hh
  step as ⟨i2, hi2⟩
  step as ⟨c, hc⟩
  have hcv : b.val[at'.val + 2]! = c := by
    rw [getElem!_pos b.val (at'.val + 2) (by scalar_tac), hc]; simp [hi2]
  split
  · simp only [WP.spec_ok]
    rename_i hne
    have hc : ¬ (be16N b.val at'.val = len.val - 2 ∧ b.val[at'.val + 2]!.val = 0) := by
      simp only [bne_iff_ne, ne_eq] at hne
      rw [hcv]; exact fun h => hne (by scalar_tac)
    simp only [hc, ↓reduceIte] at hw
    intro hn hh; rw [hw] at hh; cases hh
  rename_i hne1 hne2
  have hc1 : be16N b.val at'.val = len.val - 2 ∧ b.val[at'.val + 2]!.val = 0 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne1 hne2
    rw [hcv]; constructor <;> scalar_tac
  simp only [hc1, and_self, ↓reduceIte] at hw
  step as ⟨i4, hi4⟩
  step as ⟨n, hn⟩
  step as ⟨i5, hi5⟩
  split
  · simp only [WP.spec_ok]
    have hc : ¬ be16N b.val (at'.val + 3) ≤ len.val - 5 := by scalar_tac
    simp only [hc, ↓reduceIte] at hw
    intro hn hh; rw [hw] at hh; cases hh
  have hc : be16N b.val (at'.val + 3) ≤ len.val - 5 := by scalar_tac
  simp only [hc, ↓reduceIte] at hw
  step as ⟨i6, hi6⟩
  step as ⟨i7, hi7⟩
  step as ⟨s, hs, hsl⟩
  have hsv : s.val = win b.val (at'.val + 5) (at'.val + 5 + be16N b.val (at'.val + 3)) := by
    rw [hs]; simp only [List.slice, win]; congr 2; scalar_tac
  apply WP.spec_mono (name.Name.from_text.spec s)
  rintro (_ | nm) hres
  · intro hn hh
    rw [hw, Option.some.injEq] at hh
    rw [← hh, ← hsv]; exact hres
  · obtain ⟨hinv, hlen, htext⟩ := hres
    have hlt : (name.strip s.val).length = nm.len.val := by
      have := congrArg List.length htext
      simp only [name.Name.text, List.length_map, List.length_take] at this
      simp only [name.Name.Inv] at hinv
      simp at this; omega
    refine ⟨_, hw, ?_, ?_, hinv, ?_⟩
    · rw [← hsv]; intro h0; rw [h0] at hlt; simp at hlt; omega
    · rw [← hsv, hlt]; exact hinv
    · rw [← hsv]; exact htext

/-! ## The ClientHello -/

theorem win_all (r : List U8) : win r 0 r.length = r := by simp [win]

theorem fragmentN_short (r : List U8) (h : r.length < 5) : fragmentN r = none := by
  match r, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _, h => simp at h; omega

theorem fragmentN_eq (r : List U8) (h : 5 ≤ r.length) :
    fragmentN r =
      if r[0]!.val = 22 ∧ r[1]!.val = 3 ∧ r[2]!.val ≤ 4 ∧ be16N r 3 ≤ r.length - 5 then
        some (win r 5 (5 + be16N r 3))
      else none := by
  have hr := win_all r
  have hl := le_refl r.length
  conv_lhs => rw [← hr, win_cons r 0 _ (by omega) hl, win_cons r (0 + 1) _ (by omega) hl,
    win_cons r (0 + 1 + 1) _ (by omega) hl, win_cons r (0 + 1 + 1 + 1) _ (by omega) hl,
    win_cons r (0 + 1 + 1 + 1 + 1) _ (by omega) hl]
  simp only [fragmentN, win_length r _ _ hl, Nat.zero_add, show 1 + 1 = 2 from rfl,
    show 2 + 1 = 3 from rfl, show 3 + 1 = 4 from rfl, show 4 + 1 = 5 from rfl]
  unfold be16N
  simp only [show 3 + 1 = 4 from rfl]
  by_cases hc : r[0]!.val = 22 ∧ r[1]!.val = 3 ∧ r[2]!.val ≤ 4 ∧
      r[3]!.val * 256 + r[4]!.val ≤ r.length - 5
  · simp only [hc, and_self, ↓reduceIte]
    rw [win_take _ _ _ _ (by omega)]
  · simp only [hc, ↓reduceIte]

theorem bodyN_short (r : List U8) (re : Nat) (h5 : 5 ≤ re) (h9 : re < 9) (he : re ≤ r.length) :
    bodyN (win r 5 re) = none := by
  have hw := win_length r 5 re he
  match h : win r 5 re with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ => rw [h] at hw; simp at hw; omega

/-- The length of the ClientHello body. -/
def bodyLenN (r : List U8) : Nat := r[6]!.val * 65536 + r[7]!.val * 256 + r[8]!.val

theorem bodyN_eq (r : List U8) (re : Nat) (h9 : 9 ≤ re) (he : re ≤ r.length) :
    bodyN (win r 5 re) =
      if r[5]!.val = 1 ∧ bodyLenN r ≤ re - 9 then some (win r 9 (9 + bodyLenN r)) else none := by
  rw [win_cons r 5 _ (by omega) he, win_cons r (5 + 1) _ (by omega) he,
    win_cons r (5 + 1 + 1) _ (by omega) he, win_cons r (5 + 1 + 1 + 1) _ (by omega) he]
  simp only [bodyN, win_length r _ _ he]
  unfold bodyLenN
  change (if r[5]!.val = 1 ∧ r[6]!.val * 65536 + r[7]!.val * 256 + r[8]!.val ≤ re - 9 then
      some (List.take (r[6]!.val * 65536 + r[7]!.val * 256 + r[8]!.val) (win r 9 re)) else none) = _
  by_cases hc : r[5]!.val = 1 ∧ r[6]!.val * 65536 + r[7]!.val * 256 + r[8]!.val ≤ re - 9
  · simp only [hc, and_self, ↓reduceIte]
    rw [win_take _ _ _ _ (by omega)]
  · simp only [hc, ↓reduceIte]

theorem not_spec (r : List U8) (h : serverNameN r = none ∨ ∃ hn, serverNameN r = some (some hn) ∧
    (name.strip hn = [] ∨ 253 < (name.strip hn).length)) : ∀ c, ¬ ClientHello.Spec r c := by
  intro c hc
  unfold ClientHello.Spec at hc
  rcases h with h | ⟨hn, h, hb⟩
  · simp [h] at hc
  · cases hs : c.server_name with
    | none => simp [h, hs] at hc
    | some n =>
      simp only [h, hs] at hc
      obtain ⟨h1, h2, -⟩ := hc
      rcases hb with hb | hb
      · exact h1 hb
      · omega

theorem spec_none (r : List U8) (h : serverNameN r = some none) :
    ClientHello.Spec r { server_name := none } := by
  simp [ClientHello.Spec, h]

theorem spec_some (r : List U8) (hn : List U8) (n : name.Name) (h : serverNameN r = some (some hn))
    (h1 : name.strip hn ≠ []) (h2 : (name.strip hn).length ≤ 253) (h3 : n.Inv)
    (h4 : n.text = ((name.strip hn).map (·.val)).map name.lowerN) :
    ClientHello.Spec r { server_name := some n } := by
  simp only [ClientHello.Spec, h]
  exact ⟨h1, h2, h3, h4⟩

theorem bne_u8 {x y : U8} (h : (x != y) = true) : x.val ≠ y.val := by
  simp only [bne_iff_ne, ne_eq] at h; exact fun e => h (by scalar_tac)

/-- **Spec theorem for `<ClientHello as Validate<&[u8]>>::validate`**:
    accepts exactly the streams starting with a ClientHello with a valid
    server name or none. -/
@[step]
theorem ClientHello.Insts.UntrustedValidateShared0SliceU8ValidationError.validate.spec
    (r : Slice U8) :
    ClientHello.Insts.UntrustedValidateShared0SliceU8ValidationError.validate r
      ⦃ (res : core.result.Result ClientHello ValidationError) =>
        match res with
        | .Ok c => ClientHello.Spec r.val c
        | .Err _ => ∀ c, ¬ ClientHello.Spec r.val c ⦄ := by
  unfold ClientHello.Insts.UntrustedValidateShared0SliceU8ValidationError.validate
  dsimp only
  by_cases hc : r.len < RECORD_HEADER_LEN
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    exact not_spec _ (Or.inl (by simp only [serverNameN, fragmentN_short r.val (by scalar_tac)]))
  rw [if_neg hc]
  have h5 : 5 ≤ r.val.length := by scalar_tac
  have hfr := fragmentN_eq r.val h5
  -- The record header.
  step as ⟨i1, hi1⟩
  have e0 : r.val[0]!.val = i1.val := by rw [getElem!_pos r.val 0 (by omega), hi1]
  by_cases hc : (i1 != CONTENT_HANDSHAKE) = true
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    have := bne_u8 hc
    refine not_spec _ (Or.inl ?_)
    have hc : ¬ (r.val[0]!.val = 22 ∧ r.val[1]!.val = 3 ∧ r.val[2]!.val ≤ 4 ∧
        be16N r.val 3 ≤ r.val.length - 5) := fun h => this (by simpa [← e0] using h.1)
    simp only [serverNameN, hfr, hc, ↓reduceIte]
  rw [if_neg hc]
  have c0 : r.val[0]!.val = 22 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc; rw [e0, hc]; simp
  step as ⟨i2, hi2⟩
  have e1 : r.val[1]!.val = i2.val := by rw [getElem!_pos r.val 1 (by omega), hi2]
  by_cases hc : (i2 != 3#u8) = true
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    have := bne_u8 hc
    refine not_spec _ (Or.inl ?_)
    have hc : ¬ (r.val[0]!.val = 22 ∧ r.val[1]!.val = 3 ∧ r.val[2]!.val ≤ 4 ∧
        be16N r.val 3 ≤ r.val.length - 5) := fun h => this (by simpa [← e1] using h.2.1)
    simp only [serverNameN, hfr, hc, ↓reduceIte]
  rw [if_neg hc]
  have c1 : r.val[1]!.val = 3 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc; rw [e1, hc]; rfl
  step as ⟨i3, hi3⟩
  have e2 : r.val[2]!.val = i3.val := by rw [getElem!_pos r.val 2 (by omega), hi3]
  by_cases hc : i3 > 4#u8
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    have hc : ¬ (r.val[0]!.val = 22 ∧ r.val[1]!.val = 3 ∧ r.val[2]!.val ≤ 4 ∧
        be16N r.val 3 ≤ r.val.length - 5) := fun h => by scalar_tac
    simp only [serverNameN, hfr, hc, ↓reduceIte]
  rw [if_neg hc]
  have c2 : r.val[2]!.val ≤ 4 := by scalar_tac
  step as ⟨fl, hfl⟩
  step as ⟨i5, hi5⟩
  by_cases hc : fl > i5
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    have hc : ¬ (r.val[0]!.val = 22 ∧ r.val[1]!.val = 3 ∧ r.val[2]!.val ≤ 4 ∧
        be16N r.val 3 ≤ r.val.length - 5) := fun h => by scalar_tac
    simp only [serverNameN, hfr, hc, ↓reduceIte]
  rw [if_neg hc]
  step as ⟨re, hre⟩
  have hfr' : fragmentN r.val = some (win r.val 5 re.val) := by
    have hc : r.val[0]!.val = 22 ∧ r.val[1]!.val = 3 ∧ r.val[2]!.val ≤ 4 ∧
        be16N r.val 3 ≤ r.val.length - 5 := ⟨c0, c1, c2, by scalar_tac⟩
    simp only [hfr, hc, and_self, ↓reduceIte]
    congr 2; scalar_tac
  clear hfr
  have hre' : re.val ≤ r.val.length := by scalar_tac
  -- The handshake header.
  by_cases hc : fl < HANDSHAKE_HEADER_LEN
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    simp only [serverNameN, hfr', bodyN_short r.val re.val (by scalar_tac) (by scalar_tac) hre']
  rw [if_neg hc]
  have hbd := bodyN_eq r.val re.val (by scalar_tac) hre'
  step as ⟨i6, hi6⟩
  have e5 : r.val[5]!.val = i6.val := by rw [getElem!_pos r.val 5 (by scalar_tac), hi6]; simp
  by_cases hc : (i6 != CLIENT_HELLO) = true
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    have := bne_u8 hc
    refine not_spec _ (Or.inl ?_)
    have hc : ¬ (r.val[5]!.val = 1 ∧ bodyLenN r.val ≤ re.val - 9) := 
      fun h => this (by simpa [← e5] using h.1)
    simp only [serverNameN, hfr', hbd, hc, ↓reduceIte]
  rw [if_neg hc]
  have c5 : r.val[5]!.val = 1 := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc; rw [e5, hc]; simp
  step as ⟨body, hbody⟩
  step as ⟨i7, hi7⟩
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  step as ⟨i10, hi10⟩
  step as ⟨i11, hi11⟩
  step as ⟨i12, hi12⟩
  have := be16N_lt r.val 7
  step as ⟨bl, hbl⟩
  have hb9 : body.val ≤ re.val := by scalar_tac
  step as ⟨i13, hi13⟩
  have hL : bl.val = bodyLenN r.val := by
    have e6 : r.val[6]!.val = i8.val := by
      rw [getElem!_pos r.val 6 (by scalar_tac), hi8]; simp [hi7]
    have h9 : i9.val = i8.val := by rw [hi9]; simp
    have h11 : i11.val = 7 := by scalar_tac
    unfold bodyLenN
    rw [hbl, hi10, hi12, h9, h11, ← e6]
    unfold be16N; simp only [Nat.reduceAdd]; omega
  by_cases hc : bl > i13
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    have hc : ¬ (r.val[5]!.val = 1 ∧ bodyLenN r.val ≤ re.val - 9) := fun h => by scalar_tac
    simp only [serverNameN, hfr', hbd, hc, ↓reduceIte]
  rw [if_neg hc]
  step as ⟨e, he⟩
  have hsn : serverNameN r.val = helloN (win r.val 9 e.val) := by
    have hc : r.val[5]!.val = 1 ∧ bodyLenN r.val ≤ re.val - 9 := ⟨c5, by scalar_tac⟩
    simp only [serverNameN, hfr', hbd, hc, and_self, ↓reduceIte]
    congr 2; scalar_tac
  have he' : e.val ≤ r.val.length := by scalar_tac
  -- The ClientHello.
  by_cases hc : bl < VERSION_RANDOM_LEN
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    rw [hsn, helloN, win_length _ _ _ he']
    simp only [show e.val - 9 < 34 by scalar_tac, ↓reduceIte]
  rw [if_neg hc]
  have hsn2 : serverNameN r.val = afterRandomN (win r.val 43 e.val) := by
    rw [hsn, helloN, win_length _ _ _ he', win_drop _ _ _ _ (by scalar_tac)]
    simp only [show ¬ e.val - 9 < 34 by scalar_tac, ↓reduceIte]
  clear hbd hsn
  -- Session ID, cipher suites, compression methods.
  step as ⟨sid, hsid⟩
  have hsid' : sid.val = 43 := by scalar_tac
  step as ⟨o, ho⟩
  rw [hsid'] at ho
  rcases o with _ | p
  · dsimp only
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    simp only [hsn2, afterRandomN, ho]
  obtain ⟨hp1, hp2, hv1⟩ := ho
  dsimp only
  step as ⟨o1, ho1⟩
  rcases o1 with _ | p1
  · dsimp only
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    simp only [hsn2, afterRandomN, hv1, ho1]
  obtain ⟨hq1, hq2, hv2⟩ := ho1
  dsimp only
  step as ⟨o2, ho2⟩
  rcases o2 with _ | p2
  · dsimp only
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    simp only [hsn2, afterRandomN, hv1, hv2, ho2]
  obtain ⟨hr1, hr2, hv3⟩ := ho2
  dsimp only
  have hsn3 : serverNameN r.val = extensionsN (win r.val p2.val e.val) := by
    simp only [hsn2, afterRandomN, hv1, hv2, hv3]
  clear hsn2
  -- No extensions.
  by_cases hc : p2 = e
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    apply spec_none
    rw [hsn3, hc, win_nil]
    simp [extensionsN]
  rw [if_neg hc]
  have hlt : p2.val < e.val := by scalar_tac
  have hne : win r.val p2.val e.val ≠ [] := by
    intro h; have := win_length r.val p2.val e.val he'; rw [h] at this; simp at this; omega
  -- The extensions.
  step as ⟨o3, ho3⟩
  rcases o3 with _ | p3
  · dsimp only
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    simp only [hsn3, extensionsN, hne, ↓reduceIte, ho3]
  obtain ⟨hs1, hs2, hv4⟩ := ho3
  dsimp only
  by_cases hc : (p3 != e) = true
  · rw [if_pos hc]
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    have hne3 : win r.val p3.val e.val ≠ [] := by
      have : p3.val ≠ e.val := by simp only [bne_iff_ne, ne_eq] at hc; exact fun h => hc (by scalar_tac)
      intro h; have := win_length r.val p3.val e.val he'; rw [h] at this; simp at this; omega
    simp only [hsn3, extensionsN, hne, ↓reduceIte, hv4, ne_eq, hne3, not_false_eq_true]
  rw [if_neg hc]
  have hp3 : p3.val = e.val := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc; rw [hc]
  step as ⟨i14, hi14⟩
  step as ⟨o4, ho4⟩
  rw [show i14.val = p2.val + 2 by scalar_tac] at ho4
  have hsn4 : serverNameN r.val = match extsN (win r.val (p2.val + 2) e.val) with
      | none => none
      | some exts => match exts.find? (fun x => x.1 = 0) with
        | none => some none
        | some x => (hostN x.2).map some := by
    simp only [hsn3, extensionsN, hne, ↓reduceIte, hv4, hp3, win_nil, ne_eq, not_true_eq_false]
  clear hsn3
  rcases o4 with _ | ⟨found, at', len⟩
  · dsimp only
    simp only [WP.spec_ok]
    refine not_spec _ (Or.inl ?_)
    simp only [hsn4, ho4]
  obtain ⟨exts, hex, hfind⟩ := ho4
  dsimp only
  rw [hex] at hsn4
  dsimp only at hsn4
  have key : (found = false ∧ serverNameN r.val = some none) ∨
      (found = true ∧ at'.val + len.val ≤ r.val.length ∧
        serverNameN r.val = (hostN (win r.val at'.val (at'.val + len.val))).map some) := by
    cases hx : exts.find? (fun x => x.1 = 0) with
    | none =>
      simp only [hx] at hfind hsn4
      exact Or.inl ⟨hfind, hsn4⟩
    | some x =>
      simp only [hx] at hfind hsn4
      obtain ⟨h1, h2, h3⟩ := hfind
      exact Or.inr ⟨h1, by scalar_tac, by rw [hsn4, h3]⟩
  clear hfind hsn4
  step*
  · rcases key with ⟨hf, -⟩ | ⟨-, -, hs⟩
    · exact absurd ‹found = true› (by rw [hf]; simp)
    · subst_vars
      refine not_spec _ ?_
      cases hh : hostN (win r.val at'.val (at'.val + len.val)) with
      | none => left; rw [hs, hh]; rfl
      | some hn => right; exact ⟨hn, by rw [hs, hh]; rfl, o5_post hn hh⟩
  · rcases key with ⟨hf, -⟩ | ⟨-, -, hs⟩
    · exact absurd ‹found = true› (by rw [hf]; simp)
    · subst_vars
      obtain ⟨hn, hh, h1, h2, h3, h4⟩ := o5_post
      exact spec_some _ hn _ (by rw [hs, hh]; rfl) h1 h2 h3 h4
  · rcases key with ⟨-, hs⟩ | ⟨hf, -⟩
    · exact spec_none _ hs
    · exact absurd hf (by simp_all)

end adfilter.tls
