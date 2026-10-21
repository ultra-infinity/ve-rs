/- Specs of `wireguard::device`: the sans-IO device.

   `Device.Inv` is the invariant every entry point keeps: each keypair's
   replay window means some set of counters, the routing table is
   well-formed, and the local indices of live sessions and handshakes are
   distinct. Given it, the entry points never fail, and:
   - a transport message is sent only under a keypair that may send (younger
     than `REJECT_AFTER_TIME`, counter below `REJECT_AFTER_MESSAGES`), with its
     counter, which then goes up by one;
   - an initiation is sent to a peer only `REKEY_TIMEOUT` after the previous
     one;
   - a packet is delivered only if it is authentic under a keypair that may
     receive, its counter is fresh for that keypair's replay window (and is
     then recorded), and it is an IP packet whose source routes back to the
     peer. -/
import Wireguard.TransportTop
import Wireguard.CookieTop

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace wireguard.device
open wireguard.crypto wireguard.transport

/-! ## Constants -/

@[simp, scalar_tac_simps] theorem MAX_PEERS_val : MAX_PEERS.val = 512 := by simp [MAX_PEERS]
@[simp, scalar_tac_simps] theorem MAX_PACKET_LEN_val : MAX_PACKET_LEN.val = 65535 := by
  simp [MAX_PACKET_LEN]
@[simp, scalar_tac_simps] theorem REKEY_AFTER_MESSAGES_val :
    REKEY_AFTER_MESSAGES.val = 1152921504606846976 := by simp [REKEY_AFTER_MESSAGES]
@[simp, scalar_tac_simps] theorem REKEY_AFTER_TIME_val : REKEY_AFTER_TIME.val = 120000000000 := by
  simp [REKEY_AFTER_TIME]
@[simp, scalar_tac_simps] theorem REJECT_AFTER_TIME_val :
    REJECT_AFTER_TIME.val = 180000000000 := by simp [REJECT_AFTER_TIME]
@[simp, scalar_tac_simps] theorem ERASE_AFTER_TIME_val : ERASE_AFTER_TIME.val = 540000000000 := by
  simp [ERASE_AFTER_TIME]
@[simp, scalar_tac_simps] theorem REKEY_ATTEMPT_TIME_val :
    REKEY_ATTEMPT_TIME.val = 90000000000 := by simp [REKEY_ATTEMPT_TIME]
@[simp, scalar_tac_simps] theorem REKEY_TIMEOUT_val : REKEY_TIMEOUT.val = 5000000000 := by
  simp [REKEY_TIMEOUT]
@[simp, scalar_tac_simps] theorem KEEPALIVE_TIMEOUT_val :
    KEEPALIVE_TIMEOUT.val = 10000000000 := by simp [KEEPALIVE_TIMEOUT]
@[simp, scalar_tac_simps] theorem COOKIE_SECRET_MAX_AGE_val :
    COOKIE_SECRET_MAX_AGE.val = 120000000000 := by simp [COOKIE_SECRET_MAX_AGE]
@[simp, scalar_tac_simps] theorem COOKIE_MAX_AGE_val : COOKIE_MAX_AGE.val = 115000000000 := by
  simp [COOKIE_MAX_AGE]
@[simp, scalar_tac_simps] theorem REJECT_AFTER_MESSAGES_val :
    replay.REJECT_AFTER_MESSAGES.val = replay.REJECT := by
  simp [replay.REJECT_AFTER_MESSAGES, replay.REJECT]

/-! ## Small functions -/

/-- **Spec theorem for `elapsed`**: `now - since`, truncated at 0. -/
@[step]
theorem elapsed.spec (since now : U64) :
    elapsed since now ⦃ (r : U64) => r.val = now.val - since.val ⦄ := by
  unfold elapsed
  split
  · step*
  · simp only [WP.spec_ok]; scalar_tac

/-- **Spec theorem for `keys_equal`'s loop**. -/
@[step]
theorem keys_equal_loop.spec (a b : Array U8 32#usize) (equal : Bool) (i : Usize)
    (hi : i.val ≤ 32) :
    keys_equal_loop a b equal i ⦃ (r : Bool) =>
      r = (equal && decide (a.val.drop i.val = b.val.drop i.val)) ⦄ := by
  unfold keys_equal_loop
  split
  · have hla : i.val < a.val.length := by simp; scalar_tac
    have hlb : i.val < b.val.length := by simp; scalar_tac
    step as ⟨x, hx⟩
    step as ⟨y, hy⟩
    have hda : a.val.drop i.val = x :: a.val.drop (i.val + 1) := by
      rw [hx]; exact List.drop_eq_getElem_cons hla
    have hdb : b.val.drop i.val = y :: b.val.drop (i.val + 1) := by
      rw [hy]; exact List.drop_eq_getElem_cons hlb
    by_cases hxy : x = y
    · simp only [hxy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_tc_ok]
      step as ⟨i3, hi3⟩
      step as ⟨r, hr⟩
      rw [hr, hi3, hda, hdb, hxy]; simp
    · have hne : (x != y) = true := by simpa using hxy
      simp only [hne, ↓reduceIte, bind_tc_ok]
      step as ⟨i3, hi3⟩
      step as ⟨r, hr⟩
      rw [hr, hda, hdb]; simp [hxy]
  · simp only [WP.spec_ok]
    have : i.val = 32 := by scalar_tac
    simp [this]
termination_by 32 - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `keys_equal`**. -/
@[step]
theorem keys_equal.spec (a b : Array U8 32#usize) :
    keys_equal a b ⦃ (r : Bool) => r = decide (a = b) ⦄ := by
  unfold keys_equal
  apply WP.spec_mono (keys_equal_loop.spec a b true 0#usize (by simp))
  intro r hr
  simp [hr, Array.eq_iff]

/-! ## Keypairs and slots -/

deriving instance Inhabited for replay.Replay, noise.Chain, noise.InitiatorState, Endpoint,
  Keypair, Handshake, Peer

/-- `kp` may receive at `now`: valid, and younger than `REJECT_AFTER_TIME`. -/
def CanRecv (kp : Keypair) (now : Nat) : Prop :=
  kp.valid = true ∧ kp.created.val ≤ now ∧ now - kp.created.val < 180000000000

/-- `kp` may send at `now`: it may receive, and its counter is below
    `REJECT_AFTER_MESSAGES`. -/
def CanSend (kp : Keypair) (now : Nat) : Prop :=
  CanRecv kp now ∧ kp.counter.val < replay.REJECT

instance (kp : Keypair) (now : Nat) : Decidable (CanRecv kp now) := by
  unfold CanRecv; infer_instance
instance (kp : Keypair) (now : Nat) : Decidable (CanSend kp now) := by
  unfold CanSend; infer_instance

/-- **Spec theorem for `can_receive`**. -/
@[step]
theorem can_receive.spec (kp : Keypair) (now : U64) :
    can_receive kp now ⦃ (r : Bool) => r = decide (CanRecv kp now.val) ⦄ := by
  unfold can_receive CanRecv
  split
  · split
    · step*
    · simp only [WP.spec_ok]
      simp_all [UScalar.le_equiv]
  · simp_all

/-- **Spec theorem for `can_send`**. -/
@[step]
theorem can_send.spec (kp : Keypair) (now : U64) :
    can_send kp now ⦃ (r : Bool) => r = decide (CanSend kp now.val) ⦄ := by
  unfold can_send CanSend
  step*

/-- The keypair of `p` in slot `s`: current (0), previous (1) or next. -/
def kpAt (p : Peer) (s : Nat) : Keypair :=
  if s = 0 then p.current else if s = 1 then p.previous else p.next

/-- `p` with `kp` in slot `s`. -/
def setKpAt (p : Peer) (s : Nat) (kp : Keypair) : Peer :=
  if s = 0 then { p with current := kp } else if s = 1 then { p with previous := kp }
  else { p with next := kp }

/-- The slot of `p`'s valid keypair with local index `x`, or 3. -/
def slotOf (p : Peer) (x : U32) : Nat :=
  if p.current.valid ∧ p.current.local_index = x then 0
  else if p.previous.valid ∧ p.previous.local_index = x then 1
  else if p.next.valid ∧ p.next.local_index = x then 2 else 3

theorem slotOf_le (p : Peer) (x : U32) : slotOf p x ≤ 3 := by
  unfold slotOf; split_ifs <;> omega

theorem slotOf_found {p : Peer} {x : U32} (h : slotOf p x ≠ 3) :
    (kpAt p (slotOf p x)).valid = true ∧ (kpAt p (slotOf p x)).local_index = x := by
  unfold slotOf at *
  split_ifs at * with h0 h1 h2 <;> simp_all [kpAt]

/-- **Spec theorem for `session_slot`**. -/
@[step]
theorem session_slot.spec (p : Peer) (x : U32) :
    session_slot p x ⦃ (r : U8) => r.val = slotOf p x ⦄ := by
  unfold session_slot slotOf
  split_ifs <;> simp_all

/-- **Spec theorem for `keypair`**. -/
@[step]
theorem keypair.spec (p : Peer) (s : U8) :
    keypair p s ⦃ (r : Keypair) => r = kpAt p s.val ⦄ := by
  unfold keypair kpAt
  split_ifs <;> simp_all

/-- **Spec theorem for `set_keypair`**. -/
@[step]
theorem set_keypair.spec (p : Peer) (s : U8) (kp : Keypair) :
    set_keypair p s kp ⦃ (r : Peer) => r = setKpAt p s.val kp ⦄ := by
  unfold set_keypair setKpAt
  split_ifs <;> simp_all

/-- The four places a local index lives in a peer. -/
inductive Slot | hs | cur | prev | next
  deriving DecidableEq

/-- The local index in slot `s` of `p`, if it is in use. -/
def Peer.idx (p : Peer) : Slot → Option U32
  | .hs => if p.handshake.active then some p.handshake.local_index else none
  | .cur => if p.current.valid then some p.current.local_index else none
  | .prev => if p.previous.valid then some p.previous.local_index else none
  | .next => if p.next.valid then some p.next.local_index else none

/-- `p` uses the local index `x`. -/
def Uses (p : Peer) (x : U32) : Prop := ∃ s, p.idx s = some x

theorem uses_iff (p : Peer) (x : U32) :
    Uses p x ↔ slotOf p x ≠ 3 ∨ (p.handshake.active = true ∧ p.handshake.local_index = x) := by
  unfold Uses slotOf
  constructor
  · rintro ⟨s, hs⟩
    cases s <;> simp [Peer.idx] at hs <;> split_ifs <;> simp_all
  · intro h
    split_ifs at h with h0 h1 h2
    · exact ⟨.cur, by simp [Peer.idx, h0.1, h0.2]⟩
    · exact ⟨.prev, by simp [Peer.idx, h1.1, h1.2]⟩
    · exact ⟨.next, by simp [Peer.idx, h2.1, h2.2]⟩
    · obtain h | ⟨ha, hx⟩ := h
      · exact absurd rfl h
      · exact ⟨.hs, by simp [Peer.idx, ha, hx]⟩

/-- **Spec theorem for `uses_index`**. -/
@[step]
theorem uses_index.spec (p : Peer) (x : U32) :
    uses_index p x ⦃ (r : Bool) => (r = true ↔ Uses p x) ⦄ := by
  unfold uses_index
  step as ⟨s, hs⟩
  rw [uses_iff]
  split
  · rename_i h
    simp only [WP.spec_ok, true_iff]
    left; intro h3; rw [← hs] at h3; simp_all
  · rename_i h
    have h3 : slotOf p x = 3 := by rw [← hs]; simpa using h
    split <;> simp_all

/-! ## Invariants of peers -/

/-- The replay window of `kp` means some set of counters. -/
def KpInv (kp : Keypair) : Prop := ∃ S, kp.replay.Inv S

/-- The replay windows of `p`'s keypairs mean sets of counters. -/
def Peer.Inv (p : Peer) : Prop := KpInv p.current ∧ KpInv p.previous ∧ KpInv p.next

/-- The local indices `p'` uses are ones `p` uses, in the same slots. -/
def SubIdx (p p' : Peer) : Prop := ∀ s x, p'.idx s = some x → p.idx s = some x

theorem SubIdx.refl (p : Peer) : SubIdx p p := fun _ _ h => h

theorem SubIdx.trans {p q r : Peer} (h1 : SubIdx p q) (h2 : SubIdx q r) : SubIdx p r :=
  fun s x h => h1 s x (h2 s x h)

/-- `kp'` is `kp`, or an invalid keypair with an empty-meaning window. -/
def KeepOrEmpty (kp kp' : Keypair) : Prop := kp' = kp ∨ (kp'.valid = false ∧ KpInv kp')

/-- **Spec theorem for `Keypair::empty`**. -/
@[step]
theorem Keypair.empty.spec : Keypair.empty ⦃ (kp : Keypair) => kp.valid = false ∧ KpInv kp ⦄ := by
  unfold Keypair.empty
  step*
  exact ⟨_, r_post⟩

/-- **Spec theorem for `expired`**. -/
@[step]
theorem expired.spec (kp : Keypair) (now : U64) :
    expired kp now ⦃ (r : Bool) =>
      r = (kp.valid && decide (540000000000 ≤ now.val - kp.created.val)) ⦄ := by
  unfold expired
  split
  · step*
  · simp_all

theorem keep_or_empty_step (b : Bool) (k : Keypair) :
    (if b then Keypair.empty else ok k) ⦃ (k' : Keypair) => KeepOrEmpty k k' ⦄ := by
  split
  · apply WP.spec_mono Keypair.empty.spec
    intro r hr; exact Or.inr hr
  · simp [KeepOrEmpty]

/-- **Spec theorem for `erase_old`**: each keypair is kept or erased. -/
@[step]
theorem erase_old.spec (p : Peer) (now : U64) :
    erase_old p now ⦃ (p' : Peer) => ∃ k0 k1 k2,
      p' = { p with current := k0, previous := k1, next := k2 } ∧
      KeepOrEmpty p.current k0 ∧ KeepOrEmpty p.previous k1 ∧ KeepOrEmpty p.next k2 ⦄ := by
  unfold erase_old
  step as ⟨b0, hb0⟩
  step with keep_or_empty_step b0 p.current as ⟨k0, hk0⟩
  step as ⟨b1, hb1⟩
  step with keep_or_empty_step b1 p.previous as ⟨k1, hk1⟩
  step as ⟨b2, hb2⟩
  split
  · step as ⟨k2, hk2, hk2'⟩
    exact ⟨k0, k1, k2, rfl, hk0, hk1, Or.inr ⟨hk2, hk2'⟩⟩
  · simp only [WP.spec_ok]
    exact ⟨k0, k1, p.next, rfl, hk0, hk1, Or.inl rfl⟩

theorem KeepOrEmpty.inv {kp kp' : Keypair} (h : KeepOrEmpty kp kp') (hi : KpInv kp) : KpInv kp' := by
  rcases h with rfl | ⟨-, h⟩ <;> assumption

theorem KeepOrEmpty.idx {kp kp' : Keypair} (h : KeepOrEmpty kp kp') {x : U32}
    (hx : (if kp'.valid then some kp'.local_index else none) = some x) :
    (if kp.valid then some kp.local_index else none) = some x := by
  rcases h with rfl | ⟨hv, -⟩
  · exact hx
  · simp [hv] at hx

theorem erase_sub {p : Peer} {k0 k1 k2 : Keypair} (h0 : KeepOrEmpty p.current k0)
    (h1 : KeepOrEmpty p.previous k1) (h2 : KeepOrEmpty p.next k2) :
    SubIdx p { p with current := k0, previous := k1, next := k2 } := by
  intro s x hx
  cases s
  · exact hx
  · exact h0.idx hx
  · exact h1.idx hx
  · exact h2.idx hx

theorem erase_inv {p : Peer} {k0 k1 k2 : Keypair} (h0 : KeepOrEmpty p.current k0)
    (h1 : KeepOrEmpty p.previous k1) (h2 : KeepOrEmpty p.next k2) (hp : p.Inv) :
    Peer.Inv { p with current := k0, previous := k1, next := k2 } :=
  ⟨h0.inv hp.1, h1.inv hp.2.1, h2.inv hp.2.2⟩

/-- **Spec theorem for `initiation_too_soon`**. -/
@[step]
theorem initiation_too_soon.spec (p : Peer) (now : U64) :
    initiation_too_soon p now ⦃ (r : Bool) =>
      r = (p.has_initiation && decide (now.val - p.initiation_at.val < 5000000000)) ⦄ := by
  unfold initiation_too_soon
  split
  · step*
  · simp_all

/-- **Spec theorem for `wants_rekey`**. -/
@[step]
theorem wants_rekey.spec (kp : Keypair) (now : U64) :
    wants_rekey kp now ⦃ (r : Bool) =>
      r = (decide (1152921504606846976 ≤ kp.counter.val) ||
        (kp.initiator && decide (120000000000 ≤ now.val - kp.created.val))) ⦄ := by
  unfold wants_rekey
  split
  · simp_all [UScalar.le_equiv]
  · split
    · step*
    · simp_all [UScalar.le_equiv]

/-- `p` with its handshake given up. -/
def giveUp (p : Peer) : Peer :=
  { p with handshake := { p.handshake with active := false }, rekey_wanted := false }

theorem giveUp_sub (p : Peer) : SubIdx p (giveUp p) := by
  intro s x hx; cases s <;> simp only [Peer.idx, giveUp] at hx ⊢ <;> first | exact hx | simp at hx

theorem noKeepalive_sub (p : Peer) : SubIdx p { p with keepalive_due := false } :=
  fun _ _ hx => hx

/-- **Spec theorem for `handshake_timer`**: the peer is unchanged, or its
    handshake is given up. -/
@[step]
theorem handshake_timer.spec (p : Peer) (now : U64) :
    handshake_timer p now ⦃ (b : Bool) (p' : Peer) =>
      p' = p ∨ p' = giveUp p ⦄ := by
  unfold handshake_timer giveUp
  split
  · step as ⟨i, hi⟩
    split
    · simp
    · step as ⟨i1, hi1⟩
      split <;> simp
  · simp

/-- **Spec theorem for `keepalive_timer`**: the peer is unchanged, or a
    keepalive is no longer due. -/
@[step]
theorem keepalive_timer.spec (p : Peer) (now : U64) :
    keepalive_timer p now ⦃ (b : Bool) (p' : Peer) =>
      p' = p ∨ p' = { p with keepalive_due := false } ⦄ := by
  unfold keepalive_timer
  split
  · step as ⟨i, hi⟩
    split
    · step as ⟨b, hb⟩
      split
      · simp
      · split
        · step*
        · simp
    · split
      · step*
      · simp
  · split
    · step*
    · simp

/-- What the timers keep of a peer: its keys, its initiation time, and its
    current keypair unless erased. -/
def TimersKeep (p p' : Peer) : Prop :=
  p'.initiation_at = p.initiation_at ∧ p'.has_initiation = p.has_initiation ∧
    p'.public = p.public ∧ p'.mac1_key = p.mac1_key ∧ KeepOrEmpty p.current p'.current

/-- **Spec theorem for `timers`**: what the timers ask for, and a peer with
    possibly fewer sessions and handshakes, and otherwise the same. -/
@[step]
theorem timers.spec (p : Peer) (now : U64) :
    timers p now ⦃ (t : U8) (p' : Peer) =>
      t.val ≤ 2 ∧ SubIdx p p' ∧ (p.Inv → p'.Inv) ∧ TimersKeep p p' ⦄ := by
  unfold timers
  step as ⟨q, k0, k1, k2, hq, h0, h1, h2⟩
  have hsub : SubIdx p q := hq ▸ erase_sub h0 h1 h2
  have hinv : p.Inv → q.Inv := fun hp => hq ▸ erase_inv h0 h1 h2 hp
  have hkeep : TimersKeep p q := by rw [hq]; exact ⟨rfl, rfl, rfl, rfl, h0⟩
  step as ⟨b, q2, hq2⟩
  have hsub2 : SubIdx p q2 := by
    rcases hq2 with h | h <;> rw [h]
    · exact hsub
    · exact SubIdx.trans hsub (giveUp_sub q)
  have hinv2 : p.Inv → q2.Inv := by
    rcases hq2 with h | h <;> rw [h]
    · exact hinv
    · exact hinv
  have hkeep2 : TimersKeep p q2 := by
    rcases hq2 with h | h <;> rw [h]
    · exact hkeep
    · exact hkeep
  split
  · simp only [WP.spec_ok]
    exact ⟨by simp, hsub2, hinv2, hkeep2⟩
  step as ⟨b1, q3, hq3⟩
  have hsub3 : SubIdx p q3 := by
    rcases hq3 with h | h <;> rw [h]
    · exact hsub2
    · exact SubIdx.trans hsub2 (noKeepalive_sub q2)
  have hinv3 : p.Inv → q3.Inv := by
    rcases hq3 with h | h <;> rw [h]
    · exact hinv2
    · exact hinv2
  have hkeep3 : TimersKeep p q3 := by
    rcases hq3 with h | h <;> rw [h]
    · exact hkeep2
    · exact hkeep2
  split
  · simp only [WP.spec_ok]
    exact ⟨by simp, hsub3, hinv3, hkeep3⟩
  · simp only [WP.spec_ok]
    exact ⟨by simp, hsub3, hinv3, hkeep3⟩

/-! ## Copying, endpoints and empty values -/

/-- **Spec theorem for `copy_out`'s loop**. -/
@[step]
theorem copy_out_loop.spec (out src : Slice U8) (i : Usize) (h : src.length ≤ out.length)
    (hi : i.val ≤ src.length) :
    copy_out_loop out src i ⦃ (out' : Slice U8) =>
      out'.val = out.val.take i.val ++ src.val.drop i.val ++ out.val.drop src.length ⦄ := by
  unfold copy_out_loop
  dsimp only
  split
  · step*
    rw [out'_post, s_post, Slice.set_val_eq, i3_post, i2_post]
    exact copy_step out.val src.val i.val src.length _ (by scalar_tac) (by scalar_tac) rfl
      (getElem!_pos src.val i.val (by scalar_tac)).symm
  · simp only [WP.spec_ok]
    have : i.val = src.length := by scalar_tac
    rw [this, copy_done _ _ _ rfl]
termination_by src.length - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `copy_out`**: copies `src` to the start of `out` if it
    fits. -/
@[step]
theorem copy_out.spec (out src : Slice U8) :
    copy_out out src ⦃ (b : Bool) (out' : Slice U8) =>
      out'.length = out.length ∧ (b = true ↔ src.length ≤ out.length) ∧
        (b = true → out'.val = src.val ++ out.val.drop src.length) ⦄ := by
  unfold copy_out
  dsimp only
  split
  · simp only [WP.spec_ok, WP.uncurry']
    simp; scalar_tac
  · step*
    have hl : out1.val = src.val ++ out.val.drop src.length := by simpa using out1_post
    refine ⟨?_, by scalar_tac, fun _ => hl⟩
    simp only [Slice.length, hl, List.length_append, List.length_drop]
    scalar_tac

/-- One step of a copying loop writing `src` at offset `o`. -/
theorem copy_step_at (work src : List U8) (o i p : Nat) (v : U8) (hi : i < p)
    (hp : o + p ≤ work.length) (hsrc : src.length = p) (hv : v = src[i]!) :
    (work.set (o + i) v).take (o + i + 1) ++ src.drop (i + 1) ++ (work.set (o + i) v).drop (o + p) =
      work.take (o + i) ++ src.drop i ++ work.drop (o + p) := by
  have hd : src.drop i = src[i] :: src.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
  rw [untrusted.take_set_succ _ _ _ (by omega), List.drop_set_of_lt (by omega), hd, hv,
    getElem!_pos _ _ (by omega)]
  simp

/-- **Spec theorem for `Endpoint::cookie_bytes`'s loop**. -/
@[step]
theorem Endpoint.cookie_bytes_loop.spec (a : Array U8 16#usize) (out : Array U8 19#usize)
    (i : Usize) (hi : i.val ≤ 16) :
    Endpoint.cookie_bytes_loop a out i ⦃ (out' : Array U8 19#usize) =>
      out'.val = out.val.take (1 + i.val) ++ a.val.drop i.val ++ out.val.drop 17 ⦄ := by
  unfold Endpoint.cookie_bytes_loop
  split
  · step*
    rw [out'_post, a1_post, Array.set_val_eq, i3_post, i2_post, i1_post,
      show 1 + (i.val + 1) = 1 + i.val + 1 by omega, show (17 : Nat) = 1 + 16 from rfl]
    exact copy_step_at out.val a.val 1 i.val 16 _ (by scalar_tac) (by simp) (by simp)
      (getElem!_pos a.val i.val (by simp; scalar_tac)).symm
  · simp only [WP.spec_ok]
    have : i.val = 16 := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp), List.append_nil, List.take_append_drop]
termination_by 16 - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `Endpoint::cookie_bytes`**: it does not fail (what the
    bytes are does not matter, only that they are a function of the
    endpoint). -/
@[step]
theorem Endpoint.cookie_bytes.spec (e : Endpoint) :
    Endpoint.cookie_bytes e ⦃ (_ : Array U8 19#usize) => True ⦄ := by
  unfold Endpoint.cookie_bytes
  split <;> step*

/-- **Spec theorem for `Endpoint::unset`**. -/
@[step]
theorem Endpoint.unset.spec : Endpoint.unset ⦃ (_ : Endpoint) => True ⦄ := by
  unfold Endpoint.unset; simp

/-- No index is in use in `p`, and its windows mean sets. -/
def Peer.Fresh (p : Peer) : Prop := p.Inv ∧ ∀ s, p.idx s = none

/-- **Spec theorem for `Peer::empty`**. -/
@[step]
theorem Peer.empty.spec : Peer.empty ⦃ (p : Peer) =>
    p.Fresh ∧ p.initiation_at.val = 0 ∧ p.has_endpoint = false ∧ p.enabled = false ⦄ := by
  unfold Peer.empty
  step as ⟨e, he⟩
  step as ⟨k, hkv, hki⟩
  refine ⟨⟨⟨hki, hki, hki⟩, ?_⟩, by simp⟩
  intro s; cases s <;> simp [Peer.idx, hkv]

/-! ## The device invariant -/

/-- Peer number `j` of `d`. -/
def peer (d : Device) (j : Nat) : Peer := d.peers.val[j]!

theorem index_peer (d : Device) (j : Usize) (h : j.val < d.peers.val.length) :
    d.peers.val[j.val] = peer d j.val := by
  simp [peer, getElem!_pos d.peers.val j.val h]

theorem peer_set (d : Device) (i j : Nat) (p : Peer) (hi : i < 512) :
    (d.peers.val.set i p)[j]! = if i = j then p else peer d j := by
  by_cases h : i = j
  · subst h; simp [hi]
  · simp [h, peer]

/-- The local indices of live sessions and handshakes are distinct: no index
    is in two places. -/
def Distinct (d : Device) : Prop :=
  ∀ i j s t x, i < d.peer_count.val → j < d.peer_count.val →
    (peer d i).idx s = some x → (peer d j).idx t = some x → i = j ∧ s = t

/-- The invariant of the device. -/
def Device.Inv (d : Device) : Prop :=
  d.peer_count.val ≤ 512 ∧ allowed_ips.Inv d.allowed_ips ∧ (∀ j < 512, (peer d j).Inv) ∧
    Distinct d ∧ (∀ j < 512, (peer d j).initiation_at.val ≤ d.now.val)

/-- Replacing peer `i` by `p'` keeps the indices distinct if each index of
    `p'` comes from a slot of the old peer `i` (by an injective map of slots),
    or is a new index `n`, in use nowhere, in one slot `snew`. -/
theorem Distinct.replace {d : Device} (hd : Distinct d) {i : Usize}
    (hi : i.val < d.peer_count.val) (h16 : d.peer_count.val ≤ 512) (p' : Peer) (n : U32)
    (hn : ∀ j < d.peer_count.val, ¬ Uses (peer d j) n) (σ : Slot → Slot)
    (hσ : ∀ s t, σ s = σ t → s = t) (snew : Slot)
    (hp : ∀ s x, p'.idx s = some x → (peer d i.val).idx (σ s) = some x ∨ (x = n ∧ s = snew)) :
    Distinct { d with peers := d.peers.set i p' } := by
  intro a b s t x ha hb hsa htb
  simp only [peer, Array.set_val_eq] at hsa htb ha hb
  rw [peer_set d i.val _ _ (by omega)] at hsa htb
  split at hsa <;> split at htb
  · subst_vars
    rcases hp s x hsa with h1 | ⟨rfl, rfl⟩ <;> rcases hp t x htb with h2 | ⟨h2, rfl⟩
    · exact ⟨rfl, hσ _ _ (hd _ _ _ _ x hi hi h1 h2).2⟩
    · exact absurd ⟨_, h1⟩ (h2 ▸ hn _ hi)
    · exact absurd ⟨_, h2⟩ (hn _ hi)
    · exact ⟨rfl, rfl⟩
  · subst_vars
    rcases hp s x hsa with h1 | ⟨rfl, -⟩
    · exact absurd (hd _ b _ _ x hi hb h1 htb).1 (by assumption)
    · exact absurd ⟨_, htb⟩ (hn b hb)
  · subst_vars
    rcases hp t x htb with h2 | ⟨rfl, -⟩
    · exact absurd (hd a _ _ _ x ha hi hsa h2).1 (by omega)
    · exact absurd ⟨_, hsa⟩ (hn a ha)
  · exact hd a b s t x ha hb hsa htb

/-- Replacing peer `i` by `p'`, whose indices are the old peer's in the same
    slots, keeps them distinct. -/
theorem Distinct.replace_sub {d : Device} (hd : Distinct d) {i : Usize}
    (hi : i.val < d.peer_count.val) (h16 : d.peer_count.val ≤ 512) (p' : Peer)
    (hp : SubIdx (peer d i.val) p') :
    Distinct { d with peers := d.peers.set i p' } := by
  intro a b s t x ha hb hsa htb
  simp only [peer, Array.set_val_eq] at hsa htb ha hb
  rw [peer_set d i.val _ _ (by omega)] at hsa htb
  split at hsa <;> split at htb
  · subst_vars; exact hd _ _ _ _ x hi hi (hp s x hsa) (hp t x htb)
  · subst_vars; exact hd _ b _ _ x hi hb (hp s x hsa) htb
  · subst_vars; exact hd a _ _ _ x ha hi hsa (hp t x htb)
  · exact hd a b s t x ha hb hsa htb
/-! ## Construction and lookups -/

/-- A device whose peers are all a fresh peer, with none in use, satisfies the
    invariant. -/
theorem new_inv (d : Device) (p : Peer) (hp : p.Fresh) (hpi : p.initiation_at.val = 0)
    (hpeers : d.peers = Array.repeat 512#usize p) (hc : d.peer_count.val = 0)
    (hai : allowed_ips.Inv d.allowed_ips) : d.Inv := by
  have hpj : ∀ j < 512, peer d j = p := by
    intro j hj
    simp only [peer, hpeers, Array.repeat_val]
    rw [getElem!_pos _ _ (by rw [List.length_replicate]; scalar_tac), List.getElem_replicate]
  refine ⟨by omega, hai, fun j hj => hpj j hj ▸ hp.1, ?_, fun j hj => ?_⟩
  · intro a b s t x ha; omega
  · rw [hpj j hj, hpi]; omega

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

/-- **Spec theorem for `Device::new`**: a device with no peers, satisfying the
    invariant. -/
@[step]
theorem Device.new.spec (priv : Key) :
    Device.new inst c priv ⦃ (d : Device) => d.Inv ∧ d.peer_count.val = 0 ⦄ := by
  unfold Device.new
  step*
  exact ⟨new_inv _ p p_post p_post1 rfl rfl ai_post, rfl⟩
end

/-- `p` is the configured peer with static public key `x`. -/
def IsPeer (p : Peer) (x : Key) : Prop := p.enabled = true ∧ p.public = x

/-- **Spec theorem for `is_peer`**. -/
@[step]
theorem is_peer.spec (p : Peer) (x : Key) : is_peer p x ⦃ (r : Bool) => (r = true ↔ IsPeer p x) ⦄ := by
  unfold is_peer IsPeer
  split
  · step*
  · rename_i h; simp [h]

/-- **Spec theorem for `Device::find_peer`'s loop**. -/
@[step]
theorem Device.find_peer_loop.spec (d : Device) (x : Key) (i : Usize)
    (hi : i.val ≤ d.peer_count.val) (hc : d.peer_count.val ≤ 512)
    (hpre : ∀ j < i.val, ¬ IsPeer (peer d j) x) :
    Device.find_peer_loop d x i ⦃ (r : Usize) =>
      r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → IsPeer (peer d r.val) x) ∧
        ∀ j < r.val, ¬ IsPeer (peer d j) x ⦄ := by
  unfold Device.find_peer_loop
  split
  · step as ⟨q, hq⟩
    step as ⟨b, hb⟩
    rw [hq, index_peer d i (by simp; scalar_tac)] at hb
    split
    · rename_i hbt
      simp only [WP.spec_ok]
      exact ⟨by scalar_tac, fun _ => hb.1 hbt, hpre⟩
    · rename_i hbf
      have hne : ¬ IsPeer (peer d i.val) x := fun h => hbf (hb.2 h)
      step as ⟨i1, hi1⟩
      apply WP.spec_mono (Device.find_peer_loop.spec d x i1 (by scalar_tac) hc ?_)
      · exact fun r hr => hr
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp (hi1 ▸ hj) with hj | rfl
        · exact hpre j hj
        · exact hne
  · simp only [WP.spec_ok]
    refine ⟨hi, fun h => absurd h (by scalar_tac), hpre⟩
termination_by d.peer_count.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `Device::find_peer`**: the number of the configured
    peer with static public key `x`, or `peer_count` if none. -/
@[step]
theorem Device.find_peer.spec (d : Device) (x : Key) (hc : d.peer_count.val ≤ 512) :
    Device.find_peer d x ⦃ (r : Usize) =>
      r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → IsPeer (peer d r.val) x) ∧
        (r.val = d.peer_count.val → ∀ j < d.peer_count.val, ¬ IsPeer (peer d j) x) ⦄ := by
  unfold Device.find_peer
  apply WP.spec_mono (Device.find_peer_loop.spec d x 0#usize (by simp) hc (by simp))
  rintro r ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun hr => hr ▸ h3⟩

/-- **Spec theorem for `Device::find_session`'s loop**. -/
@[step]
theorem Device.find_session_loop.spec (d : Device) (x : U32) (i : Usize)
    (hi : i.val ≤ d.peer_count.val) (hc : d.peer_count.val ≤ 512)
    (hpre : ∀ j < i.val, slotOf (peer d j) x = 3) :
    Device.find_session_loop d x i ⦃ (r : Usize) =>
      r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → slotOf (peer d r.val) x ≠ 3) ∧
        ∀ j < r.val, slotOf (peer d j) x = 3 ⦄ := by
  unfold Device.find_session_loop
  split
  · step as ⟨q, hq⟩
    step as ⟨s, hs⟩
    rw [hq, index_peer d i (by simp; scalar_tac)] at hs
    split
    · rename_i hs3
      have h3 : slotOf (peer d i.val) x = 3 := by rw [← hs, hs3]; rfl
      step as ⟨i1, hi1⟩
      apply WP.spec_mono (Device.find_session_loop.spec d x i1 (by scalar_tac) hc ?_)
      · exact fun r hr => hr
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp (hi1 ▸ hj) with hj | rfl
        · exact hpre j hj
        · exact h3
    · rename_i hs3
      simp only [WP.spec_ok]
      refine ⟨by scalar_tac, fun _ => ?_, hpre⟩
      rw [← hs]; intro h; apply hs3; scalar_tac
  · simp only [WP.spec_ok]
    refine ⟨hi, fun h => absurd h (by scalar_tac), hpre⟩
termination_by d.peer_count.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `Device::find_session`**: the number of a peer with a
    session with local index `x`, or `peer_count` if none. -/
@[step]
theorem Device.find_session.spec (d : Device) (x : U32) (hc : d.peer_count.val ≤ 512) :
    Device.find_session d x ⦃ (r : Usize) =>
      r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → slotOf (peer d r.val) x ≠ 3) ∧
        (r.val = d.peer_count.val → ∀ j < d.peer_count.val, slotOf (peer d j) x = 3) ⦄ := by
  unfold Device.find_session
  apply WP.spec_mono (Device.find_session_loop.spec d x 0#usize (by simp) hc (by simp))
  rintro r ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun hr => hr ▸ h3⟩

/-- `p` has a handshake in flight with local index `x`. -/
def HasHandshake (p : Peer) (x : U32) : Prop :=
  p.handshake.active = true ∧ p.handshake.local_index = x

/-- **Spec theorem for `Device::find_handshake`'s loop**. -/
@[step]
theorem Device.find_handshake_loop.spec (d : Device) (x : U32) (i : Usize)
    (hi : i.val ≤ d.peer_count.val) (hc : d.peer_count.val ≤ 512)
    (hpre : ∀ j < i.val, ¬ HasHandshake (peer d j) x) :
    Device.find_handshake_loop d x i ⦃ (r : Usize) =>
      r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → HasHandshake (peer d r.val) x) ∧
        ∀ j < r.val, ¬ HasHandshake (peer d j) x ⦄ := by
  unfold Device.find_handshake_loop
  split
  · step as ⟨q, hq⟩
    rw [index_peer d i (by simp; scalar_tac)] at hq
    subst hq
    have next : ¬ HasHandshake (peer d i.val) x →
        (do
          let i1 ← i + 1#usize
          Device.find_handshake_loop d x i1) ⦃ (r : Usize) =>
          r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → HasHandshake (peer d r.val) x) ∧
            ∀ j < r.val, ¬ HasHandshake (peer d j) x ⦄ := by
      intro hn
      step as ⟨i1, hi1⟩
      apply WP.spec_mono (Device.find_handshake_loop.spec d x i1 (by scalar_tac) hc ?_)
      · exact fun r hr => hr
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp (hi1 ▸ hj) with hj | rfl
        · exact hpre j hj
        · exact hn
    split
    · split
      · simp only [WP.spec_ok]
        exact ⟨by scalar_tac, fun _ => ⟨by assumption, by assumption⟩, hpre⟩
      · exact next (fun h => by simp_all [HasHandshake])
    · exact next (fun h => by simp_all [HasHandshake])
  · simp only [WP.spec_ok]
    refine ⟨hi, fun h => absurd h (by scalar_tac), hpre⟩
termination_by d.peer_count.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `Device::find_handshake`**: the number of a peer with a
    handshake in flight with local index `x`, or `peer_count` if none. -/
@[step]
theorem Device.find_handshake.spec (d : Device) (x : U32) (hc : d.peer_count.val ≤ 512) :
    Device.find_handshake d x ⦃ (r : Usize) =>
      r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → HasHandshake (peer d r.val) x) ∧
        (r.val = d.peer_count.val → ∀ j < d.peer_count.val, ¬ HasHandshake (peer d j) x) ⦄ := by
  unfold Device.find_handshake
  apply WP.spec_mono (Device.find_handshake_loop.spec d x 0#usize (by simp) hc (by simp))
  rintro r ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun hr => hr ▸ h3⟩

/-- **Spec theorem for `Device::index_in_use`'s loop**. -/
@[step]
theorem Device.index_in_use_loop.spec (d : Device) (x : U32) (i : Usize)
    (hi : i.val ≤ d.peer_count.val) (hc : d.peer_count.val ≤ 512)
    (hpre : ∀ j < i.val, ¬ Uses (peer d j) x) :
    Device.index_in_use_loop d x i ⦃ (n : Usize) (r : Usize) =>
      n = d.peer_count ∧ r.val ≤ d.peer_count.val ∧
        (r.val < d.peer_count.val → Uses (peer d r.val) x) ∧ ∀ j < r.val, ¬ Uses (peer d j) x ⦄ := by
  unfold Device.index_in_use_loop
  split
  · step as ⟨q, hq⟩
    step as ⟨b, hb⟩
    rw [hq, index_peer d i (by simp; scalar_tac)] at hb
    split
    · rename_i hbt
      simp only [WP.spec_ok]
      exact ⟨rfl, by scalar_tac, fun _ => hb.mp hbt, hpre⟩
    · rename_i hbf
      have hn : ¬ Uses (peer d i.val) x := fun h => hbf (hb.mpr h)
      step as ⟨i1, hi1⟩
      apply WP.spec_mono (Device.index_in_use_loop.spec d x i1 (by scalar_tac) hc ?_)
      · exact fun r hr => hr
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp (hi1 ▸ hj) with hj | rfl
        · exact hpre j hj
        · exact hn
  · simp only [WP.spec_ok]
    refine ⟨rfl, hi, fun h => absurd h (by scalar_tac), hpre⟩
termination_by d.peer_count.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `Device::index_in_use`**. -/
@[step]
theorem Device.index_in_use.spec (d : Device) (x : U32) (hc : d.peer_count.val ≤ 512) :
    Device.index_in_use d x ⦃ (r : Bool) =>
      (r = true ↔ ∃ j < d.peer_count.val, Uses (peer d j) x) ⦄ := by
  unfold Device.index_in_use
  step as ⟨n, r, hn, h1, h2, h3⟩
  subst hn
  simp only [decide_eq_true_eq]
  constructor
  · intro h; exact ⟨_, h, h2 h⟩
  · rintro ⟨j, hj, hu⟩
    by_contra hr
    exact h3 j (by scalar_tac) hu

/-- **Spec theorem for `Device::clock`**: the later of `now` and the latest
    time seen, which becomes the latest time seen. -/
@[step]
theorem Device.clock.spec (d : Device) (now : U64) :
    Device.clock d now ⦃ (t : U64) (d' : Device) =>
      t.val = max now.val d.now.val ∧ d' = { d with now := t } ∧ d.now.val ≤ t.val ⦄ := by
  unfold Device.clock
  split
  · simp only [WP.spec_ok]; refine ⟨by scalar_tac, rfl, by scalar_tac⟩
  · simp only [WP.spec_ok]; refine ⟨by scalar_tac, rfl, le_refl _⟩

/-- **Spec theorem for `Device::has_fresh_cookie`**. -/
@[step]
theorem Device.has_fresh_cookie.spec (p : Peer) (now : U64) :
    Device.has_fresh_cookie p now ⦃ (_ : Bool) => True ⦄ := by
  unfold Device.has_fresh_cookie
  split <;> step*

/-- **Spec theorem for `Device::secret_stale`**. -/
@[step]
theorem Device.secret_stale.spec (d : Device) (now : U64) :
    Device.secret_stale d now ⦃ (_ : Bool) => True ⦄ := by
  unfold Device.secret_stale
  split <;> step*

/-! ## Keeping the invariant -/

theorem Device.Inv.clock {d : Device} (hd : d.Inv) (t : U64) (ht : d.now.val ≤ t.val) :
    Device.Inv { d with now := t } :=
  ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, fun j hj => le_trans (hd.2.2.2.2 j hj) ht⟩

/-- Replacing peer `i` by `p'` with indices from the old peer's same slots,
    windows meaning sets, and an initiation time not in the future, keeps
    the invariant. -/
theorem Device.Inv.replace {d : Device} (hd : d.Inv) {i : Usize} (hi : i.val < d.peer_count.val)
    (p' : Peer) (hsub : SubIdx (peer d i.val) p') (hinv : p'.Inv)
    (hia : p'.initiation_at.val ≤ d.now.val) :
    Device.Inv { d with peers := d.peers.set i p' } := by
  obtain ⟨hc, hai, hpi, hdis, hti⟩ := hd
  refine ⟨hc, hai, fun j hj => ?_, hdis.replace_sub hi hc p' hsub, fun j hj => ?_⟩
  · simp only [peer, Array.set_val_eq]
    rw [peer_set d i.val _ _ (by omega)]
    split
    · exact hinv
    · exact hpi j hj
  · simp only [peer, Array.set_val_eq]
    rw [peer_set d i.val _ _ (by omega)]
    split
    · exact hia
    · exact hti j hj

/-- The same, with one new index `n` in use nowhere, in slot `snew`. -/
theorem Device.Inv.replace_fresh {d : Device} (hd : d.Inv) {i : Usize}
    (hi : i.val < d.peer_count.val) (p' : Peer) (n : U32)
    (hn : ∀ j < d.peer_count.val, ¬ Uses (peer d j) n) (σ : Slot → Slot)
    (hσ : ∀ s t, σ s = σ t → s = t) (snew : Slot)
    (hp : ∀ s x, p'.idx s = some x → (peer d i.val).idx (σ s) = some x ∨ (x = n ∧ s = snew))
    (hinv : p'.Inv) (hia : p'.initiation_at.val ≤ d.now.val) :
    Device.Inv { d with peers := d.peers.set i p' } := by
  obtain ⟨hc, hai, hpi, hdis, hti⟩ := hd
  refine ⟨hc, hai, fun j hj => ?_, hdis.replace hi hc p' n hn σ hσ snew hp, fun j hj => ?_⟩
  · simp only [peer, Array.set_val_eq]
    rw [peer_set d i.val _ _ (by omega)]
    split
    · exact hinv
    · exact hpi j hj
  · simp only [peer, Array.set_val_eq]
    rw [peer_set d i.val _ _ (by omega)]
    split
    · exact hia
    · exact hti j hj


theorem peer_replace {d' : Device} (d : Device) {i : Usize} {p' : Peer} (j : Nat)
    (hi : i.val < 512) (h : d'.peers = d.peers.set i p') :
    peer d' j = if i.val = j then p' else peer d j := by
  simp only [peer, h, Array.set_val_eq]
  exact peer_set d i.val j p' hi

theorem idx_eq_of {p q : Peer} (h1 : q.handshake = p.handshake) (h2 : q.current = p.current)
    (h3 : q.previous = p.previous) (h4 : q.next = p.next) : q.idx = p.idx := by
  funext s; cases s <;> simp [Peer.idx, h1, h2, h3, h4]

theorem inv_of {p q : Peer} (hp : p.Inv) (h2 : q.current = p.current)
    (h3 : q.previous = p.previous) (h4 : q.next = p.next) : q.Inv := by
  rw [Peer.Inv, h2, h3, h4]; exact hp

/-- Adding a peer with no indices in use, at the end, keeps the invariant. -/
theorem Device.Inv.add {d : Device} (hd : d.Inv) (hlt : d.peer_count.val < 512) (p' : Peer)
    (hnone : ∀ s, p'.idx s = none) (hinv : p'.Inv) (hia : p'.initiation_at.val ≤ d.now.val)
    (n : Usize) (hn : n.val = d.peer_count.val + 1) :
    Device.Inv { d with peers := d.peers.set d.peer_count p', peer_count := n } := by
  obtain ⟨hc, hai, hpi, hdis, hti⟩ := hd
  have hpr := fun j => peer_replace (d' := { d with peers := d.peers.set d.peer_count p', peer_count := n }) d j hlt rfl
  refine ⟨by simp only; omega, hai, fun j hj => ?_, ?_, fun j hj => ?_⟩
  · rw [hpr]; split
    · exact hinv
    · exact hpi j hj
  · intro a b s t x ha hb hsa htb
    simp only at ha hb
    rw [hpr] at hsa htb
    split at hsa
    · simp [hnone] at hsa
    split at htb
    · simp [hnone] at htb
    exact hdis a b s t x (by omega) (by omega) hsa htb
  · simp only; rw [hpr]; split
    · exact hia
    · exact hti j hj

/-- **Spec theorem for `Device::free_slot`'s loop**. -/
@[step]
theorem Device.free_slot_loop.spec (d : Device) (i : Usize) (hi : i.val ≤ d.peer_count.val)
    (hc : d.peer_count.val ≤ 512) (hpre : ∀ j < i.val, (peer d j).enabled = true) :
    Device.free_slot_loop d i ⦃ (r : Usize) =>
      r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → (peer d r.val).enabled = false) ∧
        ∀ j < r.val, (peer d j).enabled = true ⦄ := by
  unfold Device.free_slot_loop
  split
  · step as ⟨q, hq⟩
    rw [index_peer d i (by simp; scalar_tac)] at hq
    split
    · rename_i hen
      step as ⟨i1, hi1⟩
      apply Device.free_slot_loop.spec d i1 (by scalar_tac) hc
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (hi1 ▸ hj) with hj | rfl
      · exact hpre j hj
      · rw [← hq]; exact hen
    · rename_i hen
      simp only [WP.spec_ok]
      exact ⟨by scalar_tac, fun _ => by rw [← hq]; simpa using hen, hpre⟩
  · simp only [WP.spec_ok]
    exact ⟨hi, fun h => absurd h (by scalar_tac), hpre⟩
termination_by d.peer_count.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `Device::free_slot`**: the first slot of a removed
    peer, or `peer_count` if none. -/
@[step]
theorem Device.free_slot.spec (d : Device) (hc : d.peer_count.val ≤ 512) :
    Device.free_slot d ⦃ (r : Usize) =>
      r.val ≤ d.peer_count.val ∧ (r.val < d.peer_count.val → (peer d r.val).enabled = false) ∧
        ∀ j < r.val, (peer d j).enabled = true ⦄ := by
  unfold Device.free_slot
  exact Device.free_slot_loop.spec d 0#usize (by simp) hc (by simp)

/-- A fresh peer's indices are a subset of any peer's. -/
theorem SubIdx.of_fresh (p : Peer) {p' : Peer} (h : ∀ s, p'.idx s = none) : SubIdx p p' :=
  fun s x hs => by rw [h s] at hs; cases hs

/-- **Spec theorem for `Device::remove_peer`**: peer `i`'s slot becomes an
    empty one, not configured, and its allowed IPs go. -/
@[step]
theorem Device.remove_peer.spec (d : Device) (hd : d.Inv) (i : Usize) :
    Device.remove_peer d i ⦃ (r : Bool) (d' : Device) =>
      d'.Inv ∧ d'.now = d.now ∧ d'.peer_count = d.peer_count ∧
        (r = true ↔ i.val < d.peer_count.val) ∧
        (r = false → d' = d) ∧
        (r = true → (peer d' i.val).enabled = false ∧ (∀ s, (peer d' i.val).idx s = none) ∧
          allowed_ips.inUse d'.allowed_ips =
            allowed_ips.keep (UScalar.cast .U16 i) (allowed_ips.inUse d.allowed_ips) ∧
          ∀ j < 512, j ≠ i.val → peer d' j = peer d j) ⦄ := by
  unfold Device.remove_peer
  split
  · simp only [WP.spec_ok]
    refine ⟨hd, rfl, rfl, ?_, fun _ => rfl, fun h => by cases h⟩
    simp only [Bool.false_eq_true, false_iff]; scalar_tac
  rename_i hlt
  have hil : i.val < d.peer_count.val := by scalar_tac
  have hc := hd.1
  step as ⟨p, hfresh, hpi0, _hpe, hen⟩
  step as ⟨a, ha⟩
  step as ⟨q, hq⟩
  step with allowed_ips.AllowedIps.remove_peer.spec d.allowed_ips hd.2.1 q as ⟨t, ht, htu⟩
  have hinv1 := Device.Inv.replace hd hil p (SubIdx.of_fresh _ hfresh.2) hfresh.1 (by simp [hpi0])
  have hinvD : Device.Inv { d with peers := a, allowed_ips := t } := by
    rw [ha]; exact ⟨hinv1.1, ht, hinv1.2.2⟩
  refine ⟨hinvD, by simp [hil], fun h => absurd h (by simp), fun _ => ?_⟩
  have hp : peer { d with peers := a, allowed_ips := t } i.val = p := by
    rw [peer_replace d i.val (by omega) ha]; simp
  refine ⟨by rw [hp, hen], by rw [hp]; exact hfresh.2, by rw [htu, hq], fun j _ hj => ?_⟩
  rw [peer_replace d j (by omega) ha, if_neg (by omega)]

/-- `p`, configured as the peer with static public key `pub`. -/
def withConfig (p : Peer) (pub psk m ck : Key) (ka : U64) : Peer :=
  { p with «public» := pub, psk := psk, mac1_key := m, cookie_key := ck, persistent_keepalive := ka, enabled := true }

/-! ## Configuration -/

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

/-- **Spec theorem for `Device::add_peer`**: adds a configured peer with no
    sessions, in the first slot of a removed peer or else at the end, unless
    the device is full or has it already. -/
@[step]
theorem Device.add_peer.spec (d : Device) (hd : d.Inv) (pub psk : Key) (ka : U64) :
    Device.add_peer inst d c pub psk ka ⦃ (r : Option Usize) (d' : Device) =>
      d'.Inv ∧ d'.now = d.now ∧ d'.allowed_ips = d.allowed_ips ∧
        match r with
        | none => d' = d
        | some i => i.val ≤ d.peer_count.val ∧ i.val < 512 ∧
            d'.peer_count.val = max d.peer_count.val (i.val + 1) ∧
            IsPeer (peer d' i.val) pub ∧
            (i.val < d.peer_count.val → (peer d i.val).enabled = false) ∧
            ∀ j < 512, j ≠ i.val → peer d' j = peer d j ⦄ := by
  unfold Device.add_peer
  have hc := hd.1
  step as ⟨i, hi1, hi2, hi3⟩
  split
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl⟩
  step as ⟨k, hk1, hk2, hk3⟩
  split
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl⟩
  rename_i hfull
  have hk512 : k.val < 512 := by
    have : k.val ≠ 512 := fun h => hfull (by scalar_tac)
    omega
  step as ⟨p, hfresh, hpi0, _hpe, _hen⟩
  step as ⟨a, ha⟩
  step as ⟨a1, ha1⟩
  step as ⟨x, back, hx, hback⟩
  rw [hback]
  have hnone : ∀ s, (withConfig p pub psk a a1 ka).idx s = none := by
    intro s; rw [idx_eq_of rfl rfl rfl rfl]; exact hfresh.2 s
  have hpinv : (withConfig p pub psk a a1 ka).Inv := inv_of hfresh.1 rfl rfl rfl
  split
  · rename_i heq
    have hkc : k.val = d.peer_count.val := by rw [heq]
    step as ⟨n, hn⟩
    refine ⟨?_, by omega, hk512, by omega, ?_, fun h => absurd h (by omega),
      fun j _ hj => ?_⟩
    · rw [show k = d.peer_count from heq]
      exact Device.Inv.add hd (by omega) _ hnone hpinv (by simp [withConfig, hpi0]) n hn
    · rw [peer_replace d _ hk512 rfl]; simp [IsPeer]
    · rw [peer_replace d _ hk512 rfl, if_neg (by omega)]
  · rename_i hne
    have hkc : k.val < d.peer_count.val := by
      have : k.val ≠ d.peer_count.val := fun h => hne (by scalar_tac)
      omega
    simp only [WP.spec_ok]
    refine ⟨?_, rfl, rfl, by omega, hk512, by simp only; omega, ?_, hk2, fun j _ hj => ?_⟩
    · exact Device.Inv.replace hd hkc _ (SubIdx.of_fresh _ hnone) hpinv (by simp [withConfig, hpi0])
    · rw [peer_replace d _ hk512 rfl]; simp [IsPeer]
    · rw [peer_replace d _ hk512 rfl, if_neg (by omega)]

/-- **Spec theorem for `Device::set_endpoint`**. -/
@[step]
theorem Device.set_endpoint.spec (d : Device) (hd : d.Inv) (i : Usize) (e : Endpoint) :
    Device.set_endpoint d i e ⦃ (d' : Device) =>
      d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ⦄ := by
  unfold Device.set_endpoint
  split
  · have hc := hd.1
    have hi16 : i.val < 512 := by scalar_tac
    step as ⟨p, hp⟩
    rw [index_peer d i (by simp; omega)] at hp
    step as ⟨a, ha⟩
    rw [ha]
    apply hd.replace (i := i) (by scalar_tac)
    · rw [hp]; intro s x hx; rwa [idx_eq_of rfl rfl rfl rfl] at hx
    · exact inv_of (hp ▸ hd.2.2.1 i.val hi16) rfl rfl rfl
    · rw [hp]; exact hd.2.2.2.2 _ hi16
  · simpa using hd

/-- **Spec theorem for `Device::allow`**. -/
@[step]
theorem Device.allow.spec (d : Device) (hd : d.Inv) (i : Usize) (v6 : Bool) (addr : U128)
    (len : U32) :
    Device.allow d i v6 addr len ⦃ (_ : Bool) (d' : Device) =>
      d'.Inv ∧ d'.peers = d.peers ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ⦄ := by
  unfold Device.allow
  split
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl⟩
  step as ⟨pp, hpp⟩
  split
  · step as ⟨q, hq⟩
    step with allowed_ips.AllowedIps.insert.spec d.allowed_ips hd.2.1 v6 addr len q
      as ⟨b, t, ht, _ht⟩
    exact ⟨hd.1, ht, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl⟩

/-- **Spec theorem for `Device::finish_handshake_message`**: writes the
    message with its MACs to `out`, and records its `mac1`. -/
@[step]
theorem Device.finish_handshake_message.spec (p : Peer) (now : U64) (msg out : Slice U8)
    (h32 : 32 ≤ msg.length) :
    Device.finish_handshake_message inst c p now msg out
      ⦃ (b : Bool) (p' : Peer) (msg' : Slice U8) (out' : Slice U8) =>
        p' = { p with last_mac1 := p'.last_mac1 } ∧ out'.length = out.length ∧
          ∃ tau, msg'.val = cookie.Spec.withMacs P msg.val p.mac1_key tau ∧
            (b = true ↔ msg.length ≤ out.length) ∧
            (b = true → out'.val = msg'.val ++ out.val.drop msg.length) ⦄ := by
  unfold Device.finish_handshake_message
  step as ⟨fresh, _hf⟩
  have hlen : ∀ tau, (cookie.Spec.withMacs P msg.val p.mac1_key tau).length = msg.length := by
    intro tau
    have h32' : 32 ≤ msg.val.length := h32
    cases tau <;> simp [cookie.Spec.withMacs, Slice.length, Array.property] <;> omega
  obtain ⟨tau, htau⟩ : ∃ tau, (if fresh = true then ok (p, some p.cookie) else ok (p, none) :
      Result (Peer × Option (Array U8 16#usize))) = ok (p, tau) := by
    split <;> exact ⟨_, rfl⟩
  rw [htau]
  step as ⟨m1, m2, hm1, hm2⟩
  have hl : m2.length = msg.length := by
    have := hlen tau; rw [← hm2] at this; simpa [Slice.length] using this
  step as ⟨b1, out1, hol, hb, hcopy⟩
  exact ⟨hol, tau, hm2, by rw [hb, hl], fun h => by rw [hcopy h, hl]⟩

end

/-! ## Sending -/

/-- Device `d'` sent an initiation to its peer `i`, as `bytes`, at `now`: not
    within `REKEY_TIMEOUT` of the previous one, recorded as the latest, and
    the paper's initiation (with its MACs) for the peer's key, with a fresh
    handshake whose state the peer now keeps. -/
def InitSent (P : Primitives) (d d' : Device) (i : Nat) (env : Env) (now : U64)
    (bytes : List U8) : Prop :=
  ((peer d i).has_initiation = true →
      (peer d i).initiation_at.val + 5000000000 ≤ now.val) ∧
    (peer d' i).has_initiation = true ∧ (peer d' i).initiation_at = now ∧
    (peer d' i).handshake.active = true ∧ (peer d' i).handshake.local_index = env.index ∧
    ∃ msg, noise.Spec.createInitiation P d'.private d'.public (peer d i).public env.ephemeral
        env.index env.timestamp = some (msg, (peer d' i).handshake.state) ∧
      ∃ enc tau, message.Message.Spec enc (.Initiation msg) ∧
        bytes = cookie.Spec.withMacs P enc (peer d i).mac1_key tau

/-- What a call that may only send did, besides keeping the invariant. -/
def SendOnly (P : Primitives) (d d' : Device) (i : Nat) (env : Env) (now : U64) (a : Action)
    (out' : List U8) (data : Usize → Prop) : Prop :=
  match a with
  | .None => True
  | .Send e n => e = (peer d' i).endpoint ∧
      ((n.val = 148 ∧ InitSent P d d' i env now (out'.take 148)) ∨ data n)
  | .Deliver _ => False

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

/-- **Spec theorem for `Device::begin_handshake`**: sends an initiation to
    peer `i`, unless one was sent within `REKEY_TIMEOUT`, it has no endpoint,
    or the new index is in use. Only peer `i` changes. -/
@[step]
theorem Device.begin_handshake.spec (d : Device) (hd : d.Inv) (env : Env) (now : U64)
    (hnow : now = d.now) (i : Usize) (hi : i.val < d.peer_count.val) (out : Slice U8) :
    Device.begin_handshake inst d c env now i out ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
      d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
        d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
        (∀ j, j ≠ i.val → peer d' j = peer d j) ∧
        (a = .None → d' = d) ∧ SendOnly P d d' i.val env now a out'.val (fun _ => False) ⦄ := by
  have hc := hd.1
  have hi16 : i.val < 512 := by omega
  unfold Device.begin_handshake
  step as ⟨p, hp⟩
  rw [index_peer d i (by simp; omega)] at hp
  split
  swap
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, trivial⟩
  rename_i hep
  step as ⟨soon, hsoon⟩
  split
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, trivial⟩
  rename_i hsoon'
  step as ⟨used, hused⟩
  split
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, trivial⟩
  rename_i hused'
  step as ⟨o, ho⟩
  rcases o with _ | ⟨msg, st⟩
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, trivial⟩
  step*
  swap
  · exact ⟨hd, b2_post, fun _ _ => trivial, fun _ => trivial, trivial⟩
  rename_i hb2
  obtain ⟨v, hv⟩ : ∃ v, (if p1.handshake.active = true then ok p1.attempt_started else ok now :
      Result U64) = ok v := by
    split <;> exact ⟨_, rfl⟩
  rw [hv]
  step as ⟨a, ha⟩
  have hk : p1.current = p.current ∧ p1.previous = p.previous ∧ p1.next = p.next ∧
      p1.endpoint = p.endpoint ∧ p1.mac1_key = p.mac1_key := by
    rw [p1_post]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hpd := fun j => peer_replace (d' := { d with peers := a }) d (i := i) j hi16 ha
  have hfresh : ∀ j < d.peer_count.val, ¬ Uses (peer d j) env.index :=
    fun j hj hu => hused' (hused.mpr ⟨j, hj, hu⟩)
  have hgate : (peer d i.val).has_initiation = true →
      (peer d i.val).initiation_at.val + 5000000000 ≤ now.val := by
    intro hhi
    rw [← hp] at hhi ⊢
    simp [hhi] at hsoon
    rw [hsoon] at hsoon'
    simp at hsoon'
    omega
  have hlen148 : (cookie.Spec.withMacs P s.val p.mac1_key tau).length = 148 := by
    have : s.val.length = 148 := by rw [s_post]; simp
    cases tau <;> simp [cookie.Spec.withMacs, Array.property, this]
  refine ⟨?_, b2_post, fun j hj => by rw [hpd, if_neg (Ne.symm hj)],
    (fun h => by cases h), ?_⟩
  · rw [ha]
    apply hd.replace_fresh (by omega) _ env.index hfresh id (fun _ _ h => h) .hs
    · intro s x hx
      cases s
      · right; simp [Peer.idx] at hx; exact ⟨hx.symm, rfl⟩
      · left; rw [← hp]; simpa [Peer.idx, hk.1] using hx
      · left; rw [← hp]; simpa [Peer.idx, hk.2.1] using hx
      · left; rw [← hp]; simpa [Peer.idx, hk.2.2.1] using hx
    · exact inv_of (hp ▸ hd.2.2.1 i.val hi16) hk.1 hk.2.1 hk.2.2.1
    · simp [hnow]
  · try simp only [SendOnly]
    rw [hpd, if_pos rfl]
    refine ⟨by simp [hk.2.2.2.1], Or.inl ⟨by simp, hgate, ?_⟩⟩
    rw [hpd, if_pos rfl]
    refine ⟨rfl, rfl, rfl, rfl, msg, by rw [← hp]; exact ho.symm, bytes.val, tau,
      bytes_post, ?_⟩
    rw [b2_post3 hb2, b2_post1, List.take_left' hlen148, s_post, hp]


/-- Device `d'` sent `packet` to its peer `i` as the transport message
    `bytes`, at `now`: under the peer's current keypair, which may send, with
    its counter, which then went up by one (nothing else of the keypair
    changed); the message is the header and the sealed padded packet. -/
def DataSent (P : Primitives) (d d' : Device) (i : Nat) (now : U64) (packet : List U8)
    (n : Usize) (bytes : List U8) : Prop :=
  CanSend (peer d i).current now.val ∧
    (peer d' i).current = { (peer d i).current with counter := (peer d' i).current.counter } ∧
    (peer d' i).current.counter.val = (peer d i).current.counter.val + 1 ∧
    n.val = paddedLen packet.length + 32 ∧
    ∃ hdr : List U8, hdr.length = 16 ∧ leNat (hdr.take 4) = 4 ∧
      FmtD message.TransportHeader.Insts.UntrustedReaderDecode (hdr.drop 4)
        ⟨(peer d i).current.remote_index, (peer d i).current.counter⟩ 12 ∧
      bytes.take n.val = hdr ++ P.aead (peer d i).current.send (peer d i).current.counter.val []
        (padded packet)

/-- **Spec theorem for `Device::send_data`**: sends `packet` to peer `i` under
    its current keypair if it may send, else starts a handshake. -/
@[step]
theorem Device.send_data.spec (d : Device) (hd : d.Inv) (env : Env) (now : U64)
    (hnow : now = d.now) (i : Usize) (hi : i.val < d.peer_count.val)
    (packet work out : Slice U8) (hlen : packet.length + 47 ≤ Usize.max) :
    Device.send_data inst d c env now i packet work out
      ⦃ (a : Action) (d' : Device) (work' : Slice U8) (out' : Slice U8) =>
        d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
          d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
          (∀ j, j ≠ i.val → peer d' j = peer d j) ∧ (a = .None → d' = d) ∧
          SendOnly P d d' i.val env now a out'.val
            (fun n => DataSent P d d' i.val now packet.val n out'.val) ⦄ := by
  have hc := hd.1
  have hi16 : i.val < 512 := by omega
  unfold Device.send_data
  step as ⟨p, hp⟩
  rw [index_peer d i (by simp; omega)] at hp
  split
  swap
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, trivial⟩
  step as ⟨b, hb⟩
  split
  swap
  · step as ⟨a, d', out1, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
    cases a <;> simp_all [SendOnly]
  rename_i hep hbt
  have hcs : CanSend p.current now.val := by simpa [hbt] using hb
  step with transport.encrypt.spec (inst := inst) (c := c) (P := P) p.current.send p.current.remote_index p.current.counter
    packet work out hlen as ⟨o, work1, out1, hol, ho⟩
  rcases o with _ | n
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, hol, fun _ _ => rfl, fun _ => rfl, trivial⟩
  obtain ⟨hn, hdr, hhl, hh4, hhf, hbytes⟩ := ho
  have hrej : p.current.counter.val < replay.REJECT := hcs.2
  step as ⟨i1, hi1⟩
  step as ⟨b1, hb1⟩
  obtain ⟨b2, hb2⟩ : ∃ v, (if b1 = true then ok true else ok p.rekey_wanted : Result Bool) = ok v := by
    split <;> exact ⟨_, rfl⟩
  rw [hb2]
  step as ⟨a, ha⟩
  have hpd := fun j => peer_replace (d' := { d with peers := a }) d (i := i) j hi16 ha
  refine ⟨?_, hol, fun j hj => by rw [hpd, if_neg (Ne.symm hj)], (fun h => by cases h), ?_⟩
  · rw [ha]
    apply hd.replace (by omega)
    · rw [← hp]; intro s x hx; cases s <;> simpa [Peer.idx] using hx
    · exact inv_of (hp ▸ hd.2.2.1 i.val hi16) rfl rfl rfl
    · exact hp ▸ hd.2.2.2.2 _ hi16
  · try simp only [SendOnly]
    rw [hpd, if_pos rfl]
    refine ⟨rfl, Or.inr ⟨?_, ?_, ?_, hn, hdr, hhl, hh4, ?_, ?_⟩⟩
    · rw [← hp]; exact hcs
    · rw [hpd, if_pos rfl, ← hp]
    · rw [hpd, if_pos rfl, ← hp]; exact hi1
    · rw [← hp]; exact hhf
    · rw [← hp]; exact hbytes

/-- **Spec theorem for `Device::send_keepalive`**: `send_data` with an empty
    packet. -/
@[step]
theorem Device.send_keepalive.spec (d : Device) (hd : d.Inv) (env : Env) (now : U64)
    (hnow : now = d.now) (i : Usize) (hi : i.val < d.peer_count.val) (out : Slice U8) :
    Device.send_keepalive inst d c env now i out
      ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
        d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
          d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
          (∀ j, j ≠ i.val → peer d' j = peer d j) ∧ (a = .None → d' = d) ∧
          SendOnly P d d' i.val env now a out'.val
            (fun n => DataSent P d d' i.val now [] n out'.val) ⦄ := by
  unfold Device.send_keepalive
  step as ⟨s, hs⟩
  step as ⟨s1, back, hs1, hback⟩
  step with Device.send_data.spec (inst := inst) (c := c) (P := P) d hd env now hnow i hi s s1 out (by simp [hs]; scalar_tac)
    as ⟨a, d', w, out1, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
  have : s.val = [] := by simp [hs]
  rw [this] at h8; exact h8

/-- The IP packet `l` is addressed to peer `i`: the longest prefix matching
    its destination belongs to `i`. -/
def RoutesTo (t : allowed_ips.AllowedIps) (l : List U8) (i : Nat) : Prop :=
  ∃ ip, Inner.Spec l ip ∧ ∃ e, allowed_ips.Longest t ip.v6 ip.dst.val e ∧ e.peer.val = i

/-- **Spec theorem for `Device::handle_packet`**: an IP packet to send. If it
    is a well-formed IP packet whose destination routes to a peer, it is sent
    to that peer under its current keypair, or, if that may not send, an
    initiation is sent instead (subject to `REKEY_TIMEOUT`). Nothing else
    changes. -/
@[step]
theorem Device.handle_packet.spec (d : Device) (hd : d.Inv) (env : Env)
    (packet work out : Slice U8) :
    Device.handle_packet inst d c env packet work out
      ⦃ (a : Action) (d' : Device) (work' : Slice U8) (out' : Slice U8) =>
        d'.Inv ∧ d'.now.val = max env.now.val d.now.val ∧ d'.peer_count = d.peer_count ∧
          d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
          match a with
          | .None => True
          | .Deliver _ => False
          | .Send e n => ∃ i < d.peer_count.val, RoutesTo d.allowed_ips packet.val i ∧
              e = (peer d' i).endpoint ∧ (∀ j, j ≠ i → peer d' j = peer d j) ∧
              ((n.val = 148 ∧ InitSent P d d' i env d'.now (out'.val.take 148)) ∨
                DataSent P d d' i d'.now packet.val n out'.val) ⦄ := by
  unfold Device.handle_packet
  step as ⟨now, d1, hnow, hd1, hle⟩
  have hinv1 : d1.Inv := hd1 ▸ hd.clock now hle
  split
  · simp only [WP.spec_ok]; exact ⟨hinv1, by rw [hd1]; exact hnow, by rw [hd1], by rw [hd1], rfl,
      trivial⟩
  rename_i hsmall
  step as ⟨o, ho⟩
  rcases o with _ | ip
  · simp only [WP.spec_ok]; exact ⟨hinv1, by rw [hd1]; exact hnow, by rw [hd1], by rw [hd1], rfl,
      trivial⟩
  step with allowed_ips.AllowedIps.lookup.spec d1.allowed_ips hinv1.2.1 ip.v6 ip.dst as ⟨q, hq⟩
  rcases q with _ | q
  · simp only [WP.spec_ok]; exact ⟨hinv1, by rw [hd1]; exact hnow, by rw [hd1], by rw [hd1], rfl,
      trivial⟩
  step as ⟨i, hi⟩
  split
  · simp only [WP.spec_ok]; exact ⟨hinv1, by rw [hd1]; exact hnow, by rw [hd1], by rw [hd1], rfl,
      trivial⟩
  rename_i hilt
  have hic : i.val < d1.peer_count.val := by scalar_tac
  step with Device.send_data.spec (inst := inst) (c := c) (P := P) d1 hinv1 env now (by rw [hd1]) i hic packet work out
    (by scalar_tac) as ⟨a, d', w, out1, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨h1, by rw [h3, hd1]; exact hnow, by rw [h2, hd1], by rw [h4, hd1], h5, ?_⟩
  subst hd1
  have hiq : i.val = q.val := by rw [hi]; exact U16.cast_Usize_val_eq q
  obtain ⟨e', he', hpe'⟩ := hq
  have hroute : RoutesTo d.allowed_ips packet.val i.val :=
    ⟨ip, ho, e', he', by rw [hpe', hiq]⟩
  have h3' : d'.now = now := h3
  rw [h3']
  cases a with
  | None => trivial
  | Deliver n => exact h8
  | Send e n =>
    obtain ⟨he, hsent⟩ := h8
    exact ⟨i.val, hic, hroute, he, h6, hsent⟩

end

theorem InitSent.congr {P : Primitives} {d1 d2 d' : Device} {i : Nat} {env : Env} {now : U64}
    {bytes : List U8} (hk : TimersKeep (peer d2 i) (peer d1 i))
    (h : InitSent P d1 d' i env now bytes) : InitSent P d2 d' i env now bytes := by
  obtain ⟨hia, hhi, hpub, hmac, -⟩ := hk
  obtain ⟨hg, h1, h2, h3, h4, msg, hmsg, enc, tau, henc, hb⟩ := h
  refine ⟨fun hh => ?_, h1, h2, h3, h4, msg, by rw [← hpub]; exact hmsg, enc, tau, henc,
    by rw [← hmac]; exact hb⟩
  rw [← hia]; exact hg (hhi ▸ hh)

theorem DataSent.congr {P : Primitives} {d1 d2 d' : Device} {i : Nat} {now : U64}
    {packet : List U8} {n : Usize} {bytes : List U8}
    (hk : KeepOrEmpty (peer d2 i).current (peer d1 i).current)
    (h : DataSent P d1 d' i now packet n bytes) : DataSent P d2 d' i now packet n bytes := by
  have heq : (peer d1 i).current = (peer d2 i).current := by
    rcases hk with h' | ⟨hv, -⟩
    · exact h'
    · exact absurd h.1.1.1 (by simp [hv])
  unfold DataSent at h ⊢
  rw [← heq]; exact h

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

/-- **Spec theorem for `Device::tick_peer`**: runs the timers of peer `i`,
    and sends what they call for. Only peer `i` changes. -/
@[step]
theorem Device.tick_peer.spec (d : Device) (hd : d.Inv) (env : Env) (now : U64)
    (hnow : now = d.now) (i : Usize) (hi : i.val < d.peer_count.val) (out : Slice U8) :
    Device.tick_peer inst d c env now i out ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
      d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
        d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
        (∀ j, j ≠ i.val → peer d' j = peer d j) ∧
        SendOnly P d d' i.val env now a out'.val
          (fun n => DataSent P d d' i.val now [] n out'.val) ⦄ := by
  have hc := hd.1
  have hi16 : i.val < 512 := by omega
  unfold Device.tick_peer
  step as ⟨p, hp⟩
  rw [index_peer d i (by simp; omega)] at hp
  step as ⟨t, p1, ht, hsub, hinv, hkeep⟩
  step as ⟨x, back, hx, hback⟩
  -- The device with the timers' peer.
  have hdm : Device.Inv { d with peers := back p1 } := by
    rw [hback]
    apply hd.replace (by omega) p1
    · rw [← hp]; exact hsub
    · exact hinv (hp ▸ hd.2.2.1 i.val hi16)
    · rw [hkeep.1, hp]; exact hd.2.2.2.2 _ hi16
  have hpm := fun j => peer_replace (d' := { d with peers := back p1 }) d (i := i) (p' := p1) j hi16
    (by rw [hback])
  have hkeep' : TimersKeep (peer d i.val) (peer { d with peers := back p1 } i.val) := by
    rw [hpm, if_pos rfl, ← hp]; exact hkeep
  have hothers : ∀ j, j ≠ i.val → peer { d with peers := back p1 } j = peer d j :=
    fun j hj => by rw [hpm, if_neg (Ne.symm hj)]
  split
  · step with Device.begin_handshake.spec (inst := inst) (c := c) (P := P) _ hdm env now hnow i hi out
      as ⟨a, d', out1, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨h1, h2, h3, h4, h5, fun j hj => by rw [h6 j hj, hothers j hj], ?_⟩
    cases a with
    | None => trivial
    | Deliver n => exact h8
    | Send e n =>
      obtain ⟨he, hs⟩ := h8
      exact ⟨he, hs.imp (fun h => ⟨h.1, h.2.congr hkeep'⟩) (fun h => h.elim)⟩
  split
  · step with Device.send_keepalive.spec (inst := inst) (c := c) (P := P) _ hdm env now hnow i hi out
      as ⟨a, d', out1, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨h1, h2, h3, h4, h5, fun j hj => by rw [h6 j hj, hothers j hj], ?_⟩
    cases a with
    | None => trivial
    | Deliver n => exact h8
    | Send e n =>
      obtain ⟨he, hs⟩ := h8
      exact ⟨he, hs.imp (fun h => ⟨h.1, h.2.congr hkeep'⟩) (fun h => h.congr hkeep'.2.2.2.2)⟩
  · simp only [WP.spec_ok]
    exact ⟨hdm, rfl, rfl, rfl, rfl, hothers, trivial⟩

omit h in
theorem TimersKeep.refl (p : Peer) : TimersKeep p p := ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
omit h in

/-- What a call that runs the timers may have sent: an initiation, or a
    keepalive, to some peer `k` (at least `i`). -/
def TickSent (P : Primitives) (d d' : Device) (i : Nat) (env : Env) (now : U64) (a : Action)
    (out' : List U8) : Prop :=
  match a with
  | .None => True
  | .Deliver _ => False
  | .Send e n => ∃ k, i ≤ k ∧ k < d.peer_count.val ∧ e = (peer d' k).endpoint ∧
      ((n.val = 148 ∧ InitSent P d d' k env now (out'.take 148)) ∨
        DataSent P d d' k now [] n out')

/-- **Spec theorem for `Device::tick_from`**: runs the timers of peers `i`
    onwards until one sends something. -/
@[step]
theorem Device.tick_from.spec (d : Device) (hd : d.Inv) (env : Env) (now : U64)
    (hnow : now = d.now) (i : Usize) (hi : i.val ≤ d.peer_count.val) (out : Slice U8) :
    Device.tick_from inst d c env now i out ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
      d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
        d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
        TickSent P d d' i.val env now a out'.val ⦄ := by
  unfold Device.tick_from
  split
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl, trivial⟩
  rename_i hlt
  have hic : i.val < d.peer_count.val := by scalar_tac
  step with Device.tick_peer.spec (inst := inst) (c := c) (P := P) d hd env now hnow i hic out
    as ⟨a, d1, out1, h1, h2, h3, h4, h5, h6, h7⟩
  rcases a with _ | ⟨e, n⟩ | n
  · simp only [bind_ok, ↓reduceIte]
    step as ⟨i1, hi1⟩
    have hnow1 : now = d1.now := by rw [h3, hnow]
    have hi1' : i1.val ≤ d1.peer_count.val := by rw [h2]; scalar_tac
    step with Device.tick_from.spec d1 h1 env now hnow1 i1 hi1' out1
      as ⟨a', d', out', g1, g2, g3, g4, g5, g6⟩
    refine ⟨g1, by rw [g2, h2], by rw [g3, h3], by rw [g4, h4], by rw [g5, h5], ?_⟩
    rcases a' with _ | ⟨e', n'⟩ | n'
    · trivial
    · obtain ⟨k, hk1, hk2, he, hs⟩ := g6
      have hki : k ≠ i.val := by omega
      have hpk : peer d1 k = peer d k := h6 k hki
      have hkeep : TimersKeep (peer d k) (peer d1 k) := hpk ▸ TimersKeep.refl _
      exact ⟨k, by omega, by rw [← h2]; exact hk2, he,
        hs.imp (fun h => ⟨h.1, h.2.congr hkeep⟩) (fun h => h.congr hkeep.2.2.2.2)⟩
    · exact g6
  · simp only [bind_ok, ↓reduceIte, Bool.false_eq_true, WP.spec_ok]
    obtain ⟨he, hs⟩ := h7
    exact ⟨h1, h2, h3, h4, h5, i.val, le_refl _, hic, he, hs⟩
  · exact absurd h7 (by simp [SendOnly])
termination_by d.peer_count.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `Device::tick`**: runs the timers. Whatever it sends is
    an initiation not within `REKEY_TIMEOUT` of the previous one to that peer,
    or a keepalive under a keypair that may send. -/
@[step]
theorem Device.tick.spec (d : Device) (hd : d.Inv) (env : Env) (out : Slice U8) :
    Device.tick inst d c env out ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
      d'.Inv ∧ d'.now.val = max env.now.val d.now.val ∧ d'.peer_count = d.peer_count ∧
        d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
        TickSent P d d' 0 env d'.now a out'.val ⦄ := by
  unfold Device.tick
  step as ⟨now, d1, hnow, hd1, hle⟩
  have hinv1 : d1.Inv := hd1 ▸ hd.clock now hle
  step with Device.tick_from.spec (inst := inst) (c := c) (P := P) d1 hinv1 env now
      (by rw [hd1]) 0#usize (by simp) out
    as ⟨a, d', out1, h1, h2, h3, h4, h5, h6⟩
  subst hd1
  have h3' : d'.now = now := h3
  refine ⟨h1, by rw [h3']; exact hnow, h2, h4, h5, ?_⟩
  rw [h3']
  exact h6

omit h in
/-- Replacing peer `i` by `p'`, whose indices come from the old peer's slots
    by an injective map, keeps the invariant. -/
theorem Device.Inv.replace_perm {d : Device} (hd : d.Inv) {i : Usize}
    (hi : i.val < d.peer_count.val) (p' : Peer) (σ : Slot → Slot)
    (hσ : ∀ s t, σ s = σ t → s = t)
    (hp : ∀ s x, p'.idx s = some x → (peer d i.val).idx (σ s) = some x) (hinv : p'.Inv)
    (hia : p'.initiation_at.val ≤ d.now.val) :
    Device.Inv { d with peers := d.peers.set i p' } := by
  obtain ⟨hc, hai, hpi, hdis, hti⟩ := hd
  have hd' : Distinct { d with peers := d.peers.set i p' } := by
    intro a b s t x ha hb hsa htb
    simp only [peer, Array.set_val_eq] at hsa htb ha hb
    rw [peer_set d i.val _ _ (by omega)] at hsa htb
    split at hsa <;> split at htb
    · subst_vars
      exact ⟨rfl, hσ _ _ (hdis _ _ _ _ x hi hi (hp s x hsa) (hp t x htb)).2⟩
    · subst_vars; exact absurd (hdis _ b _ _ x hi hb (hp s x hsa) htb).1 (by omega)
    · subst_vars; exact absurd (hdis a _ _ _ x ha hi hsa (hp t x htb)).1 (by omega)
    · exact hdis a b s t x ha hb hsa htb
  refine ⟨hc, hai, fun j hj => ?_, hd', fun j hj => ?_⟩
  · simp only [peer, Array.set_val_eq]
    rw [peer_set d i.val _ _ (by omega)]
    split
    · exact hinv
    · exact hpi j hj
  · simp only [peer, Array.set_val_eq]
    rw [peer_set d i.val _ _ (by omega)]
    split
    · exact hia
    · exact hti j hj

/-- `p` with its keypairs moved on: the next one becomes current, the current
    one previous, and `k` next. -/
def rotated (p : Peer) (k : Keypair) : Peer := { p with current := p.next, previous := p.current, next := k }

/-- The slots that the keypairs of `rotated p k` come from. -/
def rotSlot : Slot → Slot
  | .hs => .hs
  | .cur => .next
  | .prev => .cur
  | .next => .prev

omit h in
theorem rotSlot_inj : ∀ s t, rotSlot s = rotSlot t → s = t := by
  intro s t h; cases s <;> cases t <;> simp_all [rotSlot]

omit h in
theorem rotated_idx (p : Peer) (k : Keypair) (hk : k.valid = false) :
    ∀ s x, (rotated p k).idx s = some x → p.idx (rotSlot s) = some x := by
  intro s x hx
  cases s <;> simp only [rotated, rotSlot, Peer.idx] at hx ⊢ <;> first | exact hx | simp [hk] at hx

omit h in
theorem rotated_inv {p : Peer} {k : Keypair} (hp : p.Inv) (hk : KpInv k) : (rotated p k).Inv :=
  ⟨hp.2.2, hp.1, hk⟩

omit h in
/-- **Spec theorem for `rotate`**. -/
@[step]
theorem rotate.spec (p : Peer) :
    rotate p ⦃ (r : Peer) => ∃ k : Keypair, k.valid = false ∧ KpInv k ∧ r = rotated p k ⦄ := by
  unfold rotate
  step as ⟨k, hk1, hk2⟩
  exact ⟨k, hk1, hk2, rfl⟩

omit h in
theorem rotate_or (q : Peer) (b : Prop) [Decidable b] :
    (if b then rotate q else ok q) ⦃ (r : Peer) =>
      (¬ b ∧ r = q) ∨ (b ∧ ∃ k : Keypair, k.valid = false ∧ KpInv k ∧ r = rotated q k) ⦄ := by
  split
  · rename_i hb
    apply WP.spec_mono (rotate.spec q); intro r hr; exact Or.inr ⟨hb, hr⟩
  · rename_i hb; simp [hb]

omit h in
theorem setKpAt_idx (p : Peer) (s : Nat) (r : replay.Replay) :
    (setKpAt p s { kpAt p s with replay := r }).idx = p.idx := by
  unfold setKpAt kpAt
  split_ifs <;> funext t <;> cases t <;> rfl

omit h in
theorem kpAt_inv {p : Peer} (hp : p.Inv) (s : Nat) : KpInv (kpAt p s) := by
  unfold kpAt; split_ifs
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2

omit h in
theorem setKpAt_inv {p : Peer} (hp : p.Inv) (s : Nat) {k : Keypair} (hk : KpInv k) :
    (setKpAt p s k).Inv := by
  unfold setKpAt; split_ifs
  · exact ⟨hk, hp.2.1, hp.2.2⟩
  · exact ⟨hp.1, hk, hp.2.2⟩
  · exact ⟨hp.1, hp.2.1, hk⟩

omit h in
theorem kpAt_setKpAt (p : Peer) (s : Nat) (k : Keypair) (hs : s < 3) :
    kpAt (setKpAt p s k) s = k := by
  unfold setKpAt kpAt; split_ifs <;> first | rfl | omega

omit h in
theorem setKpAt_two (p : Peer) (k : Keypair) : (setKpAt p 2 k).next = k := by
  simp [setKpAt]

omit h in
theorem setKpAt_fields (p : Peer) (s : Nat) (k : Keypair) :
    (setKpAt p s k).initiation_at = p.initiation_at ∧ (setKpAt p s k).handshake = p.handshake := by
  unfold setKpAt; split_ifs <;> exact ⟨rfl, rfl⟩

/-! ## Receiving -/

/-- `d` with another cookie secret. -/
def withSecret (d : Device) (a : Array U8 32#usize) (b : Bool) (t : U64) : Device :=
  { d with cookie_secret := a, has_cookie_secret := b, cookie_secret_at := t }

omit h in
theorem Device.Inv.withSecret {d : Device} (hd : d.Inv) (a : Array U8 32#usize) (b : Bool)
    (t : U64) : (withSecret d a b t).Inv := hd

/-- **Spec theorem for `Device::admit`**: lets a handshake message through
    (0) only if its `mac1` is valid and, under load, its `mac2` is valid under
    some cookie; otherwise drops it (1) or writes a cookie reply (2). Only the
    cookie secret changes. -/
@[step]
theorem Device.admit.spec (d : Device) (env : Env) (now : U64) (src : Endpoint)
    (under_load : Bool) (bytes : Slice U8) (sender : U32) (mac1 : Array U8 16#usize)
    (out : Slice U8) :
    Device.admit inst d c env now src under_load bytes sender mac1 out
      ⦃ (r : U8) (d' : Device) (out' : Slice U8) =>
        r.val ≤ 2 ∧ out'.length = out.length ∧
        d' = withSecret d d'.cookie_secret d'.has_cookie_secret d'.cookie_secret_at ∧
        (r.val = 0 → cookie.Spec.mac1Valid P bytes.val d.mac1_key ∧
          (under_load = true → ∃ tau, cookie.Spec.mac2Valid P bytes.val tau)) ⦄ := by
  unfold Device.admit
  step as ⟨b, hb⟩
  split
  swap
  · simp only [WP.spec_ok]; exact ⟨by simp, rfl, rfl, by simp⟩
  rename_i hbt
  have hm1 := hb.mp hbt
  split
  swap
  · simp only [WP.spec_ok]
    rename_i hl
    exact ⟨by simp, rfl, rfl, fun _ => ⟨hm1, fun h => absurd h hl⟩⟩
  step as ⟨st, _hst⟩
  obtain ⟨v, hv⟩ : ∃ v, (if st = true then ok (env.secret, true, now, env)
      else ok (d.cookie_secret, d.has_cookie_secret, d.cookie_secret_at, env) :
      Result (Array U8 32#usize × Bool × U64 × Env)) = ok v := by
    split <;> exact ⟨_, rfl⟩
  rw [hv]
  obtain ⟨a, b2, t, env1⟩ := v
  step as ⟨cb, _hcb⟩
  step as ⟨s, hs⟩
  step as ⟨tau, htau⟩
  step as ⟨b3, hb3⟩
  split
  · simp only [WP.spec_ok]
    rename_i hb3t
    exact ⟨by simp, rfl, rfl, fun _ => ⟨hm1, fun _ => ⟨tau, hb3.mp hb3t⟩⟩⟩
  step as ⟨reply, _hreply⟩
  step as ⟨enc, _henc⟩
  step as ⟨s1, _hs1⟩
  step as ⟨b4, out1, hol, _h1, _h2⟩
  split
  · simp only [WP.spec_ok]; exact ⟨by simp, hol, rfl, by simp⟩
  · simp only [WP.spec_ok]; exact ⟨by simp, hol, rfl, by simp⟩

/-- **Spec theorem for `Device::on_cookie_reply`**: keeps the cookie of a
    reply that decrypts under the `mac1` of our last message to the peer it is
    addressed to. Sends nothing. -/
@[step]
theorem Device.on_cookie_reply.spec (d : Device) (hd : d.Inv) (now : U64)
    (msg : message.CookieReply) :
    Device.on_cookie_reply inst d c now msg ⦃ (a : Action) (d' : Device) =>
      d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
        d'.allowed_ips = d.allowed_ips ∧ a = .None ⦄ := by
  have hc := hd.1
  unfold Device.on_cookie_reply
  step as ⟨i1, hi1, _h1, _h2⟩
  have hsel : (if i1 >= d.peer_count then Device.find_session d msg.receiver else ok i1)
      ⦃ (v : Usize) => v.val ≤ d.peer_count.val ⦄ := by
    split
    · step as ⟨v, hv, _h1, _h2⟩
      exact hv
    · simp only [WP.spec_ok]; exact hi1
  step with hsel as ⟨i2, hi2⟩
  split
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl⟩
  have hlt : i2.val < d.peer_count.val := by scalar_tac
  have hi16 : i2.val < 512 := by omega
  step as ⟨p, hp⟩
  rw [index_peer d i2 (by simp; omega)] at hp
  step as ⟨o, ho⟩
  rcases o with _ | tau
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl⟩
  step as ⟨a, ha⟩
  rw [ha]
  apply hd.replace (by omega)
  · rw [← hp]; intro s x hx; rwa [idx_eq_of rfl rfl rfl rfl] at hx
  · exact inv_of (hp ▸ hd.2.2.1 i2.val hi16) rfl rfl rfl
  · exact hp ▸ hd.2.2.2.2 _ hi16

/-- The transport message `body` with `counter`, to the session with local
    index `receiver`, was delivered by `d` as the IP packet `out'[..n]`: it
    was sealed under the receiving key of a keypair `kp` of peer `i` with that
    index, which may receive; its counter was fresh for `kp`'s window (whose
    accepted counters are some `S`, and then `S` with the counter); and the
    plaintext is an IP packet of length `n` whose source routes to `i`. -/
def Delivered (P : Primitives) (d d' : Device) (i s : Nat) (receiver : U32) (counter : U64)
    (body out' : List U8) (n : Usize) : Prop :=
  s < 3 ∧ (kpAt (peer d i) s).valid = true ∧ (kpAt (peer d i) s).local_index = receiver ∧
    CanRecv (kpAt (peer d i) s) d'.now.val ∧
    (∃ S, (kpAt (peer d i) s).replay.Inv S ∧ counter.val ∉ S ∧
      ∃ kp' : Keypair, kp'.replay.Inv (insert counter.val S) ∧
        (kp' = kpAt (peer d' i) 0 ∨ kp' = kpAt (peer d' i) s) ∧ kp'.recv = (kpAt (peer d i) s).recv) ∧
    P.aead (kpAt (peer d i) s).recv counter.val [] (out'.take (body.length - 16)) = body ∧
    ∃ ip, Inner.Spec (out'.take (body.length - 16)) ip ∧
      (∃ e, allowed_ips.Longest d.allowed_ips ip.v6 ip.src.val e ∧ e.peer.val = i) ∧ ip.len = n

/-- **Spec theorem for `Device::on_transport`**: delivers a transport message
    only as `Delivered` says; sends nothing. -/
@[step]
theorem Device.on_transport.spec (d : Device) (hd : d.Inv) (now : U64) (hnow : now = d.now)
    (src : Endpoint) (receiver : U32) (counter : U64) (body out : Slice U8) :
    Device.on_transport inst d c now src receiver counter body out
      ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
        d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
          d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
          match a with
          | .None => True
          | .Send _ _ => False
          | .Deliver n => ∃ i < d.peer_count.val, ∃ s,
              Delivered P d d' i s receiver counter body.val out'.val n ⦄ := by
  have hc := hd.1
  unfold Device.on_transport
  step as ⟨i, hi1, hi2, _hi3⟩
  split
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl, trivial⟩
  have hlt : i.val < d.peer_count.val := by scalar_tac
  have hi16 : i.val < 512 := by omega
  step as ⟨p, hp⟩
  rw [index_peer d i (by simp; omega)] at hp
  step as ⟨slot, hslot⟩
  have hs3 : slotOf p receiver ≠ 3 := hp ▸ hi2 hlt
  have hfound := slotOf_found hs3
  have hslt : slot.val < 3 := by have := slotOf_le p receiver; omega
  step as ⟨kp, hkp⟩
  step as ⟨b, hb⟩
  split
  swap
  · simp only [WP.spec_ok]; exact ⟨hd, rfl, rfl, rfl, rfl, trivial⟩
  rename_i hbt
  have hcr : CanRecv kp now.val := by simpa [hbt] using hb
  have hpinv : p.Inv := hp ▸ hd.2.2.1 i.val hi16
  obtain ⟨S, hS⟩ := hkp ▸ kpAt_inv hpinv slot.val
  step as ⟨i1, hi1v⟩
  have hi1 : i1.val = i.val := by
    rw [hi1v, UScalar.cast_val_eq]; simp only [UScalarTy.U16_numBits_eq]; scalar_tac
  step with transport.receive.spec (inst := inst) (c := c) (P := P) kp.recv kp.replay S hS
      d.allowed_ips hd.2.1 i1 counter body out
    as ⟨r, r1, out1, acc, hacc, hwin, hol, hauth, hr⟩
  step as ⟨p1, hp1⟩
  have hkp' : kp = kpAt (peer d i.val) slot.val := by rw [hkp, hp]
  have hp1idx : p1.idx = p.idx := by rw [hp1, hkp]; exact setKpAt_idx p slot.val r1
  have hp1inv : p1.Inv := by
    rw [hp1]; exact setKpAt_inv hpinv _ ⟨_, hwin⟩
  have hp1ia : p1.initiation_at = p.initiation_at := by rw [hp1]; exact (setKpAt_fields _ _ _).1
  have hp1hs : p1.handshake = p.handshake := by rw [hp1]; exact (setKpAt_fields _ _ _).2
  have hia : p.initiation_at.val ≤ d.now.val := hp ▸ hd.2.2.2.2 _ hi16
  -- The two shapes of the peer afterwards: the same keypairs, or moved on.
  have hstep : ∀ q : Peer, q.handshake = p1.handshake → q.initiation_at = p1.initiation_at →
      ((q.current = p1.current ∧ q.previous = p1.previous ∧ q.next = p1.next) ∨
        (∃ e : Keypair, e.valid = false ∧ KpInv e ∧
          q.current = p1.next ∧ q.previous = p1.current ∧ q.next = e)) →
      Device.Inv { d with peers := d.peers.set i q } := by
    intro q hq1 hq2 hq
    rcases hq with ⟨e1, e2, e3⟩ | ⟨e, he1, he2, e1, e2, e3⟩
    · apply hd.replace_perm hlt q id (fun _ _ h => h)
      · intro s x hx
        rw [← hp, show q.idx = p1.idx from idx_eq_of hq1 e1 e2 e3, hp1idx] at *
        exact hx
      · exact inv_of hp1inv e1 e2 e3
      · rw [hq2, hp1ia]; exact hia
    · apply hd.replace_perm hlt q rotSlot rotSlot_inj
      · intro s x hx
        rw [← hp, ← hp1idx]
        rw [show q.idx = (rotated p1 e).idx from idx_eq_of hq1 e1 e2 e3] at hx
        exact rotated_idx p1 e he1 s x hx
      · exact inv_of (rotated_inv hp1inv he2) e1 e2 e3
      · rw [hq2, hp1ia]; exact hia
  rcases r with _ | _ | n <;> simp only []
  · -- Dropped: only the window may have moved.
    step as ⟨a, ha⟩
    refine ⟨?_, hol⟩
    rw [ha]; exact hstep p1 rfl rfl (Or.inl ⟨rfl, rfl, rfl⟩)
  · -- A keepalive.
    step with rotate_or p1 (slot = 2#u8) as ⟨p2, hp2⟩
    step as ⟨a, ha⟩
    refine ⟨?_, hol⟩
    rw [ha]
    rcases hp2 with ⟨-, rfl⟩ | ⟨-, k, hk1, hk2, rfl⟩
    · exact hstep _ rfl rfl (Or.inl ⟨rfl, rfl, rfl⟩)
    · exact hstep _ rfl rfl (Or.inr ⟨k, hk1, hk2, rfl, rfl, rfl⟩)
  · -- A packet.
    obtain ⟨hacct, ip, hip, ⟨e, he, hpe⟩, hlen⟩ := hr
    step with rotate_or { p1 with last_received := now, keepalive_due := true } (slot = 2#u8)
      as ⟨p2, hp2⟩
    step as ⟨a, ha⟩
    have hpd := fun j => peer_replace (d' := { d with peers := a }) d (i := i) j hi16 ha
    have hkp1 : kpAt p1 slot.val = { kp with replay := r1 } := by
      rw [hp1]; exact kpAt_setKpAt _ _ _ hslt
    subst hnow
    refine ⟨?_, hol, i.val, hlt, slot.val, hslt, by rw [← hkp', hkp, hslot]; exact hfound.1,
      by rw [← hkp', hkp, hslot]; exact hfound.2, by rw [← hkp']; exact hcr,
      ⟨S, by rw [← hkp']; exact hS, (hacc.mp hacct).2.2.2.2, { kp with replay := r1 },
        by simpa [hacct] using hwin, ?_, by rw [← hkp']⟩,
      by rw [← hkp']; exact hauth hacct, ip, hip, ⟨e, he, by rw [hpe, hi1]⟩, hlen⟩
    · rw [ha]
      rcases hp2 with ⟨-, rfl⟩ | ⟨-, k, hk1, hk2, rfl⟩
      · exact hstep _ rfl rfl (Or.inl ⟨rfl, rfl, rfl⟩)
      · exact hstep _ rfl rfl (Or.inr ⟨k, hk1, hk2, rfl, rfl, rfl⟩)
    · rw [hpd, if_pos rfl]
      rcases hp2 with ⟨hs2, rfl⟩ | ⟨hs2, k, hk1, hk2, rfl⟩
      · right; rw [← hkp1]; unfold kpAt; split_ifs <;> rfl
      · left
        have : slot.val = 2 := by rw [hs2]; rfl
        rw [← hkp1, this]; simp [kpAt, rotated, hp1, setKpAt_two]
omit h in
theorem withSecret_peer (d : Device) (a : Array U8 32#usize) (b : Bool) (t : U64) (j : Nat) :
    peer (withSecret d a b t) j = peer d j := rfl

/-- The slots the peer's indices come from when a response completes its
    handshake: the handshake's becomes current, the current previous. -/
def respSlot : Slot → Slot
  | .hs => .prev
  | .cur => .hs
  | .prev => .cur
  | .next => .next

omit h in
theorem respSlot_inj : ∀ s t, respSlot s = respSlot t → s = t := by
  intro s t h; cases s <;> cases t <;> simp_all [respSlot]

/-- Device `d'` handled the response `msg`, whose bytes have a valid `mac1`,
    by completing the handshake in flight it answers per the paper, and sent
    `out'[..n]` to `e` to confirm the new session: a keepalive under it (or,
    in principle, an initiation). -/
def Confirmed (P : Primitives) (d d' : Device) (env : Env) (now : U64) (bytes : List U8)
    (msg : message.Response) (e : Endpoint) (n : Usize) (out' : List U8) : Prop :=
  cookie.Spec.mac1Valid P bytes d.mac1_key ∧
    ∃ i < d.peer_count.val, HasHandshake (peer d i) msg.receiver ∧
      ∃ chain, noise.Spec.consumeResponse P (peer d i).handshake.state d.private
        (peer d i).psk msg = some chain ∧
      ∃ dm : Device, (peer dm i).current.send = (noise.Spec.transportKeys P chain).1 ∧
        (peer dm i).current.counter.val = 0 ∧ e = (peer d' i).endpoint ∧
        ((n.val = 148 ∧ InitSent P dm d' i env now (out'.take 148)) ∨
          DataSent P dm d' i now [] n out')

/-- **Spec theorem for `Device::on_response`**: a response to our handshake
    in flight, whose `mac1` (and under load `mac2`) is valid and which
    completes the handshake per the paper, makes a new current session, which
    a keepalive then confirms; or a cookie reply is sent back. -/
@[step]
theorem Device.on_response.spec (d : Device) (hd : d.Inv) (env : Env) (now : U64)
    (hnow : now = d.now) (src : Endpoint) (under_load : Bool) (bytes : Slice U8)
    (msg : message.Response) (out : Slice U8) :
    Device.on_response inst d c env now src under_load bytes msg out
      ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
        d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
          d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
          match a with
          | .None => True
          | .Deliver _ => False
          | .Send e n => (n.val = 64 ∧ e = src) ∨
              Confirmed P d d' env now bytes.val msg e n out'.val ⦄ := by
  have hc := hd.1
  unfold Device.on_response
  step as ⟨r, d1, out1, hr, hol1, hd1, hmac⟩
  have hinv1 : d1.Inv := by rw [hd1]; exact hd.withSecret _ _ _
  have hq : d1.peers = d.peers ∧ d1.peer_count = d.peer_count ∧ d1.now = d.now ∧
      d1.allowed_ips = d.allowed_ips ∧ d1.private = d.private ∧ d1.public = d.public := by
    rw [hd1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hpe1, hcnt1, hnow1, hai1, hpriv1, hpub1⟩ := hq
  have hpd1 : ∀ j, peer d1 j = peer d j := fun j => by simp only [peer, hpe1]
  clear hd1
  split
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, Or.inl ⟨by simp, rfl⟩⟩
  rename_i hr2
  split
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  rename_i hr0
  have hr0' : r.val = 0 := by
    have : ¬ (r != 0#u8) = true := hr0
    simp at this; rw [this]
  obtain ⟨hm1, -⟩ := hmac hr0'
  have hc1 : d1.peer_count.val ≤ 512 := hinv1.1
  step as ⟨i, hi1, hi2, _hi3⟩
  split
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  have hlt : i.val < d1.peer_count.val := by scalar_tac
  have hi16 : i.val < 512 := by omega
  step as ⟨p, hp⟩
  rw [index_peer d1 i (by simp; omega)] at hp
  step as ⟨o, ho⟩
  rcases o with _ | chain
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  step as ⟨send, recv, hkeys⟩
  step as ⟨rp, hrp⟩
  step as ⟨k, hk1, hk2⟩
  step as ⟨a1, ha1⟩
  have hhs : HasHandshake p msg.receiver := hp ▸ hi2 hlt
  have hpinv : p.Inv := hp ▸ hinv1.2.2.1 i.val hi16
  have hdm : Device.Inv { d1 with peers := a1 } := by
    rw [ha1]
    apply hinv1.replace_perm hlt _ respSlot respSlot_inj
    · intro s x hx
      rw [← hp]
      cases s <;> simp only [Peer.idx, respSlot] at hx ⊢
      · simp at hx
      · simp at hx; rw [hhs.1, ← hx, hhs.2]; simp
      · exact hx
      · simp [hk1] at hx
    · exact ⟨⟨_, hrp⟩, hpinv.1, hk2⟩
    · exact hp ▸ hinv1.2.2.2.2 _ hi16
  have hpd := fun j => peer_replace (d' := { d1 with peers := a1 }) d1 (i := i) j hi16 ha1
  step with Device.send_keepalive.spec (inst := inst) (c := c) (P := P) _ hdm env now
      (by rw [hnow1]; exact hnow) i hlt out1
    as ⟨a, d', out', h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨h1, by rw [h2]; exact hcnt1, by rw [h3]; exact hnow1, by rw [h4]; exact hai1,
    by rw [h5]; exact hol1, ?_⟩
  cases a with
  | None => trivial
  | Deliver n => exact h8
  | Send e n =>
    obtain ⟨he, hs⟩ := h8
    refine Or.inr ⟨hm1, i.val, by rw [← hcnt1]; exact hlt, by rw [← hpd1, ← hp]; exact hhs,
      chain, by rw [← hpd1, ← hp, ← hpriv1]; exact ho.symm, { d1 with peers := a1 }, ?_, ?_, he, hs⟩
    · rw [hpd, if_pos rfl]; simp only; rw [← hkeys]
    · rw [hpd, if_pos rfl]; rfl

/-- Device `d'` answered the initiation `msg` from peer `i` with the response
    `bytes`: the initiation is the paper's from that (configured) peer's static key, its
    timestamp is later than the peer's previous one (and is now the latest),
    and the response is the paper's (with its MACs), whose session is now the
    peer's next one, with the new local index. -/
def Answered (P : Primitives) (d d' : Device) (i : Nat) (env : Env) (msg : message.Initiation)
    (bytes : List U8) : Prop :=
  ∃ st, noise.Spec.consumeInitiationStatic P d.private d.public msg = some st ∧
    (peer d i).enabled = true ∧ (peer d i).public = st.initiator_static ∧
    ∃ chain ts, noise.Spec.consumeInitiationTimestamp P d.private st msg = some (chain, ts) ∧
      noise.Spec.after ts.val (peer d i).last_timestamp.val = true ∧
      (peer d' i).last_timestamp = ts ∧
      ∃ resp chain', noise.Spec.createResponse P chain msg.ephemeral st.initiator_static
          (peer d i).psk env.ephemeral env.index msg.sender = some (resp, chain') ∧
        (peer d' i).next.valid = true ∧ (peer d' i).next.local_index = env.index ∧
        (peer d' i).next.send = (noise.Spec.transportKeys P chain').2 ∧
        (peer d' i).next.recv = (noise.Spec.transportKeys P chain').1 ∧
        ∃ enc tau, message.Message.Spec enc (.Response resp) ∧
          bytes = cookie.Spec.withMacs P enc (peer d i).mac1_key tau

/-- **Spec theorem for `Device::on_initiation`**: answers an initiation with
    a valid `mac1` (and under load `mac2`) only as `Answered` says, or sends a
    cookie reply. -/
@[step]
theorem Device.on_initiation.spec (d : Device) (hd : d.Inv) (env : Env) (now : U64)
    (hnow : now = d.now) (src : Endpoint) (under_load : Bool) (bytes : Slice U8)
    (msg : message.Initiation) (out : Slice U8) :
    Device.on_initiation inst d c env now src under_load bytes msg out
      ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
        d'.Inv ∧ d'.peer_count = d.peer_count ∧ d'.now = d.now ∧
          d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
          match a with
          | .None => True
          | .Deliver _ => False
          | .Send e n => e = src ∧ (n.val = 64 ∨
              (n.val = 92 ∧ cookie.Spec.mac1Valid P bytes.val d.mac1_key ∧
                ∃ i < d.peer_count.val, Answered P d d' i env msg (out'.val.take 92))) ⦄ := by
  have hc := hd.1
  unfold Device.on_initiation
  step as ⟨r, d1, out1, hr, hol1, hd1, hmac⟩
  have hinv1 : d1.Inv := by rw [hd1]; exact hd.withSecret _ _ _
  have hq : d1.peers = d.peers ∧ d1.peer_count = d.peer_count ∧ d1.now = d.now ∧
      d1.allowed_ips = d.allowed_ips ∧ d1.private = d.private ∧ d1.public = d.public := by
    rw [hd1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hpe1, hcnt1, hnow1, hai1, hpriv1, hpub1⟩ := hq
  have hpd1 : ∀ j, peer d1 j = peer d j := fun j => by simp only [peer, hpe1]
  clear hd1
  split
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, rfl, Or.inl (by simp)⟩
  split
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  rename_i hr0
  have hr0' : r.val = 0 := by
    have : ¬ (r != 0#u8) = true := hr0
    simp at this; rw [this]
  obtain ⟨hm1, -⟩ := hmac hr0'
  have hc1 : d1.peer_count.val ≤ 512 := hinv1.1
  step as ⟨o, ho⟩
  rcases o with _ | st
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  step as ⟨i, hi1, hi2, _hi3⟩
  split
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  have hlt : i.val < d1.peer_count.val := by scalar_tac
  have hi16 : i.val < 512 := by omega
  step as ⟨used, hused⟩
  split
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  rename_i hused'
  step as ⟨p, hp⟩
  rw [index_peer d1 i (by simp; omega)] at hp
  step as ⟨o1, ho1⟩
  rcases o1 with _ | ⟨chain, ts⟩
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  step as ⟨b1, hb1⟩
  split
  swap
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  rename_i hb1t
  step as ⟨o2, ho2⟩
  rcases o2 with _ | ⟨resp, chain'⟩
  · simp only [WP.spec_ok]
    exact ⟨hinv1, hcnt1, hnow1, hai1, hol1, trivial⟩
  step*
  rename_i hb2
  have hk : p1.current = p.current ∧ p1.previous = p.previous ∧ p1.next = p.next ∧
      p1.handshake = p.handshake ∧ p1.mac1_key = p.mac1_key ∧ p1.initiation_at = p.initiation_at := by
    rw [p1_post]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpinv : p.Inv := hp ▸ hinv1.2.2.1 i.val hi16
  have hfresh : ∀ j < d1.peer_count.val, ¬ Uses (peer d1 j) env.index :=
    fun j hj hu => hused' (hused.mpr ⟨j, hj, hu⟩)
  have hpd := fun j => peer_replace (d' := { d1 with peers := a1 }) d1 (i := i) j hi16 a1_post
  have hlen92 : (cookie.Spec.withMacs P s.val p.mac1_key tau).length = 92 := by
    have : s.val.length = 92 := by rw [s_post]; simp
    cases tau <;> simp [cookie.Spec.withMacs, Array.property, this]
  refine ⟨?_, hcnt1, hnow1, hai1, by rw [b2_post, hol1], ?_⟩
  · rw [a1_post]
    apply hinv1.replace_fresh hlt _ env.index hfresh id (fun _ _ h => h) .next
    · intro s x hx
      cases s
      · left; rw [← hp]; simpa [Peer.idx, hk.2.2.2.1] using hx
      · left; rw [← hp]; simpa [Peer.idx, hk.1] using hx
      · left; rw [← hp]; simpa [Peer.idx, hk.2.1] using hx
      · right; simp [Peer.idx] at hx; exact ⟨hx.symm, rfl⟩
    · exact ⟨hk.1 ▸ hpinv.1, hk.2.1 ▸ hpinv.2.1, ⟨∅, r2_post⟩⟩
    · rw [hk.2.2.2.2.2, hp]; exact hinv1.2.2.2.2 _ hi16
  · refine Or.inr ⟨by simp, hm1, i.val, by rw [← hcnt1]; exact hlt, ?_⟩
    unfold Answered
    rw [← hpd1, ← hp, ← hpriv1, ← hpub1]
    refine ⟨st, ho.symm, hp ▸ (hi2 hlt).1, hp ▸ (hi2 hlt).2, chain, ts, ho1.symm, by rw [← hb1]; exact hb1t, ?_,
      resp, chain', ho2.symm, ?_, ?_, ?_, ?_, bytes1.val, tau, bytes1_post, ?_⟩
    · rw [hpd, if_pos rfl]
    · rw [hpd, if_pos rfl]
    · rw [hpd, if_pos rfl]
    · rw [hpd, if_pos rfl]; exact congrArg Prod.snd recv_post
    · rw [hpd, if_pos rfl]; exact congrArg Prod.fst recv_post
    · have hb2 : b2 = true := by assumption
      rw [b2_post3 hb2, b2_post1, List.take_left' hlen92, s_post]

/-- What `handle_datagram` may send in answer to the message `m`. -/
def Answer (P : Primitives) (d d' : Device) (env : Env) (src : Endpoint) (bytes : List U8)
    (m : message.Message) (e : Endpoint) (n : Usize) (out' : List U8) : Prop :=
  match m with
  | .Initiation msg => e = src ∧ (n.val = 64 ∨ (n.val = 92 ∧
      cookie.Spec.mac1Valid P bytes d.mac1_key ∧
      ∃ i < d.peer_count.val, Answered P d d' i env msg (out'.take 92)))
  | .Response msg => (n.val = 64 ∧ e = src) ∨ Confirmed P d d' env d'.now bytes msg e n out'
  | _ => False

/-- **Spec theorem for `Device::handle_datagram`**: a datagram from `src`.
    Whatever is sent is a cookie reply or an answer to a well-formed
    handshake message, as `Answer` says; whatever is delivered is a packet
    from a well-formed transport message, as `Delivered` says. -/
@[step]
theorem Device.handle_datagram.spec (d : Device) (hd : d.Inv) (env : Env) (src : Endpoint)
    (under_load : Bool) (bytes out : Slice U8) :
    Device.handle_datagram inst d c env src under_load bytes out
      ⦃ (a : Action) (d' : Device) (out' : Slice U8) =>
        d'.Inv ∧ d'.now.val = max env.now.val d.now.val ∧ d'.peer_count = d.peer_count ∧
          d'.allowed_ips = d.allowed_ips ∧ out'.length = out.length ∧
          match a with
          | .None => True
          | .Deliver n => ∃ t, message.Message.Spec bytes.val (.Transport t) ∧
              ∃ i < d.peer_count.val, ∃ s, Delivered P d d' i s t.header.receiver t.header.counter
                (bytes.val.drop 16) out'.val n
          | .Send e n => ∃ m, message.Message.Spec bytes.val m ∧
              Answer P d d' env src bytes.val m e n out'.val ⦄ := by
  unfold Device.handle_datagram
  step as ⟨now, d1, hnow, hd1, hle⟩
  have hinv1 : d1.Inv := hd1 ▸ hd.clock now hle
  subst hd1
  simp only [Untrusted.validate_eq]
  step as ⟨u, hu⟩
  step as ⟨res, hres⟩
  rw [hu] at hres
  rcases res with m | err
  swap
  · simp only [WP.spec_ok]; exact ⟨hinv1, hnow, rfl, rfl, rfl, trivial⟩
  rcases m with msg | msg | msg | t
  · step with Device.on_initiation.spec (inst := inst) (c := c) (P := P) _ hinv1 env now rfl src
        under_load bytes msg out
      as ⟨a, d', out', h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, by rw [h3]; exact hnow, h2, h4, h5, ?_⟩
    cases a with
    | None => trivial
    | Deliver n => exact (show False from h6).elim
    | Send e n => exact ⟨_, hres, h6⟩
  · step with Device.on_response.spec (inst := inst) (c := c) (P := P) _ hinv1 env now rfl src
        under_load bytes msg out
      as ⟨a, d', out', h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, by rw [h3]; exact hnow, h2, h4, h5, ?_⟩
    cases a with
    | None => trivial
    | Deliver n => exact (show False from h6).elim
    | Send e n =>
      refine ⟨_, hres, ?_⟩
      have h3' : d'.now = now := h3
      simp only [Answer]; rw [h3']; exact h6
  · step with Device.on_cookie_reply.spec (inst := inst) (c := c) (P := P) _ hinv1 now msg
      as ⟨a, d', h1, h2, h3, h4, h5⟩
    subst h5
    refine ⟨h1, by rw [h3]; exact hnow, h2, h4, ?_⟩
    simp
  · step as ⟨s, hs, hsl⟩
    step with Device.on_transport.spec (inst := inst) (c := c) (P := P) _ hinv1 now rfl src
        t.header.receiver t.header.counter s out
      as ⟨a, d', out', h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, by rw [h3]; exact hnow, h2, h4, h5, ?_⟩
    cases a with
    | None => trivial
    | Send e n => exact h6.elim
    | Deliver n =>
      obtain ⟨i, hi, sl, hdel⟩ := h6
      refine ⟨t, hres, i, hi, sl, ?_⟩
      have hs' : s.val = bytes.val.drop 16 := by rw [hs]; simp
      rw [hs'] at hdel; exact hdel

end
end wireguard.device
