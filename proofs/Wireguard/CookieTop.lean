/- Specs of `wireguard::cookie`: MACs and cookie replies (whitepaper
   sections 5.4.4 and 5.4.7). -/
import Wireguard.MessageTop
import Wireguard.NoiseSpec

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace wireguard.cookie

open wireguard.crypto

/-! ## The specification -/

namespace Spec

open wireguard.noise.Spec (ascii)

def labelMac1 : List U8 := ascii "mac1----"
def labelCookie : List U8 := ascii "cookie--"

section
variable (P : Primitives)

/-- `HASH(LABEL_MAC1 ‖ S^pub)`. -/
def mac1Key (s : Key) : Key := P.hash (labelMac1 ++ s.val)

/-- `HASH(LABEL_COOKIE ‖ S^pub)`. -/
def cookieKey (s : Key) : Key := P.hash (labelCookie ++ s.val)

/-- The handshake message `msg` with its MACs written into its last 32
    bytes: `msg_α ‖ mac1 ‖ mac2`, where `mac2` is zeros without a cookie. -/
def withMacs (msg : List U8) (k : Key) (cookie : Option (Array U8 16#usize)) : List U8 :=
  let alpha := msg.take (msg.length - 32)
  let mac1 := P.mac k.val alpha
  alpha ++ mac1.val ++
    (match cookie with
     | none => List.replicate 16 0#u8
     | some ck => (P.mac ck.val (alpha ++ mac1.val)).val)

/-- The handshake message `msg` has a valid `mac1` under `k`. -/
def mac1Valid (msg : List U8) (k : Key) : Prop :=
  32 ≤ msg.length ∧
    (msg.drop (msg.length - 32)).take 16 = (P.mac k.val (msg.take (msg.length - 32))).val

/-- The handshake message `msg` has a valid `mac2` under the cookie `ck`. -/
def mac2Valid (msg : List U8) (ck : Array U8 16#usize) : Prop :=
  32 ≤ msg.length ∧
    (msg.drop (msg.length - 16)).take 16 = (P.mac ck.val (msg.take (msg.length - 16))).val

/-- The cookie reply carrying `cookie`, to a message from `receiver` whose
    `mac1` was `mac1`, under the replier's cookie key `ck`. -/
def createCookieReply (ck : Key) (receiver : U32) (nonce : Array U8 24#usize)
    (cookie mac1 : Array U8 16#usize) : message.CookieReply :=
  { receiver, nonce,
    encrypted_cookie := Array.from (P.xaead ck nonce mac1.val cookie.val)
      (by simp [P.xaead_length]) }

open Classical in
/-- XChaCha20-Poly1305 decryption: the unique plaintext `ct` encrypts, if any. -/
noncomputable def xaeadOpen (k : Key) (n : Array U8 24#usize) (ad ct : List U8) :
    Option (List U8) :=
  if h : ∃ m, P.xaead k n ad m = ct then some h.choose else none

/-- The cookie in a reply to a message whose `mac1` was `mac1`, under the
    replier's cookie key `ck`. -/
noncomputable def consumeCookieReply (ck : Key) (msg : message.CookieReply)
    (mac1 : Array U8 16#usize) : Option (Array U8 16#usize) :=
  match xaeadOpen P ck msg.nonce mac1.val msg.encrypted_cookie.val with
  | none => none
  | some c => if h : c.length = 16 then some (Array.from c h) else none

theorem xaeadOpen_some {k : Key} {n : Array U8 24#usize} {ad ct out : List U8}
    (h : P.xaead k n ad out = ct) : xaeadOpen P k n ad ct = some out := by
  have hex : ∃ m, P.xaead k n ad m = ct := ⟨out, h⟩
  simp only [xaeadOpen, hex, ↓reduceDIte, Option.some.injEq]
  exact P.xaead_inj _ _ _ _ _ (hex.choose_spec.trans h.symm)

theorem xaeadOpen_eq {k : Key} {n : Array U8 24#usize} {ad ct out : List U8} {b : Bool}
    (h1 : b = true ↔ ∃ m, P.xaead k n ad m = ct) (h2 : b = true → P.xaead k n ad out = ct) :
    xaeadOpen P k n ad ct = if b then some out else none := by
  cases b
  · simp only [Bool.false_eq_true, false_iff] at h1
    simp [xaeadOpen, h1]
  · simp [xaeadOpen_some P (h2 rfl)]

/-! ### Round trips -/

/-- A message with its MACs added has a valid `mac1`. -/
theorem mac1Valid_withMacs (msg : List U8) (k : Key) (cookie : Option (Array U8 16#usize))
    (h : 32 ≤ msg.length) : mac1Valid P (withMacs P msg k cookie) k := by
  cases cookie <;> simp [mac1Valid, withMacs]

/-- With a cookie, it also has a valid `mac2` under that cookie. -/
theorem mac2Valid_withMacs (msg : List U8) (k : Key) (ck : Array U8 16#usize)
    (h : 32 ≤ msg.length) : mac2Valid P (withMacs P msg k (some ck)) ck := by
  simp only [mac2Valid, withMacs, List.length_append, List.length_take, Array.property]
  refine ⟨by simp, ?_⟩
  have hn : msg.length - 32 + 16 + 16 - 16 = msg.length - 32 + 16 := by omega
  simp [List.drop_append, List.take_append, List.take_take, hn]

/-- A cookie reply opens, for the message it answers, to its cookie. -/
theorem consumeCookieReply_create (ck : Key) (receiver : U32) (nonce : Array U8 24#usize)
    (cookie mac1 : Array U8 16#usize) :
    consumeCookieReply P ck (createCookieReply P ck receiver nonce cookie mac1) mac1 =
      some cookie := by
  simp [consumeCookieReply, createCookieReply, xaeadOpen_some P rfl]

end

end Spec

/-! ## Specs -/

@[simp, scalar_tac_simps] theorem MACS_LEN_val : MACS_LEN.val = 32 := by simp [MACS_LEN]
@[simp, scalar_tac_simps] theorem MAC_LEN_val : crypto.MAC_LEN.val = 16 := by
  simp [crypto.MAC_LEN]

theorem LABEL_MAC1_val : LABEL_MAC1.val = Spec.labelMac1 := by
  simp only [LABEL_MAC1, Array.make]; decide

theorem LABEL_COOKIE_val : LABEL_COOKIE.val = Spec.labelCookie := by
  simp only [LABEL_COOKIE, Array.make]; decide

/-- **Spec theorem for `mac_at`**: the 16 bytes at `pos`. -/
@[step]
theorem mac_at.spec (msg : Slice U8) (pos : Usize) (h : pos.val + 16 ≤ msg.length) :
    mac_at msg pos ⦃ (r : Array U8 16#usize) => r.val = (msg.val.drop pos.val).take 16 ⦄ := by
  unfold mac_at
  step*
  have hu : (u : Slice U8).val = (msg.val.drop pos.val).take 16 := by
    rw [u_post, s_post, i_post, MAC_LEN_val]; simp [List.slice]
  have hl : (u : Slice U8).val.length = 16 := by rw [hu]; simp; scalar_tac
  apply WP.spec_bind
    (UntrustedShared0SliceU8.read_all.spec_of (ArrayU8N.Insts.UntrustedReaderDecode 16#usize) u)
  rintro (m | e) hr
  · obtain ⟨-, -, hv⟩ := hr
    simp only [WP.spec_ok]
    rw [hv, hu]; simp
  · exfalso
    exact hr (Array.from (u : Slice U8).val hl) ⟨by simp [hl], by simp [hl], by simp [hl]⟩

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

/-- **Spec theorem for `mac1_key`**. -/
@[step]
theorem mac1_key.spec (s : Key) : mac1_key inst c s ⦃ (r : Key) => r = Spec.mac1Key P s ⦄ := by
  unfold mac1_key
  step*
  simp_all [Spec.mac1Key, LABEL_MAC1_val]

/-- **Spec theorem for `cookie_key`**. -/
@[step]
theorem cookie_key.spec (s : Key) :
    cookie_key inst c s ⦃ (r : Key) => r = Spec.cookieKey P s ⦄ := by
  unfold cookie_key
  step*
  simp_all [Spec.cookieKey, LABEL_COOKIE_val]

/-- **Spec theorem for `make_cookie`**: `MAC(secret, address)`. -/
@[step]
theorem make_cookie.spec (secret : Key) (address : Slice U8) :
    make_cookie inst c secret address ⦃ (r : Array U8 16#usize) => r = P.mac secret.val address.val ⦄ := by
  unfold make_cookie
  step*

/-- **Spec theorem for `create_cookie_reply`**. -/
@[step]
theorem create_cookie_reply.spec (ck : Key) (receiver : U32) (nonce : Array U8 24#usize)
    (tau mac1 : Array U8 16#usize) :
    create_cookie_reply inst c ck receiver nonce tau mac1 ⦃ (r : message.CookieReply) =>
      r = Spec.createCookieReply P ck receiver nonce tau mac1 ⦄ := by
  unfold create_cookie_reply
  step*
  simp_all [Spec.createCookieReply, Array.eq_iff, Array.from_slice_val, P.xaead_length]

/-- **Spec theorem for `consume_cookie_reply`**. -/
@[step]
theorem consume_cookie_reply.spec (ck : Key) (msg : message.CookieReply) (mac1 : Array U8 16#usize) :
    consume_cookie_reply inst c ck msg mac1 ⦃ (r : Option (Array U8 16#usize)) =>
      r = Spec.consumeCookieReply P ck msg mac1 ⦄ := by
  unfold consume_cookie_reply
  step*
  all_goals (try have hopen := Spec.xaeadOpen_eq P b_post1 b_post2)
  all_goals subst_vars
  all_goals simp_all [Spec.consumeCookieReply, Array.eq_iff, Array.from_slice_val]


/-- **Spec theorem for `check_mac1`**: whether `mac1` is valid. -/
@[step]
theorem check_mac1.spec (msg : Slice U8) (k : Key) :
    check_mac1 inst c msg k ⦃ (r : Bool) => (r = true ↔ Spec.mac1Valid P msg.val k) ⦄ := by
  unfold check_mac1
  step*
  · simp only [Bool.false_eq_true, false_iff, Spec.mac1Valid, not_and]
    intro h32; scalar_tac
  · rw [r_post]
    have hi : i.val = msg.val.length - 32 := by scalar_tac
    simp only [decide_eq_true_eq, Array.eq_iff, expected1_post, a_post, s_post, s1_post, hi,
      Array.val_to_slice, List.slice, List.drop_zero, Nat.sub_zero, Spec.mac1Valid]
    constructor
    · intro h; exact ⟨by scalar_tac, h.symm⟩
    · intro h; exact h.2.symm

/-- **Spec theorem for `add_macs`**: writes the MACs into the last 32 bytes,
    and returns `mac1`. -/
@[step]
theorem add_macs.spec (msg : Slice U8) (k : Key) (tau : Option (Array U8 16#usize))
    (h32 : 32 ≤ msg.length) :
    add_macs inst c msg k tau ⦃ (mac1 : Array U8 16#usize) (msg' : Slice U8) =>
      mac1 = P.mac k.val (msg.val.take (msg.length - 32)) ∧
        msg'.val = Spec.withMacs P msg.val k tau ⦄ := by
  unfold add_macs
  step*
  have hn : msg.length = msg.val.length := rfl
  have hi : i.val = msg.val.length - 32 := by scalar_tac
  -- After the first write: `msg_α ‖ mac1 ‖ (the old last 16 bytes)`.
  have hm1 : mac11 = P.mac k.val (msg.val.take (msg.val.length - 32)) := by
    rw [mac11_post, s_post, s1_post, hi]; simp [List.slice]
  have hmsg1 : msg1.val = (msg.val.take (msg.val.length - 32) ++ mac11.val) ++
      msg.val.drop (msg.val.length - 16) := by
    rw [__post1, s2_post, hi]; simp only [Array.val_to_slice, Array.length_to_slice]
    congr 2; simp; omega
  have hlen : (msg.val.take (msg.val.length - 32) ++ mac11.val).length = msg.val.length - 16 := by
    simp; omega
  have hlen1 : msg1.val.length = msg.val.length := by rw [hmsg1]; simp; omega
  have h16 : msg.val.length - 32 + 16 = msg.val.length - 16 := by omega
  clear __post __post1
  cases tau
  · step*
    refine ⟨by rw [hm1, hn], ?_⟩
    have hi1 : i1.val = msg.val.length - 16 := by scalar_tac
    rw [__post1, s3_post, hi1, hmsg1, List.take_left' hlen]
    simp only [Spec.withMacs, Array.val_to_slice, Array.length_to_slice, ← hn, ← hm1]
    simp [List.drop_append, hlen]
    omega
  · rename_i t
    simp only
    step as ⟨ ts, hts ⟩
    step as ⟨ j, hj, hj1 ⟩
    step as ⟨ beta, hbeta, hbeta1 ⟩
    step as ⟨ m2, hm2 ⟩
    step as ⟨ i1, hi1, hi1' ⟩
    step as ⟨ s3, hs3 ⟩
    step as ⟨ p2, msg2, hp2, hmsg2 ⟩
    refine ⟨by rw [hm1, hn], ?_⟩
    have hbv : beta.val = msg.val.take (msg.val.length - 32) ++ mac11.val := by
      rw [hbeta, hmsg1]; simp only [List.slice, List.drop_zero, Nat.sub_zero]
      rw [show j.val = msg.val.length - 16 by rw [hj, Slice.len_val, MAC_LEN_val],
        List.take_left' hlen]
    rw [hmsg2, hs3, show i1.val = msg.val.length - 16 by rw [hi1, Slice.len_val, MAC_LEN_val],
      hmsg1, List.take_left' hlen,
      hm2, hts, hbv]
    simp only [Spec.withMacs, Array.val_to_slice, Array.length_to_slice, ← hn, ← hm1]
    simp [List.drop_append]
    omega


/-- **Spec theorem for `check_mac2`**: whether `mac2` is valid under `tau`. -/
@[step]
theorem check_mac2.spec (msg : Slice U8) (tau : Array U8 16#usize) :
    check_mac2 inst c msg tau ⦃ (r : Bool) => (r = true ↔ Spec.mac2Valid P msg.val tau) ⦄ := by
  unfold check_mac2
  step*
  · simp only [Bool.false_eq_true, false_iff, Spec.mac2Valid, not_and]
    intro h32; scalar_tac
  · rw [r_post]
    have hi : i.val = msg.val.length - 16 := by scalar_tac
    simp only [decide_eq_true_eq, Array.eq_iff, expected1_post, a_post, s_post, s1_post, hi,
      Array.val_to_slice, List.slice, List.drop_zero, Nat.sub_zero, Spec.mac2Valid]
    constructor
    · intro h; exact ⟨by scalar_tac, h.symm⟩
    · intro h; exact h.2.symm

end

end wireguard.cookie
