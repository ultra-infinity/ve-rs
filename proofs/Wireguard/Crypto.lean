/- The cryptographic primitives as pure functions, the laws a `Crypto`
   implementation is assumed to satisfy, and the specs of HMAC and the KDFs
   built on them.

   `Laws` is a hypothesis of every theorem that uses cryptography, not an
   axiom: the proofs hold for any implementation satisfying it. That the
   libcrux implementation (`crates/wireguard-libcrux`) does is the trust
   assumption, checked there against the RFC test vectors. -/
import Wireguard.Funs
import Untrusted

open Aeneas Aeneas.Std Result

namespace wireguard.crypto

/-- A 32-byte key, hash or Diffie-Hellman result. -/
abbrev Key := Array U8 32#usize

/-- The functions the primitives compute. -/
structure Primitives where
  /-- X25519. -/
  dh : Key → Key → Key
  /-- The X25519 public key of a private key. -/
  pub : Key → Key
  /-- BLAKE2s-256. -/
  hash : List U8 → Key
  /-- Keyed BLAKE2s with a 16-byte output. -/
  mac : Key → List U8 → (Array U8 16#usize)
  /-- ChaCha20-Poly1305 encryption: key, counter, associated data, plaintext. -/
  aead : Key → Nat → List U8 → List U8 → List U8
  /-- XChaCha20-Poly1305 encryption: key, nonce, associated data, plaintext. -/
  xaead : Key → (Array U8 24#usize) → List U8 → List U8 → List U8
  aead_length : ∀ k n ad m, (aead k n ad m).length = m.length + 16
  xaead_length : ∀ k n ad m, (xaead k n ad m).length = m.length + 16
  /-- Encryption is injective in the plaintext (ChaCha20 XORs it with a
      keystream), so a ciphertext has at most one plaintext. -/
  aead_inj : ∀ k n ad m m', aead k n ad m = aead k n ad m' → m = m'
  xaead_inj : ∀ k n ad m m', xaead k n ad m = xaead k n ad m' → m = m'
  /-- X25519 is commutative: both sides of a Diffie-Hellman exchange get the
      same result. -/
  dh_comm : ∀ a b, dh a (pub b) = dh b (pub a)

/-- The laws of the `Crypto` implementation `inst` on the value `c`: each
    method computes one of `P`'s functions and never fails, given buffers of
    the documented lengths. Opening succeeds exactly on the outputs of
    sealing, and then returns what was sealed; ChaCha20-Poly1305 has this
    property since decryption recomputes and checks the tag. -/
class Laws {C : Type} (inst : Crypto C) (c : C) (P : outParam Primitives) : Prop where
  x25519 : ∀ k p out,
    inst.x25519 c k p out = ok (decide ((P.dh k p).val ≠ List.replicate 32 0#u8), P.dh k p)
  x25519_public : ∀ k out, inst.x25519_public c k out = ok (P.pub k)
  hash : ∀ a b out, inst.hash c a b out = ok (P.hash (a.val ++ b.val))
  mac : ∀ k m out, inst.mac c k m out = ok (P.mac k m.val)
  aead_seal : ∀ k (n : U64) ad m (out : Slice U8), out.length = m.length + 16 →
    ∃ out', inst.aead_seal c k n ad m out = ok out' ∧ out'.val = P.aead k n.val ad.val m.val
  aead_open : ∀ k (n : U64) ad ct (out : Slice U8), out.length + 16 = ct.length →
    ∃ b out', inst.aead_open c k n ad ct out = ok (b, out') ∧ out'.length = out.length ∧
      (b = true ↔ ∃ m, P.aead k n.val ad.val m = ct.val) ∧
      (b = true → P.aead k n.val ad.val out'.val = ct.val)
  xaead_seal : ∀ k n ad m (out : Slice U8), out.length = m.length + 16 →
    ∃ out', inst.xaead_seal c k n ad m out = ok out' ∧ out'.val = P.xaead k n ad.val m.val
  xaead_open : ∀ k n ad ct (out : Slice U8), out.length + 16 = ct.length →
    ∃ b out', inst.xaead_open c k n ad ct out = ok (b, out') ∧ out'.length = out.length ∧
      (b = true ↔ ∃ m, P.xaead k n ad.val m = ct.val) ∧
      (b = true → P.xaead k n ad.val out'.val = ct.val)
  ct_eq : ∀ a b, inst.ct_eq c a b = ok (decide (a = b))

/-! ## HMAC and the KDFs -/

/-- A key zero-padded to a BLAKE2s block. -/
def padKey (k : Key) : List U8 := k.val ++ List.replicate 32 0#u8

/-- Every byte of `l` XORed with `b`. -/
def xorAll (l : List U8) (b : U8) : List U8 := l.map (· ^^^ b)

/-- `HMAC(k, m)` over BLAKE2s (RFC 2104 with a 64-byte block). -/
def Primitives.hmac (P : Primitives) (k : Key) (m : List U8) : Key :=
  P.hash (xorAll (padKey k) 0x5c#u8 ++ (P.hash (xorAll (padKey k) 0x36#u8 ++ m)).val)

/-- `KDF1(k, m)`. -/
def Primitives.kdf1 (P : Primitives) (k : Key) (m : List U8) : Key :=
  P.hmac (P.hmac k m) [1#u8]

/-- `KDF2(k, m)`. -/
def Primitives.kdf2 (P : Primitives) (k : Key) (m : List U8) : Key × Key :=
  let t0 := P.hmac k m
  let t1 := P.hmac t0 [1#u8]
  (t1, P.hmac t0 (t1.val ++ [2#u8]))

/-- `KDF3(k, m)`. -/
def Primitives.kdf3 (P : Primitives) (k : Key) (m : List U8) : Key × Key × Key :=
  let t0 := P.hmac k m
  let t1 := P.hmac t0 [1#u8]
  let t2 := P.hmac t0 (t1.val ++ [2#u8])
  (t1, t2, P.hmac t0 (t2.val ++ [3#u8]))

/-! ## Specs -/

@[simp, scalar_tac_simps] theorem BLOCK_LEN_val : BLOCK_LEN.val = 64 := by simp [BLOCK_LEN]
@[simp, scalar_tac_simps] theorem KEY_LEN_val : KEY_LEN.val = 32 := by simp [KEY_LEN]

theorem length_padKey (k : Key) : (padKey k).length = 64 := by simp [padKey]

theorem take_set_succ' (l : List U8) (i : Nat) (x : U8) (h : i < l.length) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := untrusted.take_set_succ l i x h

theorem padKey_lo (k : Key) (i : Nat) (h : i < 32) :
    (padKey k)[i]'(by simp [length_padKey]; omega) = k.val[i]'(by simp; omega) := by
  simp only [padKey]
  exact List.getElem_append_left (by simp; omega)

theorem padKey_hi (k : Key) (i : Nat) (h : 32 ≤ i) (h' : i < 64) :
    (padKey k)[i]'(by simp [length_padKey]; omega) = 0#u8 := by
  simp only [padKey]
  rw [List.getElem_append_right (by simp; omega)]
  exact List.getElem_replicate _

/-- **Spec theorem for the first loop of `hmac`**: writes the inner pad from
    byte `i` on. -/
@[step]
theorem hmac_loop0.spec (key : Key) (pad : Array U8 64#usize) (i : Usize) (hi : i.val ≤ 64) :
    hmac_loop0 key pad i ⦃ (r : Array U8 64#usize) =>
      r.val = pad.val.take i.val ++ (xorAll (padKey key) 0x36#u8).drop i.val ⦄ := by
  unfold hmac_loop0
  split
  · have hlt : i.val < 64 := by scalar_tac
    have hpad : pad.val.length = 64 := by simp
    have hx : (xorAll (padKey key) 0x36#u8).drop i.val =
        ((padKey key)[i.val]'(by simp [length_padKey]; omega) ^^^ 0x36#u8) ::
          (xorAll (padKey key) 0x36#u8).drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [xorAll, length_padKey]; omega)]
      simp [xorAll]
    split
    · step*
      rw [r_post, a_post, Array.set_val_eq, i2_post, take_set_succ' _ _ _ (by simp; omega), hx,
        padKey_lo key i.val (by scalar_tac), ← x_post]
      simp
    · step*
      rw [r_post, a_post, Array.set_val_eq, i2_post, take_set_succ' _ _ _ (by simp; omega), hx]
      have : 32 ≤ i.val := by scalar_tac
      rw [padKey_hi key i.val this (by omega), show (0#u8 ^^^ 54#u8) = 54#u8 by decide]
      simp
  · simp only [WP.spec_ok]
    have : i.val = 64 := by scalar_tac
    simp [this, xorAll, length_padKey]
termination_by 64 - i.val
decreasing_by all_goals scalar_tac

theorem xor_pads (x : U8) : (x ^^^ 0x36#u8) ^^^ (0x36#u8 ^^^ 0x5c#u8) = x ^^^ 0x5c#u8 := by
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  simp only [UScalar.bv_xor]
  rw [BitVec.xor_assoc]
  congr 1

/-- **Spec theorem for the second loop of `hmac`**: XORs every byte from `i`
    on with `0x36 ^ 0x5c`, turning the inner pad into the outer one. -/
@[step]
theorem hmac_loop1.spec (pad : Array U8 64#usize) (i : Usize) (hi : i.val ≤ 64) :
    hmac_loop1 pad i ⦃ (r : Array U8 64#usize) =>
      r.val = pad.val.take i.val ++ (pad.val.drop i.val).map (· ^^^ (0x36#u8 ^^^ 0x5c#u8)) ⦄ := by
  unfold hmac_loop1
  split
  · have hlt : i.val < pad.val.length := by simp; scalar_tac
    step*
    have e1 : i1 = 54#u8 ^^^ 92#u8 := (UScalar.eq_equiv _ _).mpr i1_post
    have e3 : i3 = i2 ^^^ i1 := (UScalar.eq_equiv _ _).mpr i3_post
    rw [r_post, a_post, Array.set_val_eq, i4_post, take_set_succ' _ _ _ hlt,
      List.drop_set_of_lt (by omega), List.drop_eq_getElem_cons hlt, e3, e1, i2_post]
    simp
    rw [List.drop_eq_getElem_cons (l := List.map (fun x => x ^^^ (54#u8 ^^^ 92#u8)) pad.val)
      (i := i.val) (by simpa using hlt)]
    simp
  · simp only [WP.spec_ok]
    have : i.val = 64 := by scalar_tac
    simp [this]
termination_by 64 - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for the loop of `append_byte`**: copies `t[i..]`. -/
@[step]
theorem append_byte_loop.spec (t : Key) (out : Array U8 33#usize) (i : Usize) (hi : i.val ≤ 32) :
    append_byte_loop t out i ⦃ (r : Array U8 33#usize) =>
      r.val = out.val.take i.val ++ t.val.drop i.val ++ out.val.drop 32 ⦄ := by
  unfold append_byte_loop
  split
  · have hlt : i.val < out.val.length := by simp; scalar_tac
    have hlt' : i.val < t.val.length := by simp; scalar_tac
    step*
    rw [r_post, a_post, Array.set_val_eq, i2_post, take_set_succ' _ _ _ hlt,
      List.drop_eq_getElem_cons hlt', i1_post, List.drop_set_of_lt (by scalar_tac)]
    simp
  · simp only [WP.spec_ok]
    have : i.val = 32 := by scalar_tac
    simp [this]
termination_by 32 - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `append_byte`**: `t ‖ b`. -/
@[step]
theorem append_byte.spec (t : Key) (b : U8) :
    append_byte t b ⦃ (r : Array U8 33#usize) => r.val = t.val ++ [b] ⦄ := by
  unfold append_byte
  step*
  rw [r_post]
  simp

/-! ### The laws, as step theorems -/

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

@[step]
theorem Laws.x25519_step (k p out : Key) :
    inst.x25519 c k p out ⦃ (b : Bool) (r : Key) =>
      b = decide ((P.dh k p).val ≠ List.replicate 32 0#u8) ∧ r = P.dh k p ⦄ := by
  rw [Laws.x25519]; simp

@[step]
theorem Laws.x25519_public_step (k out : Key) :
    inst.x25519_public c k out ⦃ (r : Key) => r = P.pub k ⦄ := by
  rw [Laws.x25519_public]; simp

@[step]
theorem Laws.mac_step (k : Key) (m : Slice U8) (out : Array U8 16#usize) :
    inst.mac c k m out ⦃ (r : Array U8 16#usize) => r = P.mac k m.val ⦄ := by
  rw [Laws.mac]; simp

@[step]
theorem Laws.ct_eq_step (a b : Array U8 16#usize) :
    inst.ct_eq c a b ⦃ (r : Bool) => r = decide (a = b) ⦄ := by
  rw [Laws.ct_eq]; simp

@[step]
theorem Laws.aead_seal_step (k : Key) (n : U64) (ad m out : Slice U8)
    (h : out.length = m.length + 16) :
    inst.aead_seal c k n ad m out ⦃ (r : Slice U8) => r.val = P.aead k n.val ad.val m.val ⦄ := by
  obtain ⟨out', h1, h2⟩ := Laws.aead_seal (inst := inst) (c := c) k n ad m out h
  rw [h1]; simpa using h2

@[step]
theorem Laws.aead_open_step (k : Key) (n : U64) (ad ct out : Slice U8)
    (h : out.length + 16 = ct.length) :
    inst.aead_open c k n ad ct out ⦃ (b : Bool) (r : Slice U8) =>
      r.length = out.length ∧ (b = true ↔ ∃ m, P.aead k n.val ad.val m = ct.val) ∧
      (b = true → P.aead k n.val ad.val r.val = ct.val) ⦄ := by
  obtain ⟨b, out', h1, h2⟩ := Laws.aead_open (inst := inst) (c := c) k n ad ct out h
  rw [h1]; simpa using h2

@[step]
theorem Laws.xaead_seal_step (k : Key) (n : Array U8 24#usize) (ad m out : Slice U8)
    (h : out.length = m.length + 16) :
    inst.xaead_seal c k n ad m out ⦃ (r : Slice U8) => r.val = P.xaead k n ad.val m.val ⦄ := by
  obtain ⟨out', h1, h2⟩ := Laws.xaead_seal (inst := inst) (c := c) k n ad m out h
  rw [h1]; simpa using h2

@[step]
theorem Laws.xaead_open_step (k : Key) (n : Array U8 24#usize) (ad ct out : Slice U8)
    (h : out.length + 16 = ct.length) :
    inst.xaead_open c k n ad ct out ⦃ (b : Bool) (r : Slice U8) =>
      r.length = out.length ∧ (b = true ↔ ∃ m, P.xaead k n ad.val m = ct.val) ∧
      (b = true → P.xaead k n ad.val r.val = ct.val) ⦄ := by
  obtain ⟨b, out', h1, h2⟩ := Laws.xaead_open (inst := inst) (c := c) k n ad ct out h
  rw [h1]; simpa using h2

@[step]
theorem Laws.hash_step (a b : Slice U8) (out : Key) :
    inst.hash c a b out ⦃ (r : Key) => r = P.hash (a.val ++ b.val) ⦄ := by
  rw [Laws.hash]; simp

/-- **Spec theorem for `hmac`**: `HMAC(key, msg)`. -/
@[step]
theorem hmac.spec (key : Key) (msg : Slice U8) :
    hmac inst c key msg ⦃ (r : Key) => r = P.hmac key msg.val ⦄ := by
  unfold hmac
  step*
  rw [r_post, s1_post, s2_post, inner1_post, s_post]
  simp only [Array.val_to_slice, pad2_post, pad1_post, List.take_zero, List.drop_zero,
    List.nil_append, Primitives.hmac, xorAll, List.map_map]
  congr 2
  apply List.map_congr_left
  intro x _
  exact xor_pads x

/-- **Spec theorem for `kdf1`**. -/
@[step]
theorem kdf1.spec (key : Key) (input : Slice U8) :
    kdf1 inst c key input ⦃ (r : Key) => r = P.kdf1 key input.val ⦄ := by
  unfold kdf1
  step*
  simp_all [Primitives.kdf1, Array.make]

/-- **Spec theorem for `kdf2`**. -/
@[step]
theorem kdf2.spec (key : Key) (input : Slice U8) :
    kdf2 inst c key input ⦃ (r : Key × Key) => r = P.kdf2 key input.val ⦄ := by
  unfold kdf2
  step*
  simp_all [Primitives.kdf2, Array.make]

/-- **Spec theorem for `kdf3`**. -/
@[step]
theorem kdf3.spec (key : Key) (input : Slice U8) :
    kdf3 inst c key input ⦃ (r : Key × Key × Key) => r = P.kdf3 key input.val ⦄ := by
  unfold kdf3
  step*
  simp_all [Primitives.kdf3, Array.make]

end

end wireguard.crypto
