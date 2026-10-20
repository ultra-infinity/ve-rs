/- The WireGuard handshake (whitepaper sections 5.4.2 to 5.4.5), transcribed
   over the abstract primitives. `NoiseTop.lean` proves that
   `wireguard::noise` computes exactly these functions.

   Each definition follows the paper line by line; the comments give the
   paper's notation. `C` is the chaining key, `H` the hash, `S` static keys,
   `E` ephemeral keys, `Q` the pre-shared key. -/
import Wireguard.Crypto

open Aeneas Aeneas.Std Result

namespace wireguard.noise.Spec

open wireguard.crypto

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List U8 := s.toList.map fun ch => ⟨BitVec.ofNat 8 ch.toNat⟩

/-- The Noise protocol name. -/
def construction : List U8 := ascii "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s"

/-- WireGuard's Noise prologue. -/
def identifier : List U8 := ascii "WireGuard v1 zx2c4 Jason@zx2c4.com"

/-- An all-zero Diffie-Hellman result, which a small-order public key gives
    and every step must reject. -/
def zeros32 : List U8 := List.replicate 32 0#u8

/-- The zero MAC fields: MACs are computed over the encoded message later. -/
def zeros16 : Array U8 16#usize := Array.repeat 16#usize 0#u8

section
variable (P : Primitives)

open Classical in
/-- AEAD decryption: the unique plaintext that `ct` encrypts, if any. -/
noncomputable def aeadOpen (k : Key) (n : Nat) (ad ct : List U8) : Option (List U8) :=
  if h : ∃ m, P.aead k n ad m = ct then some h.choose else none

/-- `C = Hash(CONSTRUCTION)`, `H = Hash(Hash(C ‖ IDENTIFIER) ‖ S_r^pub)`. -/
def initialChain (sr : Key) : Chain :=
  let key := P.hash construction
  { key, hash := P.hash ((P.hash (key.val ++ identifier)).val ++ sr.val) }

/-- The initiator's message and kept state (section 5.4.2). -/
def createInitiation (siPriv siPub srPub eiPriv : Key) (sender : U32)
    (ts : Array U8 12#usize) : Option (message.Initiation × InitiatorState) :=
  let ch := initialChain P srPub
  let eiPub := P.pub eiPriv                                  -- E_i^pub
  let ck := P.kdf1 ch.key eiPub.val                          -- C = KDF1(C, E_i^pub)
  let h := P.hash (ch.hash.val ++ eiPub.val)                 -- H = Hash(H ‖ ephemeral)
  if (P.dh eiPriv srPub).val = zeros32 then none else
  let ck' := P.kdf2 ck (P.dh eiPriv srPub).val               -- (C, κ) = KDF2(C, DH(E_i, S_r))
  let encS := P.aead ck'.2 0 h.val siPub.val                 -- static = AEAD(κ, 0, S_i^pub, H)
  let h := P.hash (h.val ++ encS)                            -- H = Hash(H ‖ static)
  if (P.dh siPriv srPub).val = zeros32 then none else
  let ck'' := P.kdf2 ck'.1 (P.dh siPriv srPub).val           -- (C, κ) = KDF2(C, DH(S_i, S_r))
  let encT := P.aead ck''.2 0 h.val ts.val                   -- timestamp = AEAD(κ, 0, T, H)
  let h := P.hash (h.val ++ encT)                            -- H = Hash(H ‖ timestamp)
  some ({ sender, ephemeral := eiPub,
          encrypted_static := Array.from encS (by simp +zetaDelta [P.aead_length]),
          encrypted_timestamp := Array.from encT (by simp +zetaDelta [P.aead_length]),
          mac1 := zeros16, mac2 := zeros16 },
        { chain := { key := ck''.1, hash := h }, ephemeral_private := eiPriv })

/-- The responder's processing of an initiation, up to the initiator's static
    public key (section 5.4.2, receiving side). -/
noncomputable def consumeInitiationStatic (srPriv srPub : Key) (msg : message.Initiation) :
    Option InitiationStatic :=
  let ch := initialChain P srPub
  let ck := P.kdf1 ch.key msg.ephemeral.val
  let h := P.hash (ch.hash.val ++ msg.ephemeral.val)
  if (P.dh srPriv msg.ephemeral).val = zeros32 then none else
  let ck' := P.kdf2 ck (P.dh srPriv msg.ephemeral).val
  match aeadOpen P ck'.2 0 h.val msg.encrypted_static.val with
  | none => none
  | some s =>
    if hs : s.length = 32 then
      some { chain := { key := ck'.1, hash := P.hash (h.val ++ msg.encrypted_static.val) },
             initiator_static := Array.from s hs }
    else none

/-- The rest of the responder's processing, once the initiator is known: the
    state and the timestamp. -/
noncomputable def consumeInitiationTimestamp (srPriv : Key) (st : InitiationStatic)
    (msg : message.Initiation) : Option (Chain × Array U8 12#usize) :=
  if (P.dh srPriv st.initiator_static).val = zeros32 then none else
  let ck' := P.kdf2 st.chain.key (P.dh srPriv st.initiator_static).val
  match aeadOpen P ck'.2 0 st.chain.hash.val msg.encrypted_timestamp.val with
  | none => none
  | some t =>
    if ht : t.length = 12 then
      some ({ key := ck'.1, hash := P.hash (st.chain.hash.val ++ msg.encrypted_timestamp.val) },
            Array.from t ht)
    else none

/-- The responder's message and final state (section 5.4.3). -/
def createResponse (ch : Chain) (eiPub siPub psk erPriv : Key) (sender receiver : U32) :
    Option (message.Response × Chain) :=
  let erPub := P.pub erPriv                                  -- E_r^pub
  let ck := P.kdf1 ch.key erPub.val                          -- C = KDF1(C, E_r^pub)
  let h := P.hash (ch.hash.val ++ erPub.val)                 -- H = Hash(H ‖ ephemeral)
  if (P.dh erPriv eiPub).val = zeros32 then none else
  let ck := P.kdf1 ck (P.dh erPriv eiPub).val                -- C = KDF1(C, DH(E_r, E_i))
  if (P.dh erPriv siPub).val = zeros32 then none else
  let ck := P.kdf1 ck (P.dh erPriv siPub).val                -- C = KDF1(C, DH(E_r, S_i))
  let r := P.kdf3 ck psk.val                                 -- (C, τ, κ) = KDF3(C, Q)
  let h := P.hash (h.val ++ r.2.1.val)                       -- H = Hash(H ‖ τ)
  let empty := P.aead r.2.2 0 h.val []                       -- empty = AEAD(κ, 0, ε, H)
  some ({ sender, receiver, ephemeral := erPub,
          encrypted_nothing := Array.from empty (by simp +zetaDelta [P.aead_length]),
          mac1 := zeros16, mac2 := zeros16 },
        { key := r.1, hash := P.hash (h.val ++ empty) })     -- H = Hash(H ‖ empty)

/-- The initiator's processing of the response (section 5.4.3, receiving
    side): its final state. -/
noncomputable def consumeResponse (st : InitiatorState) (siPriv psk : Key)
    (msg : message.Response) : Option Chain :=
  let ck := P.kdf1 st.chain.key msg.ephemeral.val
  let h := P.hash (st.chain.hash.val ++ msg.ephemeral.val)
  if (P.dh st.ephemeral_private msg.ephemeral).val = zeros32 then none else
  let ck := P.kdf1 ck (P.dh st.ephemeral_private msg.ephemeral).val
  if (P.dh siPriv msg.ephemeral).val = zeros32 then none else
  let ck := P.kdf1 ck (P.dh siPriv msg.ephemeral).val
  let r := P.kdf3 ck psk.val
  let h := P.hash (h.val ++ r.2.1.val)
  if aeadOpen P r.2.2 0 h.val msg.encrypted_nothing.val = some [] then
    some { key := r.1, hash := P.hash (h.val ++ msg.encrypted_nothing.val) }
  else none

/-- The transport keys (section 5.4.5): `KDF2(C, ε)`, initiator to responder
    first. -/
def transportKeys (ch : Chain) : Key × Key := P.kdf2 ch.key []

end

/-- Whether the byte string `a` comes after `b`, compared byte by byte (for
    TAI64N timestamps, which are big-endian: whether `a` is later). -/
def after : List U8 → List U8 → Bool
  | x :: xs, y :: ys => if x = y then after xs ys else decide (y.val < x.val)
  | _, _ => false


/-! ## Agreement -/

namespace wireguard.noise.Spec

open wireguard.crypto

theorem aeadOpen_seal (P : Primitives) (k : Key) (n : Nat) (ad m : List U8) :
    aeadOpen P k n ad (P.aead k n ad m) = some m := by
  have hex : ∃ m', P.aead k n ad m' = P.aead k n ad m := ⟨m, rfl⟩
  simp only [aeadOpen, hex, ↓reduceDIte, Option.some.injEq]
  exact P.aead_inj _ _ _ _ _ hex.choose_spec

/-- **Agreement.** In an honest run of the handshake, if no Diffie-Hellman
    result is zero, the responder learns the initiator's static public key
    and timestamp, the initiator accepts the response, and both end with the
    same chaining state, hence the same transport keys (`transportKeys`), in
    mirrored roles. -/
theorem honest_run (P : Primitives) (siPriv srPriv eiPriv erPriv psk : Key) (si sr : U32)
    (ts : Array U8 12#usize)
    (h1 : (P.dh eiPriv (P.pub srPriv)).val ≠ zeros32)
    (h2 : (P.dh siPriv (P.pub srPriv)).val ≠ zeros32)
    (h3 : (P.dh erPriv (P.pub eiPriv)).val ≠ zeros32)
    (h4 : (P.dh erPriv (P.pub siPriv)).val ≠ zeros32) :
    ∃ init stI stR chR resp chF,
      createInitiation P siPriv (P.pub siPriv) (P.pub srPriv) eiPriv si ts = some (init, stI) ∧
      consumeInitiationStatic P srPriv (P.pub srPriv) init = some stR ∧
      stR.initiator_static = P.pub siPriv ∧
      consumeInitiationTimestamp P srPriv stR init = some (chR, ts) ∧
      createResponse P chR init.ephemeral stR.initiator_static psk erPriv sr si = some (resp, chF) ∧
      consumeResponse P stI siPriv psk resp = some chF := by
  have c1 := P.dh_comm srPriv eiPriv
  have c2 := P.dh_comm srPriv siPriv
  have c3 := P.dh_comm eiPriv erPriv
  have c4 := P.dh_comm siPriv erPriv
  simp [createInitiation, consumeInitiationStatic, consumeInitiationTimestamp, createResponse,
    consumeResponse, c1, c2, c3, c4, h1, h2, h3, h4, aeadOpen_seal]

end wireguard.noise.Spec
