/- Specs of `wireguard::transport`: sealing an IP packet into a transport
   message, and opening one, as the WireGuard paper (section 5.4.6)
   describes; the inner packets are checked with the verified `net`
   decoders. -/
import Wireguard.MessageTop
import Wireguard.NoiseTop
import Wireguard.ReplayTop
import Wireguard.AllowedIpsTop
import Net.Ipv4Top
import Net.Ipv6Top

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace wireguard.message

/-! ## The transport header -/

theorem foldl_beNat (acc : Nat) (b : List U8) :
    b.foldl (fun acc x => acc * 256 + x.val) acc = acc * 256 ^ b.length + beNat b := by
  induction b generalizing acc with
  | nil => simp [beNat]
  | cons x t ih =>
    have h2 : beNat (x :: t) = x.val * 256 ^ t.length + beNat t := by
      show List.foldl _ (0 * 256 + x.val) t = _
      rw [ih]; simp
    rw [List.foldl_cons, ih, h2, List.length_cons, pow_succ]
    ring

theorem beNat_append (a b : List U8) : beNat (a ++ b) = beNat a * 256 ^ b.length + beNat b := by
  show List.foldl _ 0 (a ++ b) = _
  rw [List.foldl_append]
  exact foldl_beNat _ _

theorem leNat_append (a b : List U8) : leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b := by
  simp only [leNat, List.reverse_append, beNat_append, List.length_reverse]
  ring

/-- **Spec theorem for `put_u64`**: writes the 8 bytes of `v`, least
    significant first, at `pos`. -/
@[step]
theorem put_u64.spec (out : Slice U8) (pos : Usize) (v : U64) (h : pos.val + 8 ≤ out.length) :
    put_u64 out pos v ⦃ (pos' : Usize) (out' : Slice U8) =>
      pos'.val = pos.val + 8 ∧ ∃ w : List U8, w.length = 8 ∧ leNat w = v.val ∧
        out'.val = out.val.take pos.val ++ w ++ out.val.drop (pos.val + 8) ⦄ := by
  unfold put_u64
  have hol : pos.val + 8 ≤ out.val.length := by simpa [Slice.length] using h
  step as ⟨i, i_post⟩
  step as ⟨i1, i1_post⟩
  step as ⟨pos1, out1, pos1_post, w0, hw0, hout1⟩
  step as ⟨i2, i2_post⟩
  step as ⟨i3, i3_post⟩
  step as ⟨pos', out', pos'_post, w1, hw1, hout'⟩
  · simp only [Slice.length, hout1, List.length_append, List.length_take, List.length_drop, hw0.1]
    omega
  have hv := v.hBounds
  simp only [UScalarTy.U64_numBits_eq] at hv
  have c0 : i1.val = v.val % 4294967296 := by
    rw [i1_post, UScalar.cast_val_eq, i_post]; simp only [UScalarTy.U32_numBits_eq]; omega
  have c1 : i3.val = v.val / 4294967296 := by
    rw [i3_post, UScalar.cast_val_eq, i2_post]; simp only [UScalarTy.U32_numBits_eq]; omega
  refine ⟨by rw [pos'_post, pos1_post], w0 ++ w1, by simp [hw0.1, hw1.1], ?_, ?_⟩
  · rw [leNat_append, hw0.2, hw1.2, c0, c1, hw0.1]; omega
  · rw [hout', hout1, pos1_post]
    have ht : (List.take pos.val out.val ++ w0 ++ List.drop (pos.val + 4) out.val).take
        (pos.val + 4) = List.take pos.val out.val ++ w0 := by
      rw [List.take_append_of_le_length (by simp [hw0.1]; omega)]
      simp [hw0.1]
    have hd : (List.take pos.val out.val ++ w0 ++ List.drop (pos.val + 4) out.val).drop
        (pos.val + 4 + 4) = List.drop (pos.val + 8) out.val := by
      have hl : (List.take pos.val out.val ++ w0).length = pos.val + 4 := by simp [hw0.1]; omega
      rw [show pos.val + 4 + 4 = (List.take pos.val out.val ++ w0).length + 4 by omega,
        ← List.drop_drop, List.drop_left, List.drop_drop]
      congr 1; omega
    rw [ht, hd]; simp

/-- A little-endian `u64` field at the front of `l`. -/
theorem fmt_le64 (w rest : List U8) (v : U64) (hl : w.length = 8) (hv : leNat w = v.val) :
    FmtD bytes.LittleEndianU64.Insts.UntrustedReaderDecode (w ++ rest) v 8 :=
  ⟨rfl, by simp [hl], by rw [List.take_left' hl, hv]⟩

/-- **Spec theorem for `TransportHeader::encode`**: the type, then bytes that
    decode back to the same header. -/
@[step]
theorem TransportHeader.encode.spec (self : TransportHeader) :
    TransportHeader.encode self ⦃ (a : Array U8 16#usize) =>
      leNat (a.val.take 4) = 4 ∧
        FmtD TransportHeader.Insts.UntrustedReaderDecode (a.val.drop 4) self 12 ⦄ := by
  unfold TransportHeader.encode
  step*
  obtain ⟨w0, hw0, hs1⟩ : ∃ w0, LeBytes w0 TYPE_TRANSPORT ∧
      s1.val = s.val.take 0 ++ w0 ++ s.val.drop (0 + 4) := ⟨_, pos_post1, pos_post2⟩
  obtain ⟨w1, hw1, hs3⟩ : ∃ w1, LeBytes w1 self.receiver ∧
      s3.val = s2.val.take pos.val ++ w1 ++ s2.val.drop (pos.val + 4) := ⟨_, pos1_post1, pos1_post2⟩
  have hz : s.val = [] ++ List.replicate 16 0#u8 := by simp [s_post]
  rw [hz, write_at [] w0 16 0 rfl 4 hw0.1.symm (by simp [hw0.1])] at hs1
  simp only [List.nil_append, hw0.1] at hs1
  have hpos : pos.val = w0.length := by simp [pos_post, hw0.1]
  have hs2 : s2.val = s1.val := by
    rw [s2_post, to_slice_mut_back_post, Array.from_slice_val _ _ (by simp [hs1, hw0.1])]
  rw [hs2, hs1, write_at w0 w1 12 pos.val hpos 4 hw1.1.symm (by simp [hw1.1])] at hs3
  simp only [hw1.1] at hs3
  have hs4 : s4.val = s3.val := by
    rw [s4_post, to_slice_mut_back1_post,
      Array.from_slice_val _ _ (by simp [hs3, hw0.1, hw1.1])]
  have hpos1 : pos1.val = (w0 ++ w1).length := by simp [pos1_post, hpos, hw1.1]
  have hs5 : s5.val = w0 ++ (w1 ++ w) := by
    rw [__post3, hs4, hs3, write_at (w0 ++ w1) w 8 pos1.val hpos1 8 __post1.symm (by simp [__post1])]
    simp [__post1]
  have hfinal : (to_slice_mut_back2 s5).val = s5.val := by
    rw [to_slice_mut_back2_post,
      Array.from_slice_val _ _ (by simp [hs5, hw0.1, hw1.1, __post1])]
  rw [hfinal, hs5]
  refine ⟨by rw [LeBytes.leNat_type _ _ hw0]; simp, ?_⟩
  rw [List.drop_left' hw0.1, show (12 : Nat) = 4 + (8 + 0) from rfl]
  exact Dseq.intro (fmt_le32 w1 w _ hw1)
    (by rw [List.drop_left' hw1.1]
        exact Dseq.intro (by simpa using fmt_le64 w [] self.counter __post1 __post2) (Dnil.intro _))

end wireguard.message

namespace wireguard.transport
open wireguard.message wireguard.crypto

theorem setSlice!_eq {α} (s s' : List α) (i : Nat) (h : i + s'.length ≤ s.length) :
    s.setSlice! i s' = s.take i ++ s' ++ s.drop (i + s'.length) := by
  simp only [List.setSlice!]
  rw [min_eq_left (by omega), List.take_of_length_le (le_refl _)]

/-! ## Sending -/

/-- The length of a packet padded with zeros to a multiple of 16. -/
def paddedLen (n : Nat) : Nat := (n + 15) / 16 * 16

/-- The packet zero-padded to a multiple of 16: the plaintext of a transport
    message (paper section 5.4.6, `P ‖ 0^pad`). -/
def padded (l : List U8) : List U8 := l ++ List.replicate (paddedLen l.length - l.length) 0#u8

theorem le_paddedLen (n : Nat) : n ≤ paddedLen n := by unfold paddedLen; omega

theorem length_padded (l : List U8) : (padded l).length = paddedLen l.length := by
  have := le_paddedLen l.length
  simp only [padded, List.length_append, List.length_replicate]; omega

/-- **Spec theorem for `padded_len`**. -/
@[step]
theorem padded_len.spec (len : Usize) (h : len.val + 15 ≤ Usize.max) :
    padded_len len ⦃ (r : Usize) => r.val = paddedLen len.val ⦄ := by
  unfold padded_len paddedLen
  step*

/-- The first `p` bytes of `l` followed by zeros. -/
def pad (l : List U8) (p : Nat) : List U8 := (l ++ List.replicate p 0#u8).take p

theorem length_pad (l : List U8) (p : Nat) : (pad l p).length = p := by
  simp [pad]

theorem pad_eq_padded (l : List U8) : pad l (paddedLen l.length) = padded l := by
  have := le_paddedLen l.length
  simp only [pad, padded, List.take_append, List.take_replicate,
    List.take_of_length_le this]
  congr 2; omega

theorem getElem!_pad (l : List U8) (p i : Nat) (hi : i < p) :
    (pad l p)[i]! = if i < l.length then l[i]! else 0#u8 := by
  simp only [pad]
  rw [getElem!_pos _ _ (by simp; omega), List.getElem_take]
  split
  · rw [List.getElem_append_left (by omega), getElem!_pos _ _ (by omega)]
  · rw [List.getElem_append_right (by omega)]; simp

/-- One step of a copying loop: writing the `i`-th byte of `src` at `i`. -/
theorem copy_step (work src : List U8) (i p : Nat) (v : U8) (hi : i < p) (hp : p ≤ work.length)
    (hsrc : src.length = p) (hv : v = src[i]!) :
    (work.set i v).take (i + 1) ++ src.drop (i + 1) ++ (work.set i v).drop p =
      work.take i ++ src.drop i ++ work.drop p := by
  have hd : src.drop i = src[i] :: src.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
  rw [untrusted.take_set_succ _ _ _ (by omega), List.drop_set_of_lt (by omega), hd, hv,
    getElem!_pos _ _ (by omega)]
  simp

/-- The end of a copying loop. -/
theorem copy_done (work src : List U8) (p : Nat) (hsrc : src.length = p) :
    work.take p ++ src.drop p ++ work.drop p = work := by
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil, List.take_append_drop]

/-- **Spec theorem for `encrypt`'s first loop**: copies the packet, padded
    with zeros, into `work[..p]`. -/
@[step]
theorem encrypt_loop0.spec (packet work : Slice U8) (p i : Usize) (hp : p.val ≤ work.length)
    (hi : i.val ≤ p.val) :
    encrypt_loop0 packet work p i ⦃ (work' : Slice U8) =>
      work'.val = work.val.take i.val ++ (pad packet.val p.val).drop i.val ++
        work.val.drop p.val ⦄ := by
  unfold encrypt_loop0
  dsimp only
  split
  · have hv : (if i < packet.len then packet.index_usize i else ok 0#u8) =
        ok ((pad packet.val p.val)[i.val]!) := by
      rw [getElem!_pad _ _ _ (by scalar_tac)]
      split
      · rw [if_pos (by scalar_tac)]
        have hlt : i.val < packet.val.length := by scalar_tac
        simp [Slice.index_usize, List.getElem?_eq_getElem hlt, getElem!_pos packet.val i.val hlt]
      · rw [if_neg (by scalar_tac)]
    rw [hv]
    step*
    rw [work'_post, s_post, Slice.set_val_eq, i3_post]
    exact copy_step work.val (pad packet.val p.val) i.val p.val _ (by scalar_tac) (by scalar_tac)
      (length_pad _ _) rfl
  · simp only [WP.spec_ok]
    have : i.val = p.val := by scalar_tac
    rw [this, copy_done _ _ _ (length_pad _ _)]
termination_by p.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `encrypt`'s second loop**: copies the header into
    `out[..16]`. -/
@[step]
theorem encrypt_loop1.spec (out : Slice U8) (header : Array U8 16#usize) (j : Usize)
    (h : 16 ≤ out.length) (hj : j.val ≤ 16) :
    encrypt_loop1 out header j ⦃ (out' : Slice U8) =>
      out'.val = out.val.take j.val ++ header.val.drop j.val ++ out.val.drop 16 ⦄ := by
  unfold encrypt_loop1
  split
  · step*
    rw [out'_post, s_post, Slice.set_val_eq, j1_post, i_post]
    exact copy_step out.val header.val j.val 16 _ (by scalar_tac) (by scalar_tac) (by simp)
      (getElem!_pos header.val j.val (by simp; scalar_tac)).symm
  · simp only [WP.spec_ok]
    have : j.val = 16 := by scalar_tac
    rw [this, copy_done _ _ _ (by simp)]
termination_by 16 - j.val
decreasing_by all_goals scalar_tac

@[simp, scalar_tac_simps] theorem AEAD_TAG_LEN_val : AEAD_TAG_LEN.val = 16 := by
  simp [AEAD_TAG_LEN]

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

/-- **Spec theorem for `encrypt`**: if the buffers are large enough, the
    output is a transport message from `receiver` with `counter`, carrying the
    padded packet sealed under `key` with the counter as nonce. -/
@[step]
theorem encrypt.spec (key : Key) (receiver : U32) (counter : U64) (packet work out : Slice U8)
    (hlen : packet.length + 47 ≤ Usize.max) :
    encrypt inst c key receiver counter packet work out
      ⦃ (r : Option Usize) (work' out' : Slice U8) =>
        out'.length = out.length ∧
        match r with
        | none => work.length < paddedLen packet.length ∨
            out.length < paddedLen packet.length + 32
        | some n => n.val = paddedLen packet.length + 32 ∧
            ∃ hdr : List U8, hdr.length = 16 ∧ leNat (hdr.take 4) = 4 ∧
              FmtD TransportHeader.Insts.UntrustedReaderDecode (hdr.drop 4)
                ⟨receiver, counter⟩ 12 ∧
              out'.val.take n.val = hdr ++ P.aead key counter.val [] (padded packet.val) ⦄ := by
  have hp := le_paddedLen packet.length
  have hp' : paddedLen packet.length ≤ packet.length + 15 := by unfold paddedLen; omega
  unfold encrypt
  step as ⟨p, p_post⟩
  have hpl : p.val = paddedLen packet.length := by rw [p_post]; rfl
  split
  · simp only [WP.spec_ok]
    exact ⟨rfl, Or.inl (by scalar_tac)⟩
  step as ⟨i3, i3_post⟩
  step as ⟨i4, i4_post⟩
  split
  · simp only [WP.spec_ok]
    exact ⟨rfl, Or.inr (by scalar_tac)⟩
  step as ⟨work1, work1_post⟩
  step as ⟨header, hh1, hh2⟩
  step as ⟨out1, out1_post⟩
  have hwork1 : work1.val = pad packet.val p.val ++ work.val.drop p.val := by
    simpa using work1_post
  have hout1 : out1.val = header.val ++ out.val.drop 16 := by simpa using out1_post
  have hwl : p.val ≤ work1.length := by
    simp only [Slice.length, hwork1, List.length_append, length_pad]; omega
  have hol : out1.length = out.length := by
    simp only [Slice.length, hout1, List.length_append, List.length_drop, Array.length]
    scalar_tac
  step*
  · rw [s2_post1, s1_post1]; scalar_tac
  have hn : n.val = p.val + 32 := by scalar_tac
  have hs : s.val = [] := by simp [s_post]
  have hs1 : s1.val = padded packet.val := by
    rw [s1_post, hwork1, List.slice, ← pad_eq_padded, ← hpl]
    simp [List.take_left' (length_pad _ _)]
  have hs3l : s3.val.length = p.val + 16 := by
    rw [s3_post, P.aead_length, hs1, length_padded, hpl]
  have hhl : header.val.length = 16 := by simp
  have hback : (index_mut_back s3).val = header.val ++ s3.val ++ out.val.drop (p.val + 32) := by
    have hol' : out.val.length = out.length := rfl
    have hd : (header.val ++ out.val.drop 16).drop (16 + s3.val.length) =
        out.val.drop (p.val + 32) := by
      rw [show 16 + s3.val.length = header.val.length + (p.val + 16) by omega, ← List.drop_drop,
        List.drop_left, List.drop_drop]
      congr 1; omega
    rw [s2_post2, Slice.setSlice!_val, TRANSPORT_HEADER_LEN_val,
      setSlice!_eq _ _ _ (by simp [hout1, hs3l, hhl]; scalar_tac), hout1,
      List.take_left' hhl, hd]
  refine ⟨by simp [Slice.length, hback, hs3l, hhl]; scalar_tac, by rw [hn, hpl], header.val,
    hhl, hh1, hh2, ?_⟩
  rw [hback, hn, List.take_left' (by simp [hs3l, hhl]; omega), s3_post, hs, hs1]

end
/-! ## The inner packet -/

/-- The IP version of a packet: the high four bits of its first byte. -/
def ipVersion (l : List U8) : Nat := (l.headD 0#u8).val / 16

/-- `i` describes the IP packet `l`: a well-formed IPv4 packet with its
    addresses and total length, or a well-formed IPv6 packet with its
    addresses and the length of its header and payload. -/
def Inner.Spec (l : List U8) (i : Inner) : Prop :=
  if i.v6 then
    ipVersion l = 6 ∧ ∃ p : net.ipv6.Ipv6Packet, net.ipv6.Ipv6Packet.Spec l p ∧
      i.src.val = (p.header.src : U128).val ∧ i.dst.val = (p.header.dst : U128).val ∧
      i.len.val = 40 + (p.header.payload_len : U16).val
  else
    ipVersion l = 4 ∧ ∃ p : net.ipv4.Ipv4Packet, net.ipv4.Ipv4Packet.Spec l p ∧
      i.src.val = (p.header.src : U32).val ∧ i.dst.val = (p.header.dst : U32).val ∧
      i.len.val = (p.header.total_len : U16).val

theorem Ipv6Packet.Spec.header_eq {l : List U8} {p p' : net.ipv6.Ipv6Packet}
    (h : net.ipv6.Ipv6Packet.Spec l p) (h' : net.ipv6.Ipv6Packet.Spec l p') :
    p.header = p'.header :=
  ((FmtLaws net.ipv6.Ipv6Header.Insts.UntrustedReaderDecode).functional _ _ _ _ _
    h.2.2.1 h'.2.2.1).1

/-- A packet determines its family and source address. -/
theorem Inner.Spec.src_eq {l : List U8} {i i' : Inner} (h : Inner.Spec l i)
    (h' : Inner.Spec l i') : i.v6 = i'.v6 ∧ i.src.val = i'.src.val := by
  unfold Inner.Spec at h h'
  split at h <;> split at h'
  · obtain ⟨-, p, hp, hs, -⟩ := h
    obtain ⟨-, p', hp', hs', -⟩ := h'
    rw [hs, hs', Ipv6Packet.Spec.header_eq hp hp']
    simp_all
  · omega
  · omega
  · obtain ⟨-, p, hp, hs, -⟩ := h
    obtain ⟨-, p', hp', hs', -⟩ := h'
    rw [hs, hs', net.ipv4.Ipv4Packet.Spec.header_eq hp hp']
    simp_all

/-- **Spec theorem for `inner`**: the description of the IP packet `packet`,
    or none if it is not a well-formed IPv4 or IPv6 packet. -/
@[step]
theorem inner.spec (packet : Slice U8) :
    inner packet ⦃ (r : Option Inner) =>
      match r with
      | some i => Inner.Spec packet.val i
      | none => ∀ i, ¬ Inner.Spec packet.val i ⦄ := by
  unfold inner
  step as ⟨b, hb⟩
  split
  next hbt =>
    simp only [WP.spec_ok]
    have hnil : packet.val = [] := by simpa [hbt, Slice.length] using hb
    intro i hi
    unfold Inner.Spec at hi
    split at hi <;> simp [hnil, ipVersion] at hi
  rename_i hbt
  have hne : 0 < packet.length := by
    have : ¬ packet.val = [] := by simpa [hbt, Slice.length] using hb
    simpa [Slice.length, List.length_pos_iff] using this
  step as ⟨x, hx⟩
  step as ⟨ver, hver⟩
  have hv : ipVersion packet.val = ver.val := by
    rw [hver, hx]
    obtain ⟨y, t, hyt⟩ := List.exists_cons_of_ne_nil
      (by intro h; simp [Slice.length, h] at hne : packet.val ≠ [])
    simp [ipVersion, hyt]
  split
  · simp only [Untrusted.validate_eq]
    step as ⟨u, hu⟩
    step as ⟨res, hres⟩
    rw [hu] at hres
    cases res
    · rename_i ip
      step*
      unfold Inner.Spec
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨by rw [hv]; scalar_tac, ip, hres, ?_, ?_, ?_⟩
      · rw [i2_post]; exact U32.cast_U128_val_eq _
      · rw [i4_post]; exact U32.cast_U128_val_eq _
      · rw [i6_post]; exact U16.cast_Usize_val_eq _
    · simp only [WP.spec_ok]
      intro i hi
      unfold Inner.Spec at hi
      split at hi
      · rw [hv] at hi; scalar_tac
      · obtain ⟨-, p, hp, -⟩ := hi
        exact hres p hp
  split
  · simp only [Untrusted.validate_eq]
    step as ⟨u, hu⟩
    step as ⟨res, hres⟩
    rw [hu] at hres
    cases res
    · rename_i ip
      step*
      unfold Inner.Spec
      simp only [↓reduceIte]
      refine ⟨by rw [hv]; scalar_tac, ip, hres, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · rw [i5_post, i4_post, U16.cast_Usize_val_eq]
    · simp only [WP.spec_ok]
      intro i hi
      unfold Inner.Spec at hi
      split at hi
      · obtain ⟨-, p, hp, -⟩ := hi
        exact hres p hp
      · rw [hv] at hi; scalar_tac
  · simp only [WP.spec_ok]
    intro i hi
    unfold Inner.Spec at hi
    split at hi <;> (rw [hv] at hi; scalar_tac)

/-! ## Receiving -/

/-- The packet `i` routes back to `peer`: the longest prefix in `t` matching
    its source address belongs to `peer`. -/
def Routes (t : allowed_ips.AllowedIps) (peer : U16) (i : Inner) : Prop :=
  ∃ e, allowed_ips.Longest t i.v6 i.src.val e ∧ e.peer = peer

section
variable {C : Type} {inst : Crypto C} {c : C} {P : Primitives} [h : Laws inst c P]
include h

/-- **Spec theorem for `receive`**, the paper's section 5.4.6 on the receiving
    side. A message is *accepted* when its body is the sealing, under `key`
    with `counter` as nonce, of some plaintext that fits in `out`, and its
    counter is fresh for the replay window (whose accepted counters are `S`).
    Exactly then the counter is recorded, and the plaintext is written at the
    start of `out`. An accepted message is then
    - a keepalive if its plaintext is empty,
    - delivered if its plaintext is an IP packet whose source routes back to
      `peer`,
    - and dropped otherwise. -/
@[step]
theorem receive.spec (key : Key) (window : replay.Replay) (S : Set Nat) (hw : window.Inv S)
    (table : allowed_ips.AllowedIps) (ht : allowed_ips.Inv table) (peer : U16) (counter : U64)
    (body out : Slice U8) :
    receive inst c key window table peer counter body out
      ⦃ (r : Received) (window' : replay.Replay) (out' : Slice U8) =>
        ∃ accepted : Bool,
          (accepted = true ↔ body.length - 16 ≤ out.length ∧
            (∃ m, P.aead key counter.val [] m = body.val) ∧
            counter.val < replay.REJECT ∧ window.top.val ≤ counter.val + 1 + 8128 ∧
            counter.val ∉ S) ∧
          window'.Inv (if accepted then insert counter.val S else S) ∧
          out'.length = out.length ∧
          (accepted = true →
            P.aead key counter.val [] (out'.val.take (body.length - 16)) = body.val) ∧
          match r with
          | .Drop => accepted = false ∨ (body.length ≠ 16 ∧
              ∀ i, Inner.Spec (out'.val.take (body.length - 16)) i → ¬ Routes table peer i)
          | .Keepalive => accepted = true ∧ body.length = 16
          | .Packet len => accepted = true ∧
              ∃ i, Inner.Spec (out'.val.take (body.length - 16)) i ∧ Routes table peer i ∧
                i.len = len ⦄ := by
  unfold receive
  dsimp only
  split
  · simp only [WP.spec_ok]
    refine ⟨false, ?_, hw, rfl, by simp, by simp⟩
    simp only [Bool.false_eq_true, false_iff, not_and]
    rintro - ⟨m, hm⟩
    have := congrArg List.length hm
    rw [P.aead_length] at this
    scalar_tac
  step as ⟨n, hn⟩
  split
  · simp only [WP.spec_ok]
    refine ⟨false, ?_, hw, rfl, by simp, by simp⟩
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro h; scalar_tac
  rename_i hfit
  have hn' : n.val = body.length - 16 := by scalar_tac
  have hfits : body.length - 16 ≤ out.length := by scalar_tac
  step as ⟨s, s_post⟩
  step as ⟨s1, back, s1_post, s1_len, hback⟩
  step as ⟨b, s2, hs2len, hb, hb2⟩
  have hs : s.val = [] := by simp [s_post]
  rw [hs] at hb hb2
  have hs2l : s2.val.length = n.val := by
    have : s2.length = n.val := by rw [hs2len, s1_len]
    simpa [Slice.length] using this
  have hpt : (back s2).val.take (body.length - 16) = s2.val := by
    rw [hback, setSlice!_eq _ _ _ (by simp [hs2l]; scalar_tac), ← hn']
    simp [List.take_left' hs2l]
  have hlen : (back s2).length = out.length := by
    simp [Slice.length, hback]
  split
  swap
  · rename_i hbf
    simp only [WP.spec_ok]
    refine ⟨false, ?_, hw, hlen, by simp, by simp⟩
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro _ hm
    exact absurd (hb.mpr hm) (by simp [hbf])
  rename_i hbt
  have hauth := hb2 hbt
  step as ⟨b1, window1, hb1, hinv1⟩
  split
  swap
  · rename_i hb1f
    simp only [WP.spec_ok]
    refine ⟨false, ?_, by simpa [hb1f] using hinv1, hlen, by simp, by simp⟩
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro _ _ h1 h2 h3
    exact absurd (hb1.mpr ⟨h1, h2, h3⟩) (by simp [hb1f])
  rename_i hb1t
  have hacc : (true = true ↔ body.length - 16 ≤ out.length ∧
      (∃ m, P.aead key counter.val [] m = body.val) ∧
      counter.val < replay.REJECT ∧ window.top.val ≤ counter.val + 1 + 8128 ∧
      counter.val ∉ S) := by
    simp only [true_iff]; exact ⟨hfits, hb.mp hbt, hb1.mp hb1t⟩
  have hinv : window1.Inv (if true = true then insert counter.val S else S) := by
    simpa [hb1t] using hinv1
  have hok : true = true → P.aead key counter.val [] ((back s2).val.take (body.length - 16)) =
      body.val := fun _ => by rw [hpt]; exact hauth
  split
  next hn0 =>
    simp only [WP.spec_ok]
    refine ⟨true, hacc, hinv, hlen, hok, rfl, ?_⟩
    have : n.val = 0 := by rw [hn0]; rfl
    scalar_tac
  rename_i hn0
  have hne : body.length ≠ 16 := by
    intro h16; apply hn0; scalar_tac
  step as ⟨s3, s3_post, s3_len⟩
  have hs3 : s3.val = (back s2).val.take (body.length - 16) := by
    rw [s3_post, List.slice, hn']; simp
  step as ⟨o, ho⟩
  rw [hs3] at ho
  rcases o with _ | p <;> simp only at ho ⊢
  · simp only [WP.spec_ok]
    exact ⟨true, hacc, hinv, hlen, hok, Or.inr ⟨hne, fun i hi => absurd hi (ho i)⟩⟩
  step as ⟨o1, ho1⟩
  rcases o1 with _ | q <;> simp only at ho1 ⊢
  · simp only [WP.spec_ok]
    refine ⟨true, hacc, hinv, hlen, hok, Or.inr ⟨hne, ?_⟩⟩
    rintro i hi ⟨e, ⟨hin, hm, -⟩, -⟩
    obtain ⟨hv6, hsrc⟩ := Inner.Spec.src_eq hi ho
    rw [hv6, hsrc] at hm
    exact ho1 e hin hm
  obtain ⟨e, he, hq⟩ := ho1
  split
  next hqp =>
    simp only [WP.spec_ok]
    exact ⟨true, hacc, hinv, hlen, hok, rfl, p, ho, ⟨e, he, hq.trans hqp⟩, rfl⟩
  rename_i hqp
  simp only [WP.spec_ok]
  refine ⟨true, hacc, hinv, hlen, hok, Or.inr ⟨hne, ?_⟩⟩
  rintro i hi ⟨e', he', hpeer⟩
  obtain ⟨hv6, hsrc⟩ := Inner.Spec.src_eq hi ho
  rw [hv6, hsrc] at he'
  have := allowed_ips.Longest.unique ht he he'
  subst this
  exact hqp (hq.symm.trans hpeer)

end
end wireguard.transport
