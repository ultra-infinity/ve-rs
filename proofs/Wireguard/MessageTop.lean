/- Specs of `wireguard::message`: the four message formats, their decoder and
   their encoders. -/
import Wireguard.Funs
import Wireguard.Specs.Initiation
import Wireguard.Specs.Response
import Wireguard.Specs.CookieReply
import Wireguard.Specs.TransportHeader
import Net.Lemmas

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace wireguard.message

/-! ## Constants -/

@[simp, scalar_tac_simps] theorem TYPE_LEN_val : TYPE_LEN.val = 4 := by simp [TYPE_LEN]
@[simp, scalar_tac_simps] theorem TRANSPORT_HEADER_LEN_val : TRANSPORT_HEADER_LEN.val = 16 := by
  simp [TRANSPORT_HEADER_LEN]
@[simp, scalar_tac_simps] theorem TAG_LEN_val : TAG_LEN.val = 16 := by simp [TAG_LEN]
@[simp, scalar_tac_simps] theorem INITIATION_LEN_val : INITIATION_LEN.val = 148 := by
  simp [INITIATION_LEN]
@[simp, scalar_tac_simps] theorem RESPONSE_LEN_val : RESPONSE_LEN.val = 92 := by
  simp [RESPONSE_LEN]
@[simp, scalar_tac_simps] theorem COOKIE_REPLY_LEN_val : COOKIE_REPLY_LEN.val = 64 := by
  simp [COOKIE_REPLY_LEN]
@[simp] theorem TYPE_INITIATION_eq : TYPE_INITIATION = 1#u32 := by simp [TYPE_INITIATION]
@[simp] theorem TYPE_RESPONSE_eq : TYPE_RESPONSE = 2#u32 := by simp [TYPE_RESPONSE]
@[simp] theorem TYPE_COOKIE_REPLY_eq : TYPE_COOKIE_REPLY = 3#u32 := by simp [TYPE_COOKIE_REPLY]
@[simp] theorem TYPE_TRANSPORT_eq : TYPE_TRANSPORT = 4#u32 := by simp [TYPE_TRANSPORT]

/-! ## Decoding -/

/-- `l` is a well-formed WireGuard message that decodes to `m`: its first 4
    bytes, little-endian, are the type of `m`, and the rest is `m`'s body. A
    fixed-size body is the whole rest; a transport message has at least 32
    bytes, its header is bytes 4 to 15 and its encrypted packet the rest. -/
def Message.Spec (l : List U8) (m : Message) : Prop :=
  4 ≤ l.length ∧
    match m with
    | .Initiation v => leNat (l.take 4) = 1 ∧
        FmtD Initiation.Insts.UntrustedReaderDecode (l.drop 4) v (l.length - 4)
    | .Response v => leNat (l.take 4) = 2 ∧
        FmtD Response.Insts.UntrustedReaderDecode (l.drop 4) v (l.length - 4)
    | .CookieReply v => leNat (l.take 4) = 3 ∧
        FmtD CookieReply.Insts.UntrustedReaderDecode (l.drop 4) v (l.length - 4)
    | .Transport t => leNat (l.take 4) = 4 ∧ 32 ≤ l.length ∧
        FmtD TransportHeader.Insts.UntrustedReaderDecode ((l.drop 4).take 12) t.header 12 ∧
        (t.packet : Slice U8).val = l.drop 16

/-- **Spec theorem for `<Message as Validate<&[u8]>>::validate`**: accepts
    exactly the well-formed messages, and returns their decoding. -/
@[step]
theorem _root_.wireguard.message.Message.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Message.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Message ValidationError) =>
        match r with
        | .Ok m => Message.Spec input.val m
        | .Err _ => ∀ m, ¬ Message.Spec input.val m ⦄ := by
  unfold Message.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  dsimp only
  split
  · simp only [WP.spec_ok]
    rintro m ⟨h4, -⟩
    scalar_tac
  · have h4 : 4 ≤ input.val.length := by scalar_tac
    simp only [Untrusted.validate_eq]
    step as ⟨ s, hs, hslen ⟩
    step as ⟨ u, hu ⟩
    step as ⟨ res, hres ⟩
    cases res
    · rename_i k
      obtain ⟨-, hk⟩ := hres
      have hk4 : (k : U32).val = leNat (input.val.take 4) := by
        rw [hk, hu, hs]; simp [List.slice]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨ s1, hs1, hs1len ⟩
      step as ⟨ body, hbody ⟩
      have hb : (body : Slice U8).val = input.val.drop 4 := by rw [hbody, hs1]; simp
      have hblen : (input.val.drop 4).length = input.val.length - 4 := by simp
      -- A spec of another kind contradicts the type just read.
      have hkind : ∀ m, Message.Spec input.val m →
          (k : U32).val = match m with
            | .Initiation _ => 1 | .Response _ => 2 | .CookieReply _ => 3 | .Transport _ => 4 := by
        rintro (_ | _ | _ | _) ⟨-, hm, -⟩ <;> rw [hk4, hm]
      split
      · rename_i hk1
        apply WP.spec_bind
          (UntrustedShared0SliceU8.read_all.spec_of Initiation.Insts.UntrustedReaderDecode body)
        rintro (v | e) hr
        · simp only [hb, hblen] at hr
          simp only [bind_ok, WP.spec_ok]
          exact ⟨h4, by rw [← hk4, hk1]; simp, hr⟩
        · simp only [hb, hblen] at hr
          simp only [bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
          intro m hm
          have := hkind m hm
          rcases m with v | v | v | t <;> simp_all
          exact hr v hm.2.2
      · rename_i hk1
        split
        · rename_i hk2
          apply WP.spec_bind
            (UntrustedShared0SliceU8.read_all.spec_of Response.Insts.UntrustedReaderDecode body)
          rintro (v | e) hr
          · simp only [hb, hblen] at hr
            simp only [bind_ok, WP.spec_ok]
            exact ⟨h4, by rw [← hk4, hk2]; simp, hr⟩
          · simp only [hb, hblen] at hr
            simp only [bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
            intro m hm
            have := hkind m hm
            rcases m with v | v | v | t <;> simp_all
            exact hr v hm.2.2
        · rename_i hk2
          split
          · rename_i hk3
            apply WP.spec_bind
              (UntrustedShared0SliceU8.read_all.spec_of CookieReply.Insts.UntrustedReaderDecode body)
            rintro (v | e) hr
            · simp only [hb, hblen] at hr
              simp only [bind_ok, WP.spec_ok]
              exact ⟨h4, by rw [← hk4, hk3]; simp, hr⟩
            · simp only [hb, hblen] at hr
              simp only [bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
              intro m hm
              have := hkind m hm
              rcases m with v | v | v | t <;> simp_all
              exact hr v hm.2.2
          · rename_i hk3
            split
            · rename_i hkt
              step as ⟨ i2, hi2 ⟩
              split
              · simp only [WP.spec_ok]
                intro m hm
                have := hkind m hm
                rcases m with v | v | v | t <;> simp_all
                exact absurd hm.2.2.1 (by omega)
              · step as ⟨ s2, hs2, hs2len ⟩
                step as ⟨ u1, hu1 ⟩
                have hu1' : (u1 : Slice U8).val = (input.val.drop 4).take 12 := by
                  rw [hu1, hs2]; simp [List.slice]
                have hlen12 : ((input.val.drop 4).take 12).length = 12 := by
                  simp only [List.length_take, List.length_drop]; scalar_tac
                apply WP.spec_bind
                  (UntrustedShared0SliceU8.read_all.spec_of
                    TransportHeader.Insts.UntrustedReaderDecode u1)
                rintro (h | e) hr
                · simp only [hu1', hlen12] at hr
                  simp only [bind_ok]
                  step*
                  exact ⟨h4, by rw [← hk4, hkt]; simp, by scalar_tac, hr, by simp [u2_post, s3_post]⟩
                · simp only [hu1', hlen12] at hr
                  simp only [bind_ok,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
                  intro m hm
                  have := hkind m hm
                  rcases m with v | v | v | t <;> simp_all
                  exact hr t.header hm.2.2.2.1
            · rename_i hkt
              simp only [WP.spec_ok]
              intro m hm
              have := hkind m hm
              rcases m with v | v | v | t <;> simp_all
    · exfalso
      obtain ⟨hne, -⟩ := hres
      apply hne
      rw [hu]; scalar_tac

/-! ## Encoding -/

/-- **Spec theorem for the loop of `put_bytes`**: writes `src[i..]` at
    `pos + i`, leaving the bytes before `pos + i` and after
    `pos + src.len()` alone. -/
@[step]
theorem put_bytes_loop.spec (out : Slice U8) (pos : Usize) (src : Slice U8) (i : Usize)
    (h : pos.val + src.length ≤ out.length) (hi : i.val ≤ src.length) :
    put_bytes_loop out pos src i ⦃ (out' : Slice U8) =>
      out'.val = out.val.take (pos.val + i.val) ++ src.val.drop i.val ++
        out.val.drop (pos.val + src.length) ⦄ := by
  unfold put_bytes_loop
  dsimp only
  split
  · step*
    have hlt : pos.val + i.val < out.val.length := by scalar_tac
    have hsi : i.val < src.val.length := by scalar_tac
    rw [out'_post, s_post, Slice.set_val_eq, i3_post, i4_post, ← Nat.add_assoc,
      untrusted.take_set_succ _ _ _ hlt, List.drop_set_of_lt (by scalar_tac),
      List.drop_eq_getElem_cons hsi, i2_post]
    simp
  · simp only [WP.spec_ok]
    have : i.val = src.length := by scalar_tac
    rw [this, List.drop_eq_nil_of_le (by simp), List.append_nil]
    exact (List.take_append_drop _ _).symm
termination_by src.length - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `put_bytes`**: writes `src` at `pos`, and returns the
    position after it. -/
@[step]
theorem put_bytes.spec (out : Slice U8) (pos : Usize) (src : Slice U8)
    (h : pos.val + src.length ≤ out.length) :
    put_bytes out pos src ⦃ (pos' : Usize) (out' : Slice U8) =>
      pos'.val = pos.val + src.length ∧
        out'.val = out.val.take pos.val ++ src.val ++ out.val.drop (pos.val + src.length) ⦄ := by
  unfold put_bytes
  step*
  simp_all

/-- The bytes of a `u32` field, least significant first. -/
def LeBytes (w : List U8) (v : U32) : Prop := w.length = 4 ∧ leNat w = v.val

/-- **Spec theorem for `put_u32`**: writes the 4 bytes of `v`, least
    significant first, at `pos`, and returns the position after them. -/
@[step]
theorem put_u32.spec (out : Slice U8) (pos : Usize) (v : U32) (h : pos.val + 4 ≤ out.length) :
    put_u32 out pos v ⦃ (pos' : Usize) (out' : Slice U8) =>
      pos'.val = pos.val + 4 ∧ ∃ w, LeBytes w v ∧
        out'.val = out.val.take pos.val ++ w ++ out.val.drop (pos.val + 4) ⦄ := by
  unfold put_u32
  step*
  have hs : s.val = [i1, i4, i7, i9] := by simp [s_post, Array.make]
  have hslen : s.length = 4 := by simp [Slice.length, hs]
  refine ⟨by rw [pos'_post, hslen], s.val, ⟨by simp [hs], ?_⟩, by rw [pos'_post1, hslen]⟩
  have c1 : i1.val = v.val % 256 := by
    rw [i1_post, UScalar.cast_val_eq, i_post]; simp only [UScalarTy.U8_numBits_eq]; omega
  have c2 : i4.val = v.val / 256 % 256 := by
    rw [i4_post, UScalar.cast_val_eq, i3_post, i2_post]; simp only [UScalarTy.U8_numBits_eq]; omega
  have c3 : i7.val = v.val / 65536 % 256 := by
    rw [i7_post, UScalar.cast_val_eq, i6_post, i5_post]; simp only [UScalarTy.U8_numBits_eq]; omega
  have c4 : i9.val = v.val / 16777216 := by
    rw [i9_post, UScalar.cast_val_eq, i8_post]; simp only [UScalarTy.U8_numBits_eq]
    have := v.hBounds; simp only [UScalarTy.U32_numBits_eq] at this; omega
  have := v.hBounds
  simp only [UScalarTy.U32_numBits_eq] at this
  simp only [hs, leNat, beNat, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil, c1, c2, c3, c4]
  omega

/-! ### Building the encoded bytes -/

/-- Writing `w` at position `p`, right after the bytes `pre` written so far,
    into the `n` zeros after them. -/
theorem write_at (pre w : List U8) (n p : Nat) (hp : p = pre.length) (k : Nat)
    (hk : k = w.length) (h : w.length ≤ n) :
    (pre ++ List.replicate n 0#u8).take p ++ w ++ (pre ++ List.replicate n 0#u8).drop (p + k) =
      pre ++ w ++ List.replicate (n - w.length) 0#u8 := by
  subst hp hk
  simp [List.drop_append, List.drop_replicate]

/-- A little-endian `u32` field at the front of `l`. -/
theorem fmt_le32 (w rest : List U8) (v : U32) (h : LeBytes w v) :
    FmtD bytes.LittleEndianU32.Insts.UntrustedReaderDecode (w ++ rest) v 4 :=
  ⟨rfl, by simp [h.1], by rw [List.take_left' h.1, h.2]⟩

/-- A byte array field at the front of `l`. -/
theorem fmt_array {N : Usize} (a : Array U8 N) (rest : List U8) :
    FmtD (ArrayU8N.Insts.UntrustedReaderDecode N) (a.val ++ rest) a N.val :=
  ⟨rfl, by simp, by simp⟩

theorem LeBytes.leNat_type (w : List U8) (v : U32) (h : LeBytes w v) (rest : List U8) :
    leNat ((w ++ rest).take 4) = v.val := by
  rw [List.take_left' h.1, h.2]

/-- **Spec theorem for `CookieReply::encode`**: bytes that decode back to the
    same cookie reply. -/
@[step]
theorem CookieReply.encode.spec (self : CookieReply) :
    CookieReply.encode self ⦃ (a : Array U8 64#usize) =>
      Message.Spec a.val (.CookieReply self) ⦄ := by
  unfold CookieReply.encode
  step*
  obtain ⟨w0, hw0, hs1⟩ : ∃ w0, LeBytes w0 TYPE_COOKIE_REPLY ∧
      s1.val = s.val.take 0 ++ w0 ++ s.val.drop (0 + 4) := ⟨_, pos_post1, pos_post2⟩
  have hz : s.val = [] ++ List.replicate 64 0#u8 := by simp [s_post]
  rw [hz, write_at [] w0 64 0 rfl 4 hw0.1.symm (by simp [hw0.1])] at hs1
  simp only [List.nil_append, hw0.1] at hs1
  have hpos : pos.val = w0.length := by simp [pos_post, hw0.1]
  have hs2 : s2.val = s1.val := by
    rw [s2_post, to_slice_mut_back_post, Array.from_slice_val _ _ (by simp [hs1, hw0.1])]
  have hs3 : s3.val = w0 ++ w ++ List.replicate 56 0#u8 := by
    rw [pos1_post2, hs2, hs1, write_at w0 w 60 pos.val hpos 4 pos1_post1.1.symm
      (by simp [pos1_post1.1])]
    simp [pos1_post1.1]
  have hs4 : s4.val = s3.val := by
    rw [s4_post, to_slice_mut_back1_post,
      Array.from_slice_val _ _ (by simp [hs3, hw0.1, pos1_post1.1])]
  have hpos1 : pos1.val = (w0 ++ w).length := by simp [pos1_post, hpos, pos1_post1.1]
  have hs6 : s6.val = w0 ++ w ++ self.nonce.val ++ List.replicate 32 0#u8 := by
    rw [pos2_post1, hs4, hs3, s5_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w) self.nonce.val 56 pos1.val hpos1 _ (by simp) (by simp)]
    simp
  have hs7 : s7.val = s6.val := by
    rw [s7_post, to_slice_mut_back2_post,
      Array.from_slice_val _ _ (by simp [hs6, hw0.1, pos1_post1.1])]
  have hpos2 : pos2.val = (w0 ++ w ++ self.nonce.val).length := by
    simp [pos2_post, s5_post, hpos1]; omega
  have hs9 : s9.val = w0 ++ (w ++ (self.nonce.val ++ self.encrypted_cookie.val)) := by
    rw [__post1, hs7, hs6, s8_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w ++ self.nonce.val) self.encrypted_cookie.val 32 pos2.val hpos2 _
      (by simp) (by simp)]
    simp
  have hfinal : (to_slice_mut_back3 s9).val = s9.val := by
    rw [to_slice_mut_back3_post,
      Array.from_slice_val _ _ (by simp [hs9, hw0.1, pos1_post1.1])]
  rw [hfinal, hs9]
  refine ⟨by simp [hw0.1, pos1_post1.1], by rw [LeBytes.leNat_type _ _ hw0]; simp, ?_⟩
  rw [List.drop_left' hw0.1, show (w0 ++ (w ++ (self.nonce.val ++ self.encrypted_cookie.val))).length - 4
    = 4 + ((24#usize).val + (32 + 0)) by simp [hw0.1, pos1_post1.1]]
  exact Dseq.intro (fmt_le32 w _ _ pos1_post1)
    (by rw [List.drop_left' pos1_post1.1]
        exact Dseq.intro (fmt_array self.nonce _)
          (by rw [List.drop_left' (by simp)]
              exact Dseq.intro (by simpa using fmt_array self.encrypted_cookie [])
                (Dnil.intro _)))

/-- **Spec theorem for `Response::encode`**: bytes that decode back to the same
    response. -/
@[step]
theorem Response.encode.spec (self : Response) :
    Response.encode self ⦃ (a : Array U8 92#usize) => Message.Spec a.val (.Response self) ⦄ := by
  unfold Response.encode
  step*
  obtain ⟨w0, hw0, h1⟩ : ∃ w0, LeBytes w0 TYPE_RESPONSE ∧
      s1.val = s.val.take 0 ++ w0 ++ s.val.drop (0 + 4) := ⟨_, pos_post1, pos_post2⟩
  obtain ⟨w1, hw1, h3⟩ : ∃ w1, LeBytes w1 self.sender ∧
      s3.val = s2.val.take pos.val ++ w1 ++ s2.val.drop (pos.val + 4) := ⟨_, pos1_post1, pos1_post2⟩
  have hz : s.val = [] ++ List.replicate 92 0#u8 := by simp [s_post]
  rw [hz, write_at [] w0 92 0 rfl 4 hw0.1.symm (by simp [hw0.1])] at h1
  simp only [List.nil_append, hw0.1] at h1
  have h2 : s2.val = s1.val := by
    rw [s2_post, to_slice_mut_back_post, Array.from_slice_val _ _ (by simp [h1, hw0.1])]
  rw [h2, h1, write_at w0 w1 88 pos.val (by simp [pos_post, hw0.1]) 4 hw1.1.symm
    (by simp [hw1.1])] at h3
  simp only [hw1.1] at h3
  have h4 : s4.val = s3.val := by
    rw [s4_post, to_slice_mut_back1_post, Array.from_slice_val _ _ (by simp [h3, hw0.1, hw1.1])]
  have h5 : s5.val = w0 ++ w1 ++ w ++ List.replicate 80 0#u8 := by
    rw [pos2_post2, h4, h3, write_at (w0 ++ w1) w 84 pos1.val
      (by simp [pos1_post, pos_post, hw0.1, hw1.1]) 4 pos2_post1.1.symm (by simp [pos2_post1.1])]
    simp [pos2_post1.1]
  have h6 : s6.val = s5.val := by
    rw [s6_post, to_slice_mut_back2_post,
      Array.from_slice_val _ _ (by simp [h5, hw0.1, hw1.1, pos2_post1.1])]
  have h8 : s8.val = w0 ++ w1 ++ w ++ self.ephemeral.val ++ List.replicate 48 0#u8 := by
    rw [pos3_post1, h6, h5, s7_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w1 ++ w) self.ephemeral.val 80 pos2.val
      (by simp [pos2_post, pos1_post, pos_post, hw0.1, hw1.1, pos2_post1.1]) _ (by simp) (by simp)]
    simp
  have h9 : s9.val = s8.val := by
    rw [s9_post, to_slice_mut_back3_post,
      Array.from_slice_val _ _ (by simp [h8, hw0.1, hw1.1, pos2_post1.1])]
  have h11 : s11.val = w0 ++ w1 ++ w ++ self.ephemeral.val ++ self.encrypted_nothing.val ++
      List.replicate 32 0#u8 := by
    rw [pos4_post1, h9, h8, s10_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w1 ++ w ++ self.ephemeral.val) self.encrypted_nothing.val 48 pos3.val
      (by simp [pos3_post, s7_post, pos2_post, pos1_post, pos_post, hw0.1, hw1.1,
        pos2_post1.1] <;> omega) _ (by simp) (by simp)]
    simp
  have h12 : s12.val = s11.val := by
    rw [s12_post, to_slice_mut_back4_post,
      Array.from_slice_val _ _ (by simp [h11, hw0.1, hw1.1, pos2_post1.1])]
  have h14 : s14.val = w0 ++ w1 ++ w ++ self.ephemeral.val ++ self.encrypted_nothing.val ++
      self.mac1.val ++ List.replicate 16 0#u8 := by
    rw [pos5_post1, h12, h11, s13_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w1 ++ w ++ self.ephemeral.val ++ self.encrypted_nothing.val) self.mac1.val
      32 pos4.val (by simp [pos4_post, s10_post, pos3_post, s7_post, pos2_post, pos1_post,
        pos_post, hw0.1, hw1.1, pos2_post1.1] <;> omega) _ (by simp) (by simp)]
    simp
  have h15 : s15.val = s14.val := by
    rw [s15_post, to_slice_mut_back5_post,
      Array.from_slice_val _ _ (by simp [h14, hw0.1, hw1.1, pos2_post1.1])]
  have h17 : s17.val = w0 ++ (w1 ++ (w ++ (self.ephemeral.val ++ (self.encrypted_nothing.val ++
      (self.mac1.val ++ self.mac2.val))))) := by
    rw [__post1, h15, h14, s16_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w1 ++ w ++ self.ephemeral.val ++ self.encrypted_nothing.val ++
      self.mac1.val) self.mac2.val 16 pos5.val (by simp [pos5_post, s13_post, pos4_post,
        s10_post, pos3_post, s7_post, pos2_post, pos1_post, pos_post, hw0.1, hw1.1,
        pos2_post1.1] <;> omega) _ (by simp) (by simp)]
    simp
  have hfinal : (to_slice_mut_back6 s17).val = s17.val := by
    rw [to_slice_mut_back6_post,
      Array.from_slice_val _ _ (by simp [h17, hw0.1, hw1.1, pos2_post1.1])]
  rw [hfinal, h17]
  refine ⟨by simp [hw0.1, hw1.1, pos2_post1.1], by rw [LeBytes.leNat_type _ _ hw0]; simp, ?_⟩
  rw [List.drop_left' hw0.1, show (w0 ++ (w1 ++ (w ++ (self.ephemeral.val ++
      (self.encrypted_nothing.val ++ (self.mac1.val ++ self.mac2.val)))))).length - 4
    = 4 + (4 + ((32#usize).val + ((16#usize).val + ((16#usize).val + (16 + 0))))) by
      simp [hw0.1, hw1.1, pos2_post1.1]]
  exact Dseq.intro (fmt_le32 w1 _ _ hw1)
    (by rw [List.drop_left' hw1.1]
        exact Dseq.intro (fmt_le32 w _ _ pos2_post1)
          (by rw [List.drop_left' pos2_post1.1]
              exact Dseq.intro (fmt_array self.ephemeral _)
                (by rw [List.drop_left' (by simp)]
                    exact Dseq.intro (fmt_array self.encrypted_nothing _)
                      (by rw [List.drop_left' (by simp)]
                          exact Dseq.intro (fmt_array self.mac1 _)
                            (by rw [List.drop_left' (by simp)]
                                exact Dseq.intro (by simpa using fmt_array self.mac2 [])
                                  (Dnil.intro _))))))

/-- **Spec theorem for `Initiation::encode`**: bytes that decode back to the
    same initiation. -/
@[step]
theorem Initiation.encode.spec (self : Initiation) :
    Initiation.encode self ⦃ (a : Array U8 148#usize) =>
      Message.Spec a.val (.Initiation self) ⦄ := by
  unfold Initiation.encode
  step*
  obtain ⟨w0, hw0, h1⟩ : ∃ w0, LeBytes w0 TYPE_INITIATION ∧
      s1.val = s.val.take 0 ++ w0 ++ s.val.drop (0 + 4) := ⟨_, pos_post1, pos_post2⟩
  have hz : s.val = [] ++ List.replicate 148 0#u8 := by simp [s_post]
  rw [hz, write_at [] w0 148 0 rfl 4 hw0.1.symm (by simp [hw0.1])] at h1
  simp only [List.nil_append, hw0.1] at h1
  have hw := pos1_post1
  have h2 : s2.val = s1.val := by
    rw [s2_post, to_slice_mut_back_post, Array.from_slice_val _ _ (by simp [h1, hw0.1])]
  have h3 : s3.val = w0 ++ w ++ List.replicate 140 0#u8 := by
    rw [pos1_post2, h2, h1, write_at w0 w 144 pos.val (by simp [pos_post, hw0.1]) 4 hw.1.symm
      (by simp [hw.1])]
    simp [hw.1]
  have h4 : s4.val = s3.val := by
    rw [s4_post, to_slice_mut_back1_post, Array.from_slice_val _ _ (by simp [h3, hw0.1, hw.1])]
  have h6 : s6.val = w0 ++ w ++ self.ephemeral.val ++ List.replicate 108 0#u8 := by
    rw [pos2_post1, h4, h3, s5_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w) self.ephemeral.val 140 pos1.val
      (by simp [pos1_post, pos_post, hw0.1, hw.1] <;> omega) _ (by simp) (by simp)]
    simp
  have h7 : s7.val = s6.val := by
    rw [s7_post, to_slice_mut_back2_post, Array.from_slice_val _ _ (by simp [h6, hw0.1, hw.1])]
  have h9 : s9.val = w0 ++ w ++ self.ephemeral.val ++ self.encrypted_static.val ++
      List.replicate 60 0#u8 := by
    rw [pos3_post1, h7, h6, s8_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w ++ self.ephemeral.val) self.encrypted_static.val 108 pos2.val
      (by simp [pos2_post, s5_post, pos1_post, pos_post, hw0.1, hw.1] <;> omega) _ (by simp)
      (by simp)]
    simp
  have h10 : s10.val = s9.val := by
    rw [s10_post, to_slice_mut_back3_post, Array.from_slice_val _ _ (by simp [h9, hw0.1, hw.1])]
  have h12 : s12.val = w0 ++ w ++ self.ephemeral.val ++ self.encrypted_static.val ++
      self.encrypted_timestamp.val ++ List.replicate 32 0#u8 := by
    rw [pos4_post1, h10, h9, s11_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w ++ self.ephemeral.val ++ self.encrypted_static.val)
      self.encrypted_timestamp.val 60 pos3.val (by simp [pos3_post, s8_post, pos2_post, s5_post,
        pos1_post, pos_post, hw0.1, hw.1] <;> omega) _ (by simp) (by simp)]
    simp
  have h13 : s13.val = s12.val := by
    rw [s13_post, to_slice_mut_back4_post,
      Array.from_slice_val _ _ (by simp [h12, hw0.1, hw.1])]
  have h15 : s15.val = w0 ++ w ++ self.ephemeral.val ++ self.encrypted_static.val ++
      self.encrypted_timestamp.val ++ self.mac1.val ++ List.replicate 16 0#u8 := by
    rw [pos5_post1, h13, h12, s14_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w ++ self.ephemeral.val ++ self.encrypted_static.val ++
      self.encrypted_timestamp.val) self.mac1.val 32 pos4.val (by simp [pos4_post, s11_post,
        pos3_post, s8_post, pos2_post, s5_post, pos1_post, pos_post, hw0.1, hw.1] <;> omega)
      _ (by simp) (by simp)]
    simp
  have h16 : s16.val = s15.val := by
    rw [s16_post, to_slice_mut_back5_post,
      Array.from_slice_val _ _ (by simp [h15, hw0.1, hw.1])]
  have h18 : s18.val = w0 ++ (w ++ (self.ephemeral.val ++ (self.encrypted_static.val ++
      (self.encrypted_timestamp.val ++ (self.mac1.val ++ self.mac2.val))))) := by
    rw [__post1, h16, h15, s17_post]
    simp only [Array.length_to_slice, Array.val_to_slice]
    rw [write_at (w0 ++ w ++ self.ephemeral.val ++ self.encrypted_static.val ++
      self.encrypted_timestamp.val ++ self.mac1.val) self.mac2.val 16 pos5.val (by simp [pos5_post,
        s14_post, pos4_post, s11_post, pos3_post, s8_post, pos2_post, s5_post, pos1_post, pos_post,
        hw0.1, hw.1] <;> omega) _ (by simp) (by simp)]
    simp
  have hfinal : (to_slice_mut_back6 s18).val = s18.val := by
    rw [to_slice_mut_back6_post, Array.from_slice_val _ _ (by simp [h18, hw0.1, hw.1])]
  rw [hfinal, h18]
  refine ⟨by simp [hw0.1, hw.1], by rw [LeBytes.leNat_type _ _ hw0]; simp, ?_⟩
  rw [List.drop_left' hw0.1, show (w0 ++ (w ++ (self.ephemeral.val ++
      (self.encrypted_static.val ++ (self.encrypted_timestamp.val ++ (self.mac1.val ++
      self.mac2.val)))))).length - 4
    = 4 + ((32#usize).val + ((48#usize).val + ((28#usize).val + ((16#usize).val +
      (16 + 0))))) by simp [hw0.1, hw.1]]
  exact Dseq.intro (fmt_le32 w _ _ hw)
    (by rw [List.drop_left' hw.1]
        exact Dseq.intro (fmt_array self.ephemeral _)
          (by rw [List.drop_left' (by simp)]
              exact Dseq.intro (fmt_array self.encrypted_static _)
                (by rw [List.drop_left' (by simp)]
                    exact Dseq.intro (fmt_array self.encrypted_timestamp _)
                      (by rw [List.drop_left' (by simp)]
                          exact Dseq.intro (fmt_array self.mac1 _)
                            (by rw [List.drop_left' (by simp)]
                                exact Dseq.intro (by simpa using fmt_array self.mac2 [])
                                  (Dnil.intro _))))))

/-! ## Round trips -/

/-- A byte string is the encoding of at most one message. -/
theorem Message.Spec.functional {l : List U8} {m m' : Message} (h : Message.Spec l m)
    (h' : Message.Spec l m') : m = m' := by
  obtain ⟨-, h⟩ := h
  obtain ⟨-, h'⟩ := h'
  rcases m with v | v | v | t <;> rcases m' with v' | v' | v' | t' <;> simp only at h h' <;>
    (try (exfalso; omega))
  · rw [((FmtLaws Initiation.Insts.UntrustedReaderDecode).functional _ _ _ _ _ h.2 h'.2).1]
  · rw [((FmtLaws Response.Insts.UntrustedReaderDecode).functional _ _ _ _ _ h.2 h'.2).1]
  · rw [((FmtLaws CookieReply.Insts.UntrustedReaderDecode).functional _ _ _ _ _ h.2 h'.2).1]
  · obtain ⟨-, -, hh, hp⟩ := h
    obtain ⟨-, -, hh', hp'⟩ := h'
    rcases t with ⟨th, tp⟩
    rcases t' with ⟨th', tp'⟩
    simp only at hh hp hh' hp'
    rw [((FmtLaws TransportHeader.Insts.UntrustedReaderDecode).functional _ _ _ _ _ hh hh').1,
      show tp = tp' from (Slice.eq_iff (α := U8) tp tp').mpr (hp.trans hp'.symm)]

/-- On the encoding of a message, the decoder returns that message. With the
    encoders' specs, this is the round trip: decoding what an encoder wrote
    gives back what it was given. -/
theorem Message.validate_of_spec (input : Slice U8) (m : Message) (h : Message.Spec input.val m) :
    Message.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Message ValidationError) => r = .Ok m ⦄ := by
  apply WP.spec_mono
    (Message.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec input)
  rintro (m' | e) h'
  · rw [Message.Spec.functional h' h]
  · exact absurd h (h' m)

end wireguard.message
