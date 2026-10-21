/- Specs of `wireguard::message`: the four message formats, their decoder and
   their encoders. -/
import Wireguard.Funs
import Wireguard.Specs.Initiation
import Wireguard.Specs.Response
import Wireguard.Specs.CookieReply
import Wireguard.Specs.TransportHeader
import Net.Lemmas

open Aeneas Aeneas.Std Result untrusted untrusted.reader untrusted.writer

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

theorem setSlice!_drop {α} (s s' : List α) (i : Nat) (h : i + s'.length = s.length) :
    s.setSlice! i s' = s.take i ++ s' := by
  simp only [List.setSlice!]
  rw [min_eq_left (by omega), List.take_of_length_le (le_refl _), List.drop_eq_nil_of_le (by omega),
    List.append_nil]

/-- **Spec theorem for `put_message`**: the type, little-endian, then the body,
    into an `out` that holds exactly both. -/
@[step]
theorem put_message.spec {T : Type} (inst : untrusted.writer.Encode T) {E : T → List U8}
    [untrusted.writer.EncodesAs inst E] (kind : U32) (body : T) (out : Slice U8)
    (h : out.length = 4 + (E body).length) :
    put_message inst kind body out ⦃ (out' : Slice U8) =>
      out'.val = untrusted.writer.leBytes 4 kind.val ++ E body ⦄ := by
  unfold put_message
  apply WP.spec_bind (untrusted.writer.encode_into.spec
    bytes.LittleEndianU32.Insts.UntrustedWriterEncode kind out)
  rintro ⟨r1, out1⟩ ⟨hl1, h1⟩
  simp only [WP.uncurry'_pair, uncurry]
  cases r1
  · obtain ⟨-, -, hout1⟩ := h1
    simp only [core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut]
    split
    case isFalse hn =>
      exfalso; apply hn; simp only [Slice.length] at hl1 h ⊢; scalar_tac
    simp only [bind_ok]
    apply WP.spec_bind (untrusted.writer.encode_into.spec inst body (out1.drop TYPE_LEN))
    rintro ⟨r2, s1⟩ ⟨hl2, h2⟩
    simp only [WP.uncurry'_pair, uncurry]
    have hd : (out1.drop TYPE_LEN).length = (E body).length := by
      simp only [Slice.length] at hl1 h
      simp [Slice.drop, Slice.length, hl1, h]
    cases r2
    · obtain ⟨-, -, hs1⟩ := h2
      simp only [WP.spec_ok]
      have hs1' : s1.val = E body := by
        rw [hs1, List.drop_eq_nil_of_le (by simp only [Slice.length] at hd; omega), List.append_nil]
      simp only [Slice.from_val, TYPE_LEN_val]
      rw [setSlice!_drop _ _ _ (by simp only [Slice.length] at hl1 h hs1' ⊢; rw [hs1']; omega),
        hs1', hout1, List.take_left' (by simp)]
    · exfalso
      rw [hd] at h2
      exact Nat.lt_irrefl _ h2
  · exfalso
    simp only [Slice.length] at h h1
    simp at h1
    omega

/-- A message's bytes, `kind` then the encoded `body`: its type is `kind`, and
    the rest decodes back to `body`, given `body`'s round trip. -/
theorem decodes_encoded {T : Type} (enc : untrusted.writer.Encode T)
    (dec : untrusted.reader.Decode T) {E : T → List U8} {D : List U8 → T → Nat → Prop}
    {F : List U8 → Prop} [untrusted.writer.EncodesAs enc E] [DecodesAs dec D F]
    {V : T → Prop} [h : untrusted.writer.RoundTrip enc dec V] (kind : U32) (body : T)
    (hv : V body) :
    let l := untrusted.writer.leBytes 4 kind.val ++ E body
    4 ≤ l.length ∧ leNat (l.take 4) = kind.val ∧ D (l.drop 4) body (l.length - 4) := by
  have hk := kind.hBounds
  simp only [UScalarTy.U32_numBits_eq] at hk
  refine ⟨by simp, ?_, ?_⟩
  · rw [List.take_left' (by simp), untrusted.writer.leNat_leBytes, Nat.mod_eq_of_lt (by simpa using hk)]
  · rw [List.drop_left' (by simp)]
    simpa using h.roundtrip body [] hv

/-- The bytes of the fixed-size array `a`, written through its slice. -/
theorem from_slice_put {N : Usize} (a : Std.Array U8 N) (s : Slice U8) (h : s.length = N.val) :
    (a.from_slice s).val = s.val :=
  Array.from_slice_val _ _ h

/-- **Spec theorem for `Initiation::encode`**: bytes that decode back to the
    same message. -/
@[step]
theorem Initiation.encode.spec (self : Initiation) :
    Initiation.encode self ⦃ (a : Array U8 148#usize) =>
      Message.Spec a.val (.Initiation self) ⦄ := by
  have hl : ∀ s : List U8, s = untrusted.writer.leBytes 4 TYPE_INITIATION.val ++
      FmtE Initiation.Insts.UntrustedWriterEncode self → s.length = 148 := by
    rintro s rfl
    simp only [FmtE, Eseq, Enil, Initiation.fields, List.length_append, leBytes_length, List.length_nil]
    all_goals simp
  unfold Initiation.encode
  step*
  · have := hl (untrusted.writer.leBytes 4 TYPE_INITIATION.val ++ FmtE Initiation.Insts.UntrustedWriterEncode self) rfl
    simp only [Slice.length, s_post, FmtE, List.length_append, leBytes_length] at this ⊢
    simp at this ⊢
    omega
  rw [to_slice_mut_back_post, from_slice_put _ _ (by rw [Slice.length, s1_post]; exact hl _ rfl),
    s1_post]
  obtain ⟨h4, hk, hD⟩ := decodes_encoded Initiation.Insts.UntrustedWriterEncode
    Initiation.Insts.UntrustedReaderDecode TYPE_INITIATION self (by simp only [Vseq, Vnil, FmtV, and_self])
  exact ⟨h4, by simpa using hk, hD⟩

/-- **Spec theorem for `Response::encode`**: bytes that decode back to the
    same message. -/
@[step]
theorem Response.encode.spec (self : Response) :
    Response.encode self ⦃ (a : Array U8 92#usize) =>
      Message.Spec a.val (.Response self) ⦄ := by
  have hl : ∀ s : List U8, s = untrusted.writer.leBytes 4 TYPE_RESPONSE.val ++
      FmtE Response.Insts.UntrustedWriterEncode self → s.length = 92 := by
    rintro s rfl
    simp only [FmtE, Eseq, Enil, Response.fields, List.length_append, leBytes_length, List.length_nil]
    all_goals simp
  unfold Response.encode
  step*
  · have := hl (untrusted.writer.leBytes 4 TYPE_RESPONSE.val ++ FmtE Response.Insts.UntrustedWriterEncode self) rfl
    simp only [Slice.length, s_post, FmtE, List.length_append, leBytes_length] at this ⊢
    simp at this ⊢
    omega
  rw [to_slice_mut_back_post, from_slice_put _ _ (by rw [Slice.length, s1_post]; exact hl _ rfl),
    s1_post]
  obtain ⟨h4, hk, hD⟩ := decodes_encoded Response.Insts.UntrustedWriterEncode
    Response.Insts.UntrustedReaderDecode TYPE_RESPONSE self (by simp only [Vseq, Vnil, FmtV, and_self])
  exact ⟨h4, by simpa using hk, hD⟩

/-- **Spec theorem for `CookieReply::encode`**: bytes that decode back to the
    same message. -/
@[step]
theorem CookieReply.encode.spec (self : CookieReply) :
    CookieReply.encode self ⦃ (a : Array U8 64#usize) =>
      Message.Spec a.val (.CookieReply self) ⦄ := by
  have hl : ∀ s : List U8, s = untrusted.writer.leBytes 4 TYPE_COOKIE_REPLY.val ++
      FmtE CookieReply.Insts.UntrustedWriterEncode self → s.length = 64 := by
    rintro s rfl
    simp only [FmtE, Eseq, Enil, CookieReply.fields, List.length_append, leBytes_length, List.length_nil]
    all_goals simp
  unfold CookieReply.encode
  step*
  · have := hl (untrusted.writer.leBytes 4 TYPE_COOKIE_REPLY.val ++ FmtE CookieReply.Insts.UntrustedWriterEncode self) rfl
    simp only [Slice.length, s_post, FmtE, List.length_append, leBytes_length] at this ⊢
    simp at this ⊢
    omega
  rw [to_slice_mut_back_post, from_slice_put _ _ (by rw [Slice.length, s1_post]; exact hl _ rfl),
    s1_post]
  obtain ⟨h4, hk, hD⟩ := decodes_encoded CookieReply.Insts.UntrustedWriterEncode
    CookieReply.Insts.UntrustedReaderDecode TYPE_COOKIE_REPLY self (by simp only [Vseq, Vnil, FmtV, and_self])
  exact ⟨h4, by simpa using hk, hD⟩

/-- **Spec theorem for `TransportHeader::encode`**: bytes that decode back to the
    same message. -/
@[step]
theorem TransportHeader.encode.spec (self : TransportHeader) :
    TransportHeader.encode self ⦃ (a : Array U8 16#usize) =>
      leNat (a.val.take 4) = 4 ∧
        FmtD TransportHeader.Insts.UntrustedReaderDecode (a.val.drop 4) self 12 ⦄ := by
  have hl : ∀ s : List U8, s = untrusted.writer.leBytes 4 TYPE_TRANSPORT.val ++
      FmtE TransportHeader.Insts.UntrustedWriterEncode self → s.length = 16 := by
    rintro s rfl
    simp only [FmtE, Eseq, Enil, TransportHeader.fields, List.length_append, leBytes_length, List.length_nil]
    all_goals simp
  unfold TransportHeader.encode
  step*
  · have := hl (untrusted.writer.leBytes 4 TYPE_TRANSPORT.val ++ FmtE TransportHeader.Insts.UntrustedWriterEncode self) rfl
    simp only [Slice.length, s_post, FmtE, List.length_append, leBytes_length] at this ⊢
    simp at this ⊢
    omega
  rw [to_slice_mut_back_post, from_slice_put _ _ (by rw [Slice.length, s1_post]; exact hl _ rfl),
    s1_post]
  obtain ⟨h4, hk, hD⟩ := decodes_encoded TransportHeader.Insts.UntrustedWriterEncode
    TransportHeader.Insts.UntrustedReaderDecode TYPE_TRANSPORT self (by simp only [Vseq, Vnil, FmtV, and_self])
  refine ⟨by simpa using hk, ?_⟩
  have h12 := hl _ rfl
  simp only [List.length_append, leBytes_length] at h12
  rwa [show (12 : Nat) = (untrusted.writer.leBytes 4 TYPE_TRANSPORT.val ++
    FmtE TransportHeader.Insts.UntrustedWriterEncode self).length - 4 by simp only [List.length_append, leBytes_length]; omega]

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
