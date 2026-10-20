/- Hand-written specs of `net::tcp`: the TCP header check and
   `<Ipv4Tcp as Validate<&[u8]>>::validate`, `<Ipv6Tcp as …>::validate`. -/
import Net.UdpEncode
import Net.Specs.TcpHeader

open Aeneas Aeneas.Std Result untrusted untrusted.reader net.ipv4

namespace net.tcp

@[simp, scalar_tac_simps] theorem MIN_HEADER_LEN_val : MIN_HEADER_LEN.val = 20 := by
  simp [MIN_HEADER_LEN]
@[simp] theorem PROTO_TCP_eq : PROTO_TCP = 6#u8 := by simp [PROTO_TCP]

/-- The header length of the TCP header `h`: four times its data offset. -/
def hdrLen (h : TcpHeader) : Nat := 4 * ((h.offset : U8).val / 16)

/-- `d`, the payload of an IP packet, is a TCP segment whose fixed header
    decodes to `h`: at least 20 bytes, the first 20 decode as `h`, whose data
    offset is at least 5 and whose header length fits in `d`. -/
def Segment (d : List U8) (h : TcpHeader) : Prop :=
  20 ≤ d.length ∧ FmtD TcpHeader.Insts.UntrustedReaderDecode (d.take 20) h 20 ∧
    5 ≤ (h.offset : U8).val / 16 ∧ hdrLen h ≤ d.length

theorem Segment.header_eq {d : List U8} {h h' : TcpHeader} (hs : Segment d h)
    (hs' : Segment d h') : h = h' :=
  ((FmtLaws TcpHeader.Insts.UntrustedReaderDecode).functional _ _ _ _ _ hs.2.1 hs'.2.1).1

/-- **Spec theorem for `net::tcp::header`**: the header and header length of
    a well-formed segment, or an error if it is not one. -/
@[step]
theorem header.spec (segment : Slice U8) :
    header segment ⦃ (r : core.result.Result (TcpHeader × Usize) ValidationError) =>
      match r with
      | .Ok (h, hl) => Segment segment.val h ∧ hl.val = hdrLen h
      | .Err _ => ∀ h, ¬ Segment segment.val h ⦄ := by
  unfold header
  dsimp only
  split
  · simp only [WP.spec_ok]
    rintro h ⟨h20, -⟩
    scalar_tac
  rename_i h20
  have h20' : 20 ≤ segment.val.length := by scalar_tac
  step as ⟨s, hs, hsl⟩
  step as ⟨u, hu⟩
  have hus : (u : Slice U8).val = segment.val.take 20 := by rw [hu, hs]; simp [List.slice]
  have hlen : (segment.val.take 20).length = 20 := by simp; omega
  apply WP.spec_bind (UntrustedShared0SliceU8.read_all.spec_of TcpHeader.Insts.UntrustedReaderDecode u)
  rintro (h | e) hres
  · simp only [hus, hlen] at hres
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step*
    all_goals have hoff : off.val = (h.offset : U8).val / 16 := (by
      rw [off_post, U8.cast_Usize_val_eq, i2_post])
    all_goals have huniq : ∀ h', Segment segment.val h' → h' = h := (fun h' hs' =>
      ((FmtLaws TcpHeader.Insts.UntrustedReaderDecode).functional _ _ _ _ _ hs'.2.1 hres).1)
    · intro h' hs'
      obtain rfl := huniq h' hs'
      have := hs'.2.2.1
      scalar_tac
    · intro h' hs'
      obtain rfl := huniq h' hs'
      have := hs'.2.2.2
      simp only [hdrLen] at this
      scalar_tac
    · refine ⟨⟨h20', hres, by scalar_tac, ?_⟩, ?_⟩ <;> simp only [hdrLen] <;> scalar_tac
  · simp only [hus, hlen] at hres
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    rintro h' ⟨-, hD, -⟩
    exact hres h' hD

/-! ## Checksums -/

/-- The checksum over the byte values `ps` (a pseudo-header) and then `d` is
    valid: the one's-complement sum is `0xFFFF`. -/
def ChecksumOk (ps : List Nat) (d : List U8) : Prop :=
  (inet.wordsN (ps ++ d.map (·.val))).foldl inet.add1c 0 = 65535

/-- The pieces the validators sum, in order, as one sum over the pseudo-header
    values and the segment. -/
theorem sum_pieces (a b c d : List U8) (ha : a.length % 2 = 0) (hb : b.length % 2 = 0)
    (hc : c.length % 2 = 0) :
    inet.spec (inet.spec (inet.spec (inet.spec 0 a) b) c) d =
      (inet.wordsN ((a.map (·.val) ++ b.map (·.val) ++ c.map (·.val)) ++ d.map (·.val))).foldl
        inet.add1c 0 := by
  rw [← inet.spec_append 0 a b ha, ← inet.spec_append 0 (a ++ b) c (by simp; omega),
    ← inet.spec_append 0 (a ++ b ++ c) d (by simp; omega), inet.spec_eq]
  simp

/-! ## TCP over IPv4 -/

/-- The IPv4 pseudo-header of the segment `d` carried by the IPv4 packet `l`,
    as byte values: the addresses, a zero byte, the protocol 6, and the
    segment length. -/
def pseudo4 (l d : List U8) : List Nat :=
  ((l.drop 12).take 8).map (·.val) ++ [0, 6] ++ [d.length / 256, d.length % 256]

/-- `l` is a well-formed IPv4 packet carrying a whole TCP segment, which
    decodes to `t`: `l` is an IPv4 packet with protocol 6 that is not a
    fragment, its payload `d` is a segment whose fixed header decodes as
    `t.header`, the checksum is valid over the pseudo-header and `d`, and the
    options and payload are the rest of the header and of `d`. -/
def Ipv4Tcp.Spec (l : List U8) (t : Ipv4Tcp) : Prop :=
  Ipv4Packet.Spec l t.ip ∧ (t.ip.header.protocol : U8).val = 6 ∧
    t.ip.header.fragment.more_fragments = false ∧ t.ip.header.fragment.offset.val = 0 ∧
    Segment (payloadOf l) t.header ∧ ChecksumOk (pseudo4 l (payloadOf l)) (payloadOf l) ∧
    (t.options : Slice U8).val = ((payloadOf l).take (hdrLen t.header)).drop 20 ∧
    (t.payload : Slice U8).val = (payloadOf l).drop (hdrLen t.header)

/-- **Spec theorem for `<Ipv4Tcp as Validate<&[u8]>>::validate`**: accepts
    exactly the IPv4 packets carrying a well-formed TCP segment. -/
@[step]
theorem _root_.net.tcp.Ipv4Tcp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Ipv4Tcp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Ipv4Tcp ValidationError) =>
        match r with
        | .Ok t => Ipv4Tcp.Spec input.val t
        | .Err _ => ∀ t, ¬ Ipv4Tcp.Spec input.val t ⦄ := by
  unfold Ipv4Tcp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  simp only [Untrusted.validate_eq]
  step as ⟨ u0, hu0 ⟩
  step as ⟨ res, hres ⟩
  rw [hu0] at hres
  cases res
  · rename_i ip
    have hip : Ipv4Packet.Spec input.val ip := hres
    obtain ⟨h20, hhl, hhltl, htl, -⟩ := hres
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step*
    · rintro t ⟨hip', hp, -⟩
      rw [hip'.header_eq hip] at hp
      have := ‹(ip.header.protocol != PROTO_TCP) = true›
      simp_all
    · rintro t ⟨hip', -, hm, -⟩
      rw [hip'.header_eq hip] at hm
      simp_all
    · rintro t ⟨hip', -, -, ho, -⟩
      rw [hip'.header_eq hip] at ho
      have := ‹(ip.header.fragment.offset != 0#u16) = true›
      simp_all
    have hd : segment.val = payloadOf input.val := by
      rw [segment_post, header_len_post, header_len_post1, slice_eq_payloadOf]
    have hprot : (ip.header.protocol : U8).val = 6 := by
      have := ‹¬(ip.header.protocol != PROTO_TCP) = true›
      simp at this; rw [this]
    have hmf : ip.header.fragment.more_fragments = false := by
      simpa using ‹¬ip.header.fragment.more_fragments = true›
    have hfo : ip.header.fragment.offset.val = 0 := by
      have := ‹¬(ip.header.fragment.offset != 0#u16) = true›
      simp at this; rw [this]
    rcases r1 with ⟨h, hl⟩ | e
    swap
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      rintro t ⟨-, -, -, -, hs, -⟩
      rw [← hd] at hs
      exact r1_post _ hs
    obtain ⟨hseg, hhl'⟩ := r1_post
    rw [hd] at hseg
    have hlen : (payloadOf input.val).length ≤ 65535 := by
      have h1 := beNat_lt ((input.val.drop 2).take 2)
      have h2 : ((input.val.drop 2).take 2).length ≤ 2 := by simp
      have h3 : 256 ^ ((input.val.drop 2).take 2).length ≤ 256 ^ 2 :=
        Nat.pow_le_pow_right (by decide) h2
      rw [length_payloadOf _ htl]; unfold totalLen; omega
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step*
    all_goals have hsum : i5.val = (inet.wordsN (pseudo4 input.val (payloadOf input.val) ++
        (payloadOf input.val).map (·.val))).foldl inet.add1c 0 := (by
      rw [i5_post, acc2_post, acc1_post, acc_post,
        sum_pieces s s1 s2 segment (by simp [Slice.length] at s_post1 ⊢; omega)
          (by simp [s1_post]) (by simp [s2_post])]
      have hs : s.val = (input.val.drop 12).take 8 := by rw [s_post]; rfl
      have hlseg : segment.val.length = (payloadOf input.val).length := by rw [hd]
      have hc1 : (UScalar.cast UScalarTy.U8 i1).val = (payloadOf input.val).length / 256 := by
        rw [net.udp.cast_u8, i1_post]; simp only [Slice.len_val, hlseg]; omega
      have hc2 : (UScalar.cast UScalarTy.U8 i3).val = (payloadOf input.val).length % 256 := by
        rw [net.udp.cast_u8, i3_post]; simp only [Slice.len_val, hlseg]; omega
      simp [pseudo4, hs, s1_post, s2_post, Array.make, i2_post, i4_post, hc1, hc2, hd])
    · rintro t ⟨-, -, -, -, -, hck, -⟩
      have := ‹(i5 != inet.VALID) = true›
      apply bne_iff_ne.mp this
      apply (UScalar.eq_equiv _ _).mpr
      rw [hsum, inet.VALID_val]
      exact hck
    · have : 20 ≤ hl.val := by
        rw [hhl']; unfold hdrLen; have := hseg.2.2.1; omega
      simp; scalar_tac
    · refine ⟨hip, hprot, hmf, hfo, hseg, ?_, ?_, ?_⟩
      · have := ‹¬(i5 != inet.VALID) = true›
        simp only [bne_iff_ne, ne_eq, not_not] at this
        unfold ChecksumOk
        rw [← hsum, this, inet.VALID_val]
      · simp_all [List.slice, List.drop_take]
      · simp_all
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    rintro t ⟨hip, -⟩
    exact hres t.ip hip

/-! ## TCP over IPv6 -/

theorem sum_pieces5 (a b c e d : List U8) (ha : a.length % 2 = 0) (hb : b.length % 2 = 0)
    (hc : c.length % 2 = 0) (he : e.length % 2 = 0) :
    inet.spec (inet.spec (inet.spec (inet.spec (inet.spec 0 a) b) c) e) d =
      (inet.wordsN ((a.map (·.val) ++ b.map (·.val) ++ c.map (·.val) ++ e.map (·.val)) ++
        d.map (·.val))).foldl inet.add1c 0 := by
  rw [← inet.spec_append 0 a b ha, ← inet.spec_append 0 (a ++ b) c (by simp; omega),
    ← inet.spec_append 0 (a ++ b ++ c) e (by simp; omega),
    ← inet.spec_append 0 (a ++ b ++ c ++ e) d (by simp; omega), inet.spec_eq]
  simp

/-- The IPv6 pseudo-header of the segment `d` carried by the IPv6 packet `l`,
    as byte values: the addresses, the segment length as 32 bits, three zero
    bytes and the next header 6. -/
def pseudo6 (l d : List U8) : List Nat :=
  ((l.drop 8).take 32).map (·.val) ++ [0, 0] ++ [d.length / 256, d.length % 256] ++ [0, 0, 0, 6]

/-- `l` is a well-formed IPv6 packet carrying a whole TCP segment, which
    decodes to `t`: `l` is an IPv6 packet with next header 6, its payload `d`
    is a segment whose fixed header decodes as `t.header`, the checksum is
    valid over the pseudo-header and `d`, and the options and payload are the
    rest of the header and of `d`. -/
def Ipv6Tcp.Spec (l : List U8) (t : Ipv6Tcp) : Prop :=
  ipv6.Ipv6Packet.Spec l t.ip ∧ (t.ip.header.next_header : U8).val = 6 ∧
    Segment (ipv6.payloadOf l) t.header ∧
    ChecksumOk (pseudo6 l (ipv6.payloadOf l)) (ipv6.payloadOf l) ∧
    (t.options : Slice U8).val = ((ipv6.payloadOf l).take (hdrLen t.header)).drop 20 ∧
    (t.payload : Slice U8).val = (ipv6.payloadOf l).drop (hdrLen t.header)

/-- **Spec theorem for `<Ipv6Tcp as Validate<&[u8]>>::validate`**: accepts
    exactly the IPv6 packets carrying a well-formed TCP segment. -/
@[step]
theorem _root_.net.tcp.Ipv6Tcp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Ipv6Tcp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Ipv6Tcp ValidationError) =>
        match r with
        | .Ok t => Ipv6Tcp.Spec input.val t
        | .Err _ => ∀ t, ¬ Ipv6Tcp.Spec input.val t ⦄ := by
  unfold Ipv6Tcp.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  simp only [Untrusted.validate_eq]
  step as ⟨ u0, hu0 ⟩
  step as ⟨ res, hres ⟩
  rw [hu0] at hres
  cases res
  · rename_i ip
    have hip : ipv6.Ipv6Packet.Spec input.val ip := hres
    obtain ⟨h40, hend, -⟩ := hres
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step*
    · rintro t ⟨hip', hp, -⟩
      rw [ipv6.Ipv6Packet.Spec.header_eq hip' hip] at hp
      have := ‹(ip.header.next_header != PROTO_TCP) = true›
      simp_all
    · have : 40 ≤ «end».val := by rw [end_post]; unfold ipv6.payloadEnd; omega
      scalar_tac
    have hd : segment.val = ipv6.payloadOf input.val := by
      rw [segment_post, end_post, ipv6.HEADER_LEN_val, ipv6.slice_eq_payloadOf]
    have hnext : (ip.header.next_header : U8).val = 6 := by
      have := ‹¬(ip.header.next_header != PROTO_TCP) = true›
      simp at this; rw [this]
    rcases r1 with ⟨h, hl⟩ | e
    swap
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      rintro t ⟨-, -, hs, -⟩
      rw [← hd] at hs
      exact r1_post _ hs
    obtain ⟨hseg, hhl'⟩ := r1_post
    rw [hd] at hseg
    have hlen : (ipv6.payloadOf input.val).length ≤ 65535 := by
      have h1 := beNat_lt ((input.val.drop 4).take 2)
      have h2 : ((input.val.drop 4).take 2).length ≤ 2 := by simp
      have h3 : 256 ^ ((input.val.drop 4).take 2).length ≤ 256 ^ 2 :=
        Nat.pow_le_pow_right (by decide) h2
      simp only [ipv6.payloadOf, List.length_drop, List.length_take]
      unfold ipv6.payloadEnd; omega
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step*
    all_goals have hsum : i5.val = (inet.wordsN (pseudo6 input.val (ipv6.payloadOf input.val) ++
        (ipv6.payloadOf input.val).map (·.val))).foldl inet.add1c 0 := (by
      rw [i5_post, acc3_post, acc2_post, acc1_post, acc_post,
        sum_pieces5 s s1 s2 s3 segment (by simp [Slice.length] at s_post1 ⊢; omega)
          (by simp [s1_post]) (by simp [s2_post]) (by simp [s3_post])]
      have hs : s.val = (input.val.drop 8).take 32 := by rw [s_post]; rfl
      have hlseg : segment.val.length = (ipv6.payloadOf input.val).length := by rw [hd]
      have hc1 : (UScalar.cast UScalarTy.U8 i1).val = (ipv6.payloadOf input.val).length / 256 := by
        rw [net.udp.cast_u8, i1_post]; simp only [Slice.len_val, hlseg]; omega
      have hc2 : (UScalar.cast UScalarTy.U8 i3).val = (ipv6.payloadOf input.val).length % 256 := by
        rw [net.udp.cast_u8, i3_post]; simp only [Slice.len_val, hlseg]; omega
      simp [pseudo6, hs, s1_post, s2_post, s3_post, Array.make, Array.repeat_val, i2_post, i4_post,
        hc1, hc2, hd])
    · rintro t ⟨-, -, -, hck, -⟩
      have := ‹(i5 != inet.VALID) = true›
      apply bne_iff_ne.mp this
      apply (UScalar.eq_equiv _ _).mpr
      rw [hsum, inet.VALID_val]
      exact hck
    · have : 20 ≤ hl.val := by
        rw [hhl']; unfold hdrLen; have := hseg.2.2.1; omega
      simp; scalar_tac
    · refine ⟨hip, hnext, hseg, ?_, ?_, ?_⟩
      · have := ‹¬(i5 != inet.VALID) = true›
        simp only [bne_iff_ne, ne_eq, not_not] at this
        unfold ChecksumOk
        rw [← hsum, this, inet.VALID_val]
      · simp_all [List.slice, List.drop_take]
      · simp_all
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    rintro t ⟨hip, -⟩
    exact hres t.ip hip

end net.tcp
