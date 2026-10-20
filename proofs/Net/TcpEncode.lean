/- Specs of the TCP encoders of `net::tcp`: `encode_ipv4` and `encode_ipv6`
   write packets carrying a bare segment (no options, no data) that
   `Ipv4Tcp` and `Ipv6Tcp` accept and decode back to the same addresses,
   ports, numbers and flags. The checksums use `fix_bytes`, as the UDP
   encoders do. -/
import Net.UdpEncode
import Net.TcpTop

open Aeneas Aeneas.Std Result untrusted untrusted.reader net.udp

namespace net.tcp

@[simp, scalar_tac_simps] theorem BARE_IPV4_LEN_val : BARE_IPV4_LEN.val = 40 := by
  simp [BARE_IPV4_LEN]
@[simp, scalar_tac_simps] theorem BARE_IPV6_LEN_val : BARE_IPV6_LEN.val = 60 := by
  simp [BARE_IPV6_LEN]
@[simp, scalar_tac_simps] theorem PROTO_TCP_val : PROTO_TCP.val = 6 := by simp

/-- The bytes of a bare TCP header, as numbers: data offset 5, window 0,
    urgent pointer 0. -/
def tcpN (sp dp : U16) (seq ack : U32) (flags : U8) (c : Nat) : List Nat :=
  be16N sp.val ++ be16N dp.val ++ be32N seq.val ++ be32N ack.val ++ [80, flags.val, 0, 0] ++
    be16N c ++ [0, 0]

/-- **Spec theorem for `tcp_header`**. -/
@[step]
theorem tcp_header.spec (sp dp : U16) (seq ack : U32) (flags : U8) (checksum : U16) :
    tcp_header sp dp seq ack flags checksum ⦃ (r : Array U8 20#usize) =>
      r.val.map (·.val) = tcpN sp dp seq ack flags checksum.val ⦄ := by
  unfold tcp_header
  step*
  have gs := get_of_map s_post
  have ga := get_of_map a_post
  have h1 := sp.hBounds
  have h2 := dp.hBounds
  have h3 := checksum.hBounds
  simp only [UScalarTy.U16_numBits_eq] at h1 h2 h3
  simp [Array.make, tcpN, be16N, be32N, *, cast_u8] at *
  omega

/-- A big-endian `u32` at the front of `m`. -/
theorem fmt_be32 (m : List U8) (v : U32) (h : (m.take 4).map (·.val) = be32N v.val) :
    FmtD bytes.BigEndianU32.Insts.UntrustedReaderDecode m v 4 := by
  have hl : 4 ≤ m.length := by
    have := congrArg List.length h; simp [be32N] at this; omega
  have hv := v.hBounds
  simp only [UScalarTy.U32_numBits_eq] at hv
  refine ⟨rfl, hl, ?_⟩
  rw [beNat_eq, h]; simp [beNatN, be32N]; omega

/-- The decoding of a bare TCP header. -/
def bareHeader (sp dp : U16) (seq ack : U32) (flags : U8) (c : U16) : TcpHeader :=
  { src_port := sp, dst_port := dp, seq := seq, ack := ack, offset := (80#u8 : U8),
    flags := flags, window := (0#u16 : U16), checksum := c, urgent := (0#u16 : U16) }

/-- `bytes_at`, for bare TCP headers. -/
macro "tcp_bytes_at" h:term : tactic =>
  `(tactic| (simp +zetaDelta only [take_map, drop_map, $h:term]; simp +zetaDelta [tcpN, bareHeader, be16N, be32N]))

/-- The bare header `T` decodes as a TCP header with these fields, as a
    whole segment. -/
theorem segment_of_bytes (T : List U8) (sp dp : U16) (seq ack : U32) (flags : U8) (c : U16)
    (hT : T.map (·.val) = tcpN sp dp seq ack flags c.val) :
    T.length = 20 ∧ Segment T (bareHeader sp dp seq ack flags c) ∧
      hdrLen (bareHeader sp dp seq ack flags c) = 20 := by
  have hTl : T.length = 20 := by
    have := congrArg List.length hT; simpa [tcpN, be16N, be32N] using this
  have hhl : hdrLen (bareHeader sp dp seq ack flags c) = 20 := by
    simp [hdrLen, bareHeader]
  refine ⟨hTl, ⟨by omega, ?_, by simp [bareHeader], by omega⟩, hhl⟩
  rw [List.take_of_length_le (by omega),
    show (20 : Nat) = 2 + (2 + (4 + (4 + (1 + (1 + (2 + (2 + (2 + 0)))))))) from rfl]
  exact Dseq.intro (fmt_be16 _ _ (by tcp_bytes_at hT)) (Dseq.intro (fmt_be16 _ _ (by tcp_bytes_at hT))
    (Dseq.intro (fmt_be32 _ _ (by tcp_bytes_at hT)) (Dseq.intro (fmt_be32 _ _ (by tcp_bytes_at hT))
    (Dseq.intro (fmt_be8 _ _ (by tcp_bytes_at hT)) (Dseq.intro (fmt_be8 _ _ (by tcp_bytes_at hT))
    (Dseq.intro (fmt_be16 _ _ (by tcp_bytes_at hT)) (Dseq.intro (fmt_be16 _ _ (by tcp_bytes_at hT))
    (Dseq.intro (fmt_be16 _ _ (by tcp_bytes_at hT)) (Dnil.intro _)))))))))

/-! ## IPv4 -/

/-- **The bytes `encode_ipv4` writes form a TCP segment in an IPv4
    packet**: an IPv4 header `H` without options, with protocol 6, total
    length 40, a valid checksum and these addresses, then a bare TCP header
    `T` with a valid checksum, decode to a segment with these addresses and
    header and no data. -/
theorem ipv4_tcp_of_bytes (H T : List U8) (src dst : U32) (cs sp dp : U16) (seq ack : U32)
    (flags : U8) (c : U16)
    (hH : H.map (·.val) = [69, 0] ++ be16N 40 ++ [0, 0, 64, 0, 64, 6] ++ be16N cs.val ++
      be32N src.val ++ be32N dst.val)
    (hT : T.map (·.val) = tcpN sp dp seq ack flags c.val)
    (hHc : inet.spec 0 H = 65535) (hTc : ChecksumOk (pseudo4 (H ++ T) T) T) :
    ∃ t : Ipv4Tcp, Ipv4Tcp.Spec (H ++ T) t ∧ t.ip.header.src = src ∧ t.ip.header.dst = dst ∧
      t.header = bareHeader sp dp seq ack flags c ∧ (t.payload : Slice U8).val = [] := by
  obtain ⟨hTl, hseg, hhdr⟩ := segment_of_bytes T sp dp seq ack flags c hT
  have hHl : H.length = 20 := by
    have := congrArg List.length hH; simpa [be16N, be32N] using this
  have hvals : (H ++ T).map (·.val) = H.map (·.val) ++ T.map (·.val) := by simp
  have hhl : ipv4.headerLen (H ++ T) = 20 := by
    unfold ipv4.headerLen; rw [beNat_eq, take_map, hvals, hH]; simp [beNatN]
  have htl : ipv4.totalLen (H ++ T) = 40 := by
    unfold ipv4.totalLen; rw [beNat_eq, take_map, drop_map, hvals, hH]
    simp [beNatN, be16N]
  have hpay : ipv4.payloadOf (H ++ T) = T := by
    unfold ipv4.payloadOf
    rw [htl, hhl, List.take_of_length_le (by simp; omega), List.drop_left' hHl]
  have htake : (H ++ T).take 20 = H := List.take_left' hHl
  let hdr : ipv4.Ipv4Header :=
    { version_ihl := ⟨5#u8⟩, tos := (0#u8 : U8), total_len := (40#u16 : U16),
      ident := (0#u16 : U16), fragment := ⟨true, false, 0#u16⟩, ttl := (64#u8 : U8),
      protocol := (6#u8 : U8), checksum := cs, src := src, dst := dst }
  let ip : ipv4.Ipv4Packet :=
    { header := hdr, options := Slice.from [] (by simp),
      payload := Slice.from T (by rw [hTl]; scalar_tac), padding := Slice.from [] (by simp) }
  let e : Slice U8 := Slice.from [] (by simp)
  let t : Ipv4Tcp := { ip := ip, header := bareHeader sp dp seq ack flags c, options := e, payload := e }
  refine ⟨t, ?_, rfl, rfl, rfl, Slice.from_val _ _⟩
  refine ⟨⟨by simp [hHl, hTl], by rw [hhl], by rw [hhl, htl]; omega,
    by rw [htl]; simp [hHl, hTl], ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, by rw [hpay]; exact hseg, by rw [hpay]; exact hTc, ?_, ?_⟩
  · rw [hhl, htake]; exact hHc
  · rw [htake, show (20 : Nat) = 1 + (1 + (2 + (2 + (2 + (1 + (1 + (2 + (4 + (4 + 0))))))))) from rfl]
    refine Dseq.intro (fmt_versionIhl H (by bytes_at hH)) (Dseq.intro (fmt_be8 _ _ (by bytes_at hH))
      (Dseq.intro (fmt_be16 _ _ (by bytes_at hH)) (Dseq.intro (fmt_be16 _ _ (by bytes_at hH))
      (Dseq.intro (fmt_fragment _ (by bytes_at hH)) (Dseq.intro (fmt_be8 _ _ (by bytes_at hH))
      (Dseq.intro (fmt_be8 _ _ (by bytes_at hH)) (Dseq.intro (fmt_be16 _ _ (by bytes_at hH))
      (Dseq.intro (fmt_ipv4addr _ _ (by bytes_at hH)) (Dseq.intro (fmt_ipv4addr _ _ (by bytes_at hH))
      (Dnil.intro _))))))))))
  · show (Slice.from [] _).val = _; rw [Slice.from_val]
    rw [hhl, htake, List.drop_eq_nil_of_le (by omega)]
  · show (Slice.from T _).val = _; rw [Slice.from_val, hpay]
  · show (Slice.from [] _).val = _; rw [Slice.from_val]
    rw [htl, List.drop_eq_nil_of_le (by simp; omega)]
  · show (Slice.from [] _).val = _
    rw [Slice.from_val, hpay, hhdr, List.take_of_length_le (by omega),
      List.drop_eq_nil_of_le (by omega)]
  · show (Slice.from [] _).val = _
    rw [Slice.from_val, hpay, hhdr, List.drop_eq_nil_of_le (by omega)]

/-- **Spec theorem for `encode_ipv4`**: writes, if `out` has room, an IPv4
    packet that `Ipv4Tcp` accepts and decodes to these addresses and a bare
    header with these ports, numbers and flags. -/
@[step]
theorem encode_ipv4.spec (src dst : U32) (sp dp : U16) (seq ack : U32) (flags : U8)
    (out : Slice U8) :
    encode_ipv4 src dst sp dp seq ack flags out ⦃ (r : Option Usize) (out' : Slice U8) =>
      out'.length = out.length ∧
      match r with
      | none => out.length < 40
      | some n => n.val = 40 ∧
          ∃ t : Ipv4Tcp, Ipv4Tcp.Spec (out'.val.take n.val) t ∧ t.ip.header.src = src ∧
            t.ip.header.dst = dst ∧ t.header = bareHeader sp dp seq ack flags t.header.checksum ∧
            (t.payload : Slice U8).val = [] ⦄ := by
  unfold encode_ipv4
  step*
  have hP : PROTO_TCP.val = 6 := by simp
  rw [hP] at zero_post header_post
  have hHl : header.val.length = 20 := by simp
  have hTl : seg.val.length = 20 := by simp
  have hout : out2.val.take 40 = header.val ++ seg.val := by
    rw [out2_post, out1_post, s5_post, s6_post]
    simp only [Array.val_to_slice, Array.length_to_slice, List.take_zero, List.nil_append]
    rw [List.take_left' hHl, List.take_left' (by simp [hHl, hTl])]
  refine ⟨by simp only [Slice.length, out2_post, out1_post, s5_post, s6_post, List.length_append,
    List.length_take, List.length_drop, Array.val_to_slice]; simp; scalar_tac,
    by simp, ?_⟩
  rw [BARE_IPV4_LEN_val, hout]
  -- The IP header checksum.
  have hHb := vals_lt header.val
  rw [header_post] at hHb
  have hi2 := i2.hBounds
  simp only [UScalarTy.U16_numBits_eq] at hi2
  have hHc : inet.spec 0 header.val = 65535 := by
    rw [inet.spec_eq, header_post]
    have := fix_bytes 0 (by omega) ([69, 0] ++ be16N 40 ++ [0, 0, 64, 0, 64, 6])
      (be32N src.val ++ be32N dst.val) (by simp [be16N])
      (fun x hx => hHb x (by simp only [List.mem_append] at hx ⊢; tauto))
      (fun x hx => hHb x (by simp only [List.mem_append] at hx ⊢; tauto)) i2.val (by omega)
      (Or.inl (by rw [i2_post, i1_post, s_post, inet.spec_eq, Array.val_to_slice, zero_post]; simp))
    simpa using this
  -- The TCP checksum: the validator's sum is the encoder's.
  have hs1 : s1.val = (header.val.drop 12).take 8 := by
    rw [s1_post]; simp [List.slice]
  have hs1l : s1.val.length = 8 := by rw [hs1]; simp [hHl]
  have hs2 : s2.val = [0#u8, 6#u8, 0#u8, 20#u8] := by
    rw [s2_post]; simp [Array.make]
  have hs4 : s4.val = (inet.wordsN (s1.val.map (·.val) ++ [0, 6, 0, 20] ++
      tcpN sp dp seq ack flags 0)).foldl inet.add1c 0 := by
    rw [s4_post, acc1_post, acc_post, ← inet.spec_append 0 s1.val s2.val (by rw [hs1l]),
      ← inet.spec_append 0 (s1.val ++ s2.val) s3.val (by simp [hs1l, hs2]), inet.spec_eq, s3_post,
      Array.val_to_slice]
    simp [hs2, seg0_post]
  have hTc : ChecksumOk (pseudo4 (header.val ++ seg.val) seg.val) seg.val := by
    unfold ChecksumOk pseudo4
    have eA : (((header.val ++ seg.val).drop 12).take 8) = s1.val := by
      rw [hs1, List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp [hHl])]
    rw [eA, hTl]
    have hAb := vals_lt s1.val
    have hSb := vals_lt seg.val
    rw [seg_post] at hSb
    have hi3 := i3.hBounds
    simp only [UScalarTy.U16_numBits_eq] at hi3
    have := fix_bytes 0 (by omega) (s1.val.map (·.val) ++ [0, 6, 0, 20] ++
      (be16N sp.val ++ be16N dp.val ++ be32N seq.val ++ be32N ack.val ++ [80, flags.val, 0, 0]))
      [0, 0] (by simp [be16N, be32N, hs1l])
      (fun x hx => by
        simp only [List.mem_append] at hx
        rcases hx with (h | h) | h
        · exact hAb x h
        · simp at h; omega
        · exact hSb x (by simp only [tcpN, List.mem_append]; tauto))
      (by simp) i3.val (by omega)
      (Or.inl (by rw [i3_post, hs4]; simp [tcpN]))
    rw [seg_post]; simpa [tcpN] using this
  obtain ⟨t, ht, h1, h2, h3, h4⟩ :=
    ipv4_tcp_of_bytes header.val seg.val src dst i2 sp dp seq ack flags i3 header_post seg_post hHc hTc
  exact ⟨t, ht, h1, h2, by rw [h3]; rfl, h4⟩

/-! ## IPv6 -/

/-- **The bytes `encode_ipv6` writes form a TCP segment in an IPv6
    packet**: an IPv6 header `H` with next header 6, payload length 20 and
    these addresses, then a bare TCP header `T` with a valid checksum, decode
    to a segment with these addresses and header and no data. -/
theorem ipv6_tcp_of_bytes (H T : List U8) (src dst : U128) (sp dp : U16) (seq ack : U32)
    (flags : U8) (c : U16)
    (hH : H.map (·.val) = [96, 0, 0, 0] ++ be16N 20 ++ [6, 64] ++ be128N src.val ++
      be128N dst.val)
    (hT : T.map (·.val) = tcpN sp dp seq ack flags c.val)
    (hTc : ChecksumOk (pseudo6 (H ++ T) T) T) :
    ∃ t : Ipv6Tcp, Ipv6Tcp.Spec (H ++ T) t ∧ t.ip.header.src = src ∧ t.ip.header.dst = dst ∧
      t.header = bareHeader sp dp seq ack flags c ∧ (t.payload : Slice U8).val = [] := by
  obtain ⟨hTl, hseg, hhdr⟩ := segment_of_bytes T sp dp seq ack flags c hT
  have hHl : H.length = 40 := by
    have := congrArg List.length hH; simpa [be16N, be128N, be32N] using this
  have hvals : (H ++ T).map (·.val) = H.map (·.val) ++ T.map (·.val) := by simp
  have hend : ipv6.payloadEnd (H ++ T) = 60 := by
    unfold ipv6.payloadEnd; rw [beNat_eq, take_map, drop_map, hvals, hH]
    simp [beNatN, be16N]
  have hpay : ipv6.payloadOf (H ++ T) = T := by
    unfold ipv6.payloadOf
    rw [hend, List.take_of_length_le (by simp; omega), List.drop_left' hHl]
  have htake : (H ++ T).take 40 = H := List.take_left' hHl
  let hdr : ipv6.Ipv6Header :=
    { version_class_flow := ⟨0#u8, 0#u32⟩, payload_len := (20#u16 : U16),
      next_header := (6#u8 : U8), hop_limit := (64#u8 : U8), src := src, dst := dst }
  let ip : ipv6.Ipv6Packet :=
    { header := hdr, payload := Slice.from T (by rw [hTl]; scalar_tac),
      padding := Slice.from [] (by simp) }
  let e : Slice U8 := Slice.from [] (by simp)
  let t : Ipv6Tcp := { ip := ip, header := bareHeader sp dp seq ack flags c, options := e, payload := e }
  refine ⟨t, ?_, rfl, rfl, rfl, Slice.from_val _ _⟩
  refine ⟨⟨by simp [hHl, hTl], by rw [hend]; simp [hHl, hTl], ?_, ?_, ?_⟩,
    rfl, by rw [hpay]; exact hseg, by rw [hpay]; exact hTc, ?_, ?_⟩
  · rw [htake, show (40 : Nat) = 4 + (2 + (1 + (1 + (16 + (16 + 0))))) from rfl]
    exact Dseq.intro (fmt_versionClassFlow H (by bytes_at hH))
      (Dseq.intro (fmt_be16 _ _ (by bytes_at hH)) (Dseq.intro (fmt_be8 _ _ (by bytes_at hH))
      (Dseq.intro (fmt_be8 _ _ (by bytes_at hH)) (Dseq.intro (fmt_ipv6addr _ _ (by bytes_at hH))
      (Dseq.intro (fmt_ipv6addr _ _ (by bytes_at hH)) (Dnil.intro _))))))
  · show (Slice.from T _).val = _; rw [Slice.from_val, hpay]
  · show (Slice.from [] _).val = _
    rw [Slice.from_val, hend, List.drop_eq_nil_of_le (by simp; omega)]
  · show (Slice.from [] _).val = _
    rw [Slice.from_val, hpay, hhdr, List.take_of_length_le (by omega),
      List.drop_eq_nil_of_le (by omega)]
  · show (Slice.from [] _).val = _
    rw [Slice.from_val, hpay, hhdr, List.drop_eq_nil_of_le (by omega)]

/-- **Spec theorem for `encode_ipv6`**: writes, if `out` has room, an IPv6
    packet that `Ipv6Tcp` accepts and decodes to these addresses and a bare
    header with these ports, numbers and flags. -/
@[step]
theorem encode_ipv6.spec (src dst : U128) (sp dp : U16) (seq ack : U32) (flags : U8)
    (out : Slice U8) :
    encode_ipv6 src dst sp dp seq ack flags out ⦃ (r : Option Usize) (out' : Slice U8) =>
      out'.length = out.length ∧
      match r with
      | none => out.length < 60
      | some n => n.val = 60 ∧
          ∃ t : Ipv6Tcp, Ipv6Tcp.Spec (out'.val.take n.val) t ∧ t.ip.header.src = src ∧
            t.ip.header.dst = dst ∧ t.header = bareHeader sp dp seq ack flags t.header.checksum ∧
            (t.payload : Slice U8).val = [] ⦄ := by
  unfold encode_ipv6
  step*
  have hP : PROTO_TCP.val = 6 := by simp
  rw [hP] at header_post
  have hHl : header.val.length = 40 := by simp
  have hTl : seg.val.length = 20 := by simp
  have hout : out2.val.take 60 = header.val ++ seg.val := by
    rw [out2_post, out1_post, s4_post, s5_post]
    simp only [Array.val_to_slice, Array.length_to_slice, List.take_zero, List.nil_append]
    rw [List.take_left' hHl, List.take_left' (by simp [hHl, hTl])]
  refine ⟨by simp only [Slice.length, out2_post, out1_post, s4_post, s5_post, List.length_append,
    List.length_take, List.length_drop, Array.val_to_slice]; simp; scalar_tac,
    by simp, ?_⟩
  rw [BARE_IPV6_LEN_val, hout]
  have hs : s.val = (header.val.drop 8).take 32 := by
    rw [s_post]; simp [List.slice]
  have hsl : s.val.length = 32 := by rw [hs]; simp [hHl]
  have hs1 : s1.val = [0#u8, 0#u8, 0#u8, 20#u8, 0#u8, 0#u8, 0#u8, 6#u8] := by
    rw [s1_post]; simp [Array.make]
  have hs3 : s3.val = (inet.wordsN (s.val.map (·.val) ++ [0, 0, 0, 20, 0, 0, 0, 6] ++
      tcpN sp dp seq ack flags 0)).foldl inet.add1c 0 := by
    rw [s3_post, acc1_post, acc_post, ← inet.spec_append 0 s.val s1.val (by rw [hsl]),
      ← inet.spec_append 0 (s.val ++ s1.val) s2.val (by simp [hsl, hs1]), inet.spec_eq, s2_post,
      Array.val_to_slice]
    simp [hs1, seg0_post]
  have hTc : ChecksumOk (pseudo6 (header.val ++ seg.val) seg.val) seg.val := by
    unfold ChecksumOk pseudo6
    have eA : (((header.val ++ seg.val).drop 8).take 32) = s.val := by
      rw [hs, List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp [hHl])]
    rw [eA, hTl]
    have hAb := vals_lt s.val
    have hSb := vals_lt seg.val
    rw [seg_post] at hSb
    have hi1 := i1.hBounds
    simp only [UScalarTy.U16_numBits_eq] at hi1
    have := fix_bytes 0 (by omega) (s.val.map (·.val) ++ [0, 0, 0, 20, 0, 0, 0, 6] ++
      (be16N sp.val ++ be16N dp.val ++ be32N seq.val ++ be32N ack.val ++ [80, flags.val, 0, 0]))
      [0, 0] (by simp [be16N, be32N, hsl])
      (fun x hx => by
        simp only [List.mem_append] at hx
        rcases hx with (h | h) | h
        · exact hAb x h
        · simp at h; omega
        · exact hSb x (by simp only [tcpN, List.mem_append]; tauto))
      (by simp) i1.val (by omega)
      (Or.inl (by rw [i1_post, hs3]; simp [tcpN]))
    rw [seg_post]; simpa [tcpN] using this
  obtain ⟨t, ht, h1, h2, h3, h4⟩ :=
    ipv6_tcp_of_bytes header.val seg.val src dst sp dp seq ack flags i1 header_post seg_post hTc
  exact ⟨t, ht, h1, h2, by rw [h3]; rfl, h4⟩

end net.tcp
