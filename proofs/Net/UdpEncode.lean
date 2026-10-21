/- Specs of the UDP encoders of `net::udp`: `encode_ipv4` and `encode_ipv6`
   write packets that `Ipv4Udp` and `Ipv6Udp` accept and decode back to the
   same addresses, ports and data.

   The checksums rest on one fact about one's-complement sums: writing
   `0xFFFF - s` in a checksum field that was 0 when the sum `s` was taken
   makes the sum `0xFFFF` (`fix_checksum`). -/
import Net.UdpTop

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.inet

/-! ## One's-complement sums over byte values -/

/-- `words`, over the byte values. -/
def wordsN : List Nat → List Nat
  | a :: b :: t => (256 * a + b) :: wordsN t
  | [a] => [256 * a]
  | [] => []

theorem words_eq (l : List U8) : words l = wordsN (l.map (·.val)) := by
  induction l using words.induct with
  | case1 x y t ih => simp [words, wordsN, ih]
  | case2 x => simp [words, wordsN]
  | case3 => rfl

theorem spec_eq (acc : Nat) (l : List U8) :
    spec acc l = (wordsN (l.map (·.val))).foldl add1c acc := by
  rw [spec, words_eq]

theorem wordsN_append (a b : List Nat) (h : a.length % 2 = 0) :
    wordsN (a ++ b) = wordsN a ++ wordsN b := by
  induction a using wordsN.induct with
  | case1 x y t ih =>
    simp only [List.cons_append, wordsN, List.cons_append, List.cons.injEq, true_and]
    exact ih (by simp at h; omega)
  | case2 x => simp at h
  | case3 => rfl

theorem wordsN_le (l : List Nat) (h : ∀ x ∈ l, x < 256) : ∀ w ∈ wordsN l, w ≤ 65535 := by
  induction l using wordsN.induct with
  | case1 x y t ih =>
    intro w hw
    simp only [wordsN, List.mem_cons] at hw
    rcases hw with rfl | hw
    · have := h x (by simp); have := h y (by simp); omega
    · exact ih (fun z hz => h z (by simp [hz])) w hw
  | case2 x =>
    intro w hw; simp [wordsN] at hw; have := h x (by simp); omega
  | case3 => simp [wordsN]

theorem fold_le (ws : List Nat) (acc : Nat) (h : acc ≤ 65535) (hw : ∀ w ∈ ws, w ≤ 65535) :
    ws.foldl add1c acc ≤ 65535 := by
  induction ws generalizing acc with
  | nil => simpa
  | cons w t ih =>
    simp only [List.foldl_cons]
    apply ih _ (by unfold add1c; have := hw w (by simp); split <;> omega)
    exact fun x hx => hw x (by simp [hx])

theorem fold_mod (ws : List Nat) (acc : Nat) :
    ws.foldl add1c acc % 65535 = (acc + ws.sum) % 65535 := by
  induction ws generalizing acc with
  | nil => simp
  | cons w t ih =>
    simp only [List.foldl_cons, List.sum_cons, ih]
    unfold add1c; split <;> omega

theorem fold_zero (ws : List Nat) (acc : Nat) (h : ws.foldl add1c acc ≠ 0) :
    0 < acc ∨ ∃ w ∈ ws, 0 < w := by
  induction ws generalizing acc with
  | nil => simp at h; omega
  | cons w t ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨x, hx, hx'⟩
    · by_cases hw : 0 < w
      · exact Or.inr ⟨w, by simp, hw⟩
      · left; unfold add1c at h1; split at h1 <;> omega
    · exact Or.inr ⟨x, by simp [hx], hx'⟩

theorem fold_pos (ws : List Nat) (acc : Nat) (h : 0 < acc ∨ ∃ w ∈ ws, 0 < w) :
    0 < ws.foldl add1c acc := by
  induction ws generalizing acc with
  | nil => simp at h; simpa
  | cons w t ih =>
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨x, hx, hx'⟩
    · left; unfold add1c; split <;> omega
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · left; unfold add1c; split <;> omega
      · exact Or.inr ⟨x, hx, hx'⟩

/-- **Writing the complement of a sum into its checksum field**: if the
    words `ws1 ++ 0 :: ws2` sum to `s` from `acc`, then with the field set to
    `0xFFFF - s` (or to `0xFFFF` when `s` is `0xFFFF`, the other zero) they
    sum to `0xFFFF`. -/
theorem fix_checksum (acc : Nat) (hacc : acc ≤ 65535) (ws1 ws2 : List Nat)
    (hw : ∀ w ∈ ws1 ++ ws2, w ≤ 65535) (c : Nat)
    (hc : c = 65535 - (ws1 ++ 0 :: ws2).foldl add1c acc ∨
      ((ws1 ++ 0 :: ws2).foldl add1c acc = 65535 ∧ c = 65535)) :
    (ws1 ++ c :: ws2).foldl add1c acc = 65535 := by
  have hw' : ∀ w ∈ ws1 ++ 0 :: ws2, w ≤ 65535 := by
    intro w h; simp only [List.mem_append, List.mem_cons] at h
    rcases h with h | rfl | h
    · exact hw w (by simp [h])
    · omega
    · exact hw w (by simp [h])
  have hs := fold_le _ acc hacc hw'
  have hsm := fold_mod (ws1 ++ 0 :: ws2) acc
  have hc' : c ≤ 65535 := by omega
  have ht := fold_le (ws1 ++ c :: ws2) acc hacc (by
    intro w h; simp only [List.mem_append, List.mem_cons] at h
    rcases h with h | rfl | h
    · exact hw w (by simp [h])
    · exact hc'
    · exact hw w (by simp [h]))
  have htm := fold_mod (ws1 ++ c :: ws2) acc
  simp only [List.sum_append, List.sum_cons] at hsm htm
  -- The sum is not 0: the field is not, or the rest is not.
  have hpos : 0 < (ws1 ++ c :: ws2).foldl add1c acc := by
    apply fold_pos
    by_cases hc0 : 0 < c
    · exact Or.inr ⟨c, by simp, hc0⟩
    · have hs0 : (ws1 ++ 0 :: ws2).foldl add1c acc ≠ 0 := by omega
      rcases fold_zero _ _ hs0 with h | ⟨w, hw1, hw2⟩
      · exact Or.inl h
      · refine Or.inr ⟨w, ?_, hw2⟩
        simp only [List.mem_append, List.mem_cons] at hw1 ⊢
        rcases hw1 with h | rfl | h
        · exact Or.inl h
        · omega
        · exact Or.inr (Or.inr h)
  omega

end net.inet

namespace net.udp

/-! ## Bytes -/

/-- The bytes of a 16-bit value, big-endian, as numbers. -/
def be16N (v : Nat) : List Nat := [v / 256, v % 256]

/-- The bytes of a 32-bit value, big-endian, as numbers. -/
def be32N (v : Nat) : List Nat := [v / 16777216, v / 65536 % 256, v / 256 % 256, v % 256]

/-- The bytes of a 128-bit value, big-endian, as numbers. -/
def be128N (v : Nat) : List Nat :=
  be32N (v / 79228162514264337593543950336) ++ be32N (v / 18446744073709551616 % 4294967296) ++
    be32N (v / 4294967296 % 4294967296) ++ be32N (v % 4294967296)


theorem cast_u8 {ty : UScalarTy} (x : UScalar ty) :
    (UScalar.cast .U8 x).val = x.val % 256 := by
  rw [UScalar.cast_val_eq]; simp

@[simp, scalar_tac_simps] theorem TTL_val : TTL.val = 64 := by simp [TTL]
@[simp, scalar_tac_simps] theorem MAX_PACKET_LEN_val : MAX_PACKET_LEN.val = 65535 := by
  simp [MAX_PACKET_LEN]

/-! ## Headers, through their `Encode` impls -/

section
open untrusted.writer

theorem eq_of_vals {l1 l2 : List U8} (h : l1.map (·.val) = l2.map (·.val)) : l1 = l2 := by
  refine List.map_injective_iff.mpr ?_ h
  intro a b hab; exact (UScalar.eq_equiv a b).mpr hab

theorem beBytes_vals1 (x : Nat) (h : x < 256) : (beBytes 1 x).map (·.val) = [x] := by
  simp [beBytes]; omega

theorem beBytes_vals2 (x : Nat) (h : x < 65536) : (beBytes 2 x).map (·.val) = be16N x := by
  simp [beBytes, be16N]; omega

theorem beBytes_vals4 (x : Nat) (h : x < 4294967296) : (beBytes 4 x).map (·.val) = be32N x := by
  simp [beBytes, be32N, Nat.div_div_eq_div_mul]; omega

theorem beBytes_vals16 (x : Nat) (h : x < 2 ^ 128) : (beBytes 16 x).map (·.val) = be128N x := by
  simp [beBytes, be128N, be32N, Nat.div_div_eq_div_mul]; omega

/-- Bytes with the values of `v`'s encoding decode back to `v`, consuming
    them all. -/
theorem decodes_of_vals {T : Type} (enc : untrusted.writer.Encode T) (dec : Decode T)
    {E : T → List U8} {D : List U8 → T → Nat → Prop} {F : List U8 → Prop} [EncodesAs enc E]
    [DecodesAs dec D F] {V : T → Prop} [h : RoundTrip enc dec V] (v : T) (hv : V v)
    (l : List U8) (hl : l.map (·.val) = (E v).map (·.val)) : D l v l.length := by
  rw [eq_of_vals hl]
  simpa using h.roundtrip v [] hv

/-- The IPv4 header the encoders write. -/
def hdr4 (src dst : U32) (total : U16) (proto : U8) (checksum : U16) : ipv4.Ipv4Header :=
  { version_ihl := { ihl := 5#u8 }, tos := 0#u8, total_len := total, ident := 0#u16,
    fragment := { dont_fragment := true, more_fragments := false, offset := 0#u16 }, ttl := TTL,
    protocol := proto, checksum := checksum, src := src, dst := dst }

theorem hdr4_vals (src dst : U32) (total : U16) (proto : U8) (checksum : U16) :
    (FmtE ipv4.Ipv4Header.Insts.UntrustedWriterEncode (hdr4 src dst total proto checksum)).map
      (·.val) = [69, 0] ++ be16N total.val ++ [0, 0, 64, 0, 64, proto.val] ++
        be16N checksum.val ++ be32N src.val ++ be32N dst.val := by
  have h1 := total.hBounds; have h2 := checksum.hBounds; have h3 := src.hBounds
  have h4 := dst.hBounds; have h5 := proto.hBounds
  simp only [UScalarTy.U16_numBits_eq, UScalarTy.U32_numBits_eq, UScalarTy.U8_numBits_eq] at *
  simp only [FmtE, hdr4, Eseq, Enil, ipv4.Ipv4Header.fields, ipv4.Fragment.word, List.map_append,
    List.append_nil, List.append_assoc, beBytes_vals2 _ (by simpa using h1),
    beBytes_vals2 _ (by simpa using h2), beBytes_vals4 _ (by simpa using h3),
    beBytes_vals4 _ (by simpa using h4), beBytes_vals1 _ (by simpa using h5)]
  simp [beBytes, be16N]

/-- `hdr4` is a header the decoder accepts. -/
theorem hdr4_valid (src dst : U32) (total : U16) (proto : U8) (checksum : U16) :
    FmtV ipv4.Ipv4Header.Insts.UntrustedWriterEncode ipv4.Ipv4Header.Insts.UntrustedReaderDecode
      (hdr4 src dst total proto checksum) := by
  unfold FmtV
  simp only [Vseq, Vnil, ipv4.Ipv4Header.fields, hdr4]
  simp

/-- **Spec theorem for `ipv4_header`**: the bytes of `hdr4`. -/
@[step]
theorem ipv4_header.spec (src dst : U32) (total : U16) (proto : U8) (checksum : U16) :
    ipv4_header src dst total proto checksum ⦃ (r : Array U8 20#usize) =>
      r.val.map (·.val) = [69, 0] ++ be16N total.val ++ [0, 0, 64, 0, 64, proto.val] ++
        be16N checksum.val ++ be32N src.val ++ be32N dst.val ⦄ := by
  unfold ipv4_header
  apply WP.spec_mono (encode_into_fresh _ _ 20#usize (by simp [Eseq, Enil, ipv4.Ipv4Header.fields]))
  intro r hr
  rw [hr]
  exact hdr4_vals src dst total proto checksum

/-- The IPv6 header the encoders write. -/
def hdr6 (src dst : U128) (len : U16) (next : U8) : ipv6.Ipv6Header :=
  { version_class_flow := { traffic_class := 0#u8, flow_label := 0#u32 }, payload_len := len,
    next_header := next, hop_limit := TTL, src := src, dst := dst }

theorem hdr6_vals (src dst : U128) (len : U16) (next : U8) :
    (FmtE ipv6.Ipv6Header.Insts.UntrustedWriterEncode (hdr6 src dst len next)).map (·.val) =
      [96, 0, 0, 0] ++ be16N len.val ++ [next.val, 64] ++ be128N src.val ++ be128N dst.val := by
  have h1 := len.hBounds; have h3 := src.hBounds; have h4 := dst.hBounds; have h5 := next.hBounds
  simp only [UScalarTy.U16_numBits_eq, UScalarTy.U128_numBits_eq, UScalarTy.U8_numBits_eq] at *
  simp only [FmtE, hdr6, Eseq, Enil, ipv6.Ipv6Header.fields, ipv6.VersionClassFlow.word,
    List.map_append, List.append_nil, List.append_assoc, beBytes_vals2 _ (by simpa using h1),
    beBytes_vals16 _ (by simpa using h3), beBytes_vals16 _ (by simpa using h4),
    beBytes_vals1 _ (by simpa using h5)]
  simp [beBytes]

/-- `hdr6` is a header the decoder accepts. -/
theorem hdr6_valid (src dst : U128) (len : U16) (next : U8) :
    FmtV ipv6.Ipv6Header.Insts.UntrustedWriterEncode ipv6.Ipv6Header.Insts.UntrustedReaderDecode
      (hdr6 src dst len next) := by
  unfold FmtV
  simp only [Vseq, Vnil, ipv6.Ipv6Header.fields, hdr6]
  simp

/-- **Spec theorem for `ipv6_header`**: the bytes of `hdr6`. -/
@[step]
theorem ipv6_header.spec (src dst : U128) (len : U16) (next : U8) :
    ipv6_header src dst len next ⦃ (r : Array U8 40#usize) =>
      r.val.map (·.val) = [96, 0, 0, 0] ++ be16N len.val ++ [next.val, 64] ++ be128N src.val ++
        be128N dst.val ⦄ := by
  unfold ipv6_header
  apply WP.spec_mono (encode_into_fresh _ _ 40#usize (by simp [Eseq, Enil, ipv6.Ipv6Header.fields]))
  intro r hr
  rw [hr]
  exact hdr6_vals src dst len next

/-- The UDP header the encoders write. -/
def udpHdr (sp dp len checksum : U16) : UdpHeader :=
  { src_port := sp, dst_port := dp, length := len, checksum := checksum }

theorem udpHdr_vals (sp dp len checksum : U16) :
    (FmtE UdpHeader.Insts.UntrustedWriterEncode (udpHdr sp dp len checksum)).map (·.val) =
      be16N sp.val ++ be16N dp.val ++ be16N len.val ++ be16N checksum.val := by
  have h1 := sp.hBounds; have h2 := dp.hBounds; have h3 := len.hBounds; have h4 := checksum.hBounds
  simp only [UScalarTy.U16_numBits_eq] at h1 h2 h3 h4
  simp only [FmtE, udpHdr, Eseq, Enil, UdpHeader.fields, List.map_append, List.append_nil,
    List.append_assoc, beBytes_vals2 _ (by simpa using h1), beBytes_vals2 _ (by simpa using h2),
    beBytes_vals2 _ (by simpa using h3), beBytes_vals2 _ (by simpa using h4)]

/-- **Spec theorem for `udp_header`**: the bytes of `udpHdr`. -/
@[step]
theorem udp_header.spec (sp dp len checksum : U16) :
    udp_header sp dp len checksum ⦃ (r : Array U8 8#usize) =>
      r.val.map (·.val) = be16N sp.val ++ be16N dp.val ++ be16N len.val ++ be16N checksum.val ⦄ := by
  unfold udp_header
  apply WP.spec_mono (encode_into_fresh _ _ 8#usize (by simp [Eseq, Enil, UdpHeader.fields]))
  intro r hr
  rw [hr]
  exact udpHdr_vals sp dp len checksum

end

/-- **Spec theorem for `udp_checksum`**. -/
@[step]
theorem udp_checksum.spec (s : U16) :
    udp_checksum s ⦃ (r : U16) => r.val = if s.val = 65535 then 65535 else 65535 - s.val ⦄ := by
  unfold udp_checksum
  split
  · simp_all
  · step*

/-- **Spec theorem for `put_bytes`'s loop**. -/
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

/-- **Spec theorem for `put_bytes`**: writes `src` at `pos`. -/
@[step]
theorem put_bytes.spec (out : Slice U8) (pos : Usize) (src : Slice U8)
    (h : pos.val + src.length ≤ out.length) :
    put_bytes out pos src ⦃ (out' : Slice U8) =>
      out'.val = out.val.take pos.val ++ src.val ++ out.val.drop (pos.val + src.length) ⦄ := by
  unfold put_bytes
  step*
  simpa using out'_post

end net.udp

namespace net.ipv4

/-- **Spec theorem for `Fragment::is_fragment`**. -/
@[step]
theorem Fragment.is_fragment.spec (f : Fragment) :
    Fragment.is_fragment f ⦃ (r : Bool) => (r = true ↔ f.more_fragments = true ∨ f.offset.val ≠ 0) ⦄ := by
  unfold Fragment.is_fragment
  split <;> simp_all [UScalar.neq_to_neq_val]

end net.ipv4

namespace net.udp

/-! ## Fields from bytes -/

/-- `beNat`, over the byte values. -/
def beNatN (l : List Nat) : Nat := l.foldl (fun acc x => acc * 256 + x) 0

theorem beNat_eq (l : List U8) : beNat l = beNatN (l.map (·.val)) := by
  simp only [beNat, beNatN, List.foldl_map]

theorem take_map (l : List U8) (k : Nat) : (l.take k).map (·.val) = (l.map (·.val)).take k :=
  List.map_take ..

theorem drop_map (l : List U8) (k : Nat) : (l.drop k).map (·.val) = (l.map (·.val)).drop k :=
  List.map_drop ..

/-! ## IPv4 -/

/-- **The bytes `encode_ipv4` writes form a UDP datagram in an IPv4
    packet**: an IPv4 header `H` without options with valid checksum, total
    length and these addresses, then a UDP header `U` with these ports and a
    valid checksum, then the data `D`, decode to a datagram with these
    addresses, ports and data. -/
theorem ipv4_udp_of_bytes (H U D : List U8) (src dst : U32) (total cs sp dp len ucs : U16)
    (hH : H.map (·.val) = [69, 0] ++ be16N total.val ++ [0, 0, 64, 0, 64, 17] ++ be16N cs.val ++
      be32N src.val ++ be32N dst.val)
    (hU : U.map (·.val) = be16N sp.val ++ be16N dp.val ++ be16N len.val ++ be16N ucs.val)
    (htot : total.val = 28 + D.length) (hlen : len.val = 8 + D.length)
    (hHc : inet.spec 0 H = 65535)
    (hUc : inet.spec 0 (ipv4Pseudo (H ++ U ++ D) (U ++ D) ++ (U ++ D)) = 65535) :
    ∃ u : Ipv4Udp, Ipv4Udp.Spec (H ++ U ++ D) u ∧ u.ip.header.src = src ∧
      u.ip.header.dst = dst ∧ u.header.src_port = sp ∧ u.header.dst_port = dp ∧
      (u.payload : Slice U8).val = D := by
  have hHl : H.length = 20 := by
    have := congrArg List.length hH; simpa [be16N, be32N] using this
  have hUl : U.length = 8 := by
    have := congrArg List.length hU; simpa [be16N] using this
  have hmax : 28 + D.length ≤ Usize.max := by
    have := total.hBounds; simp only [UScalarTy.U16_numBits_eq] at this; scalar_tac
  have hvals : (H ++ U ++ D).map (·.val) = H.map (·.val) ++ U.map (·.val) ++ D.map (·.val) := by
    simp
  have hhl : ipv4.headerLen (H ++ U ++ D) = 20 := by
    unfold ipv4.headerLen; rw [beNat_eq, take_map, hvals, hH]; simp [beNatN]
  have htl : ipv4.totalLen (H ++ U ++ D) = total.val := by
    unfold ipv4.totalLen; rw [beNat_eq, take_map, drop_map, hvals, hH]
    simp [beNatN, be16N]; omega
  have hpay : ipv4.payloadOf (H ++ U ++ D) = U ++ D := by
    unfold ipv4.payloadOf
    rw [htl, hhl, htot, List.take_of_length_le (by simp; omega), List.append_assoc,
      List.drop_left' hHl]
  have htake : (H ++ U ++ D).take 20 = H := by
    rw [List.append_assoc, List.take_left' hHl]
  let hdr := hdr4 src dst total 17#u8 cs
  let ip : ipv4.Ipv4Packet :=
    { header := hdr, options := Slice.from [] (by simp),
      payload := Slice.from (U ++ D) (by simp; omega), padding := Slice.from [] (by simp) }
  let uh := udpHdr sp dp len ucs
  refine ⟨{ ip, header := uh, payload := Slice.from D (by omega) }, ?_, rfl, rfl, rfl, rfl,
    Slice.from_val _ _⟩
  refine ⟨⟨by simp [hHl, hUl], by rw [hhl], by rw [hhl, htl]; omega,
    by rw [htl]; simp [hHl, hUl]; omega, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, by rw [hpay]; simp; omega, ?_, ?_, Or.inr ?_, ?_⟩
  · rw [hhl, htake]; exact hHc
  · rw [htake]
    have := decodes_of_vals ipv4.Ipv4Header.Insts.UntrustedWriterEncode
      ipv4.Ipv4Header.Insts.UntrustedReaderDecode hdr (hdr4_valid ..) H (by rw [hH, hdr4_vals]; simp)
    rwa [hHl] at this
  · show (Slice.from [] _).val = _; rw [Slice.from_val]
    rw [hhl, htake, List.drop_eq_nil_of_le (by omega)]
  · show (Slice.from (U ++ D) _).val = _; rw [Slice.from_val, hpay]
  · show (Slice.from [] _).val = _; rw [Slice.from_val]
    rw [htl, htot, List.drop_eq_nil_of_le (by simp; omega)]
  · rw [hpay, List.take_left' hUl]
    have := decodes_of_vals UdpHeader.Insts.UntrustedWriterEncode
      UdpHeader.Insts.UntrustedReaderDecode uh (by unfold untrusted.writer.FmtV; simp [untrusted.writer.Vseq, untrusted.writer.Vnil])
      U (by rw [hU, udpHdr_vals])
    rwa [hUl] at this
  · show len.val = _; rw [hpay]; simp; omega
  · rw [hpay]; exact hUc
  · show (Slice.from D _).val = _; rw [Slice.from_val, hpay, List.drop_left' hUl]

/-! ## IPv6 -/

/-- **The bytes `encode_ipv6` writes form a UDP datagram in an IPv6
    packet**: an IPv6 header `H` with these addresses and payload length,
    then a UDP header `U` with these ports and a valid, non-zero checksum,
    then the data `D`, decode to a datagram with these addresses, ports and
    data. -/
theorem ipv6_udp_of_bytes (H U D : List U8) (src dst : U128) (sp dp len ucs : U16)
    (hH : H.map (·.val) = [96, 0, 0, 0] ++ be16N len.val ++ [17, 64] ++ be128N src.val ++
      be128N dst.val)
    (hU : U.map (·.val) = be16N sp.val ++ be16N dp.val ++ be16N len.val ++ be16N ucs.val)
    (hlen : len.val = 8 + D.length) (hucs : ucs.val ≠ 0)
    (hUc : inet.spec 0 (ipv6.pseudo (H ++ U ++ D) (((U ++ D).drop 4).take 2) 17#u8 ++ (U ++ D)) =
      65535) :
    ∃ u : Ipv6Udp, Ipv6Udp.Spec (H ++ U ++ D) u ∧ u.ip.header.src = src ∧
      u.ip.header.dst = dst ∧ u.header.src_port = sp ∧ u.header.dst_port = dp ∧
      (u.payload : Slice U8).val = D := by
  have hHl : H.length = 40 := by
    have := congrArg List.length hH; simpa [be16N, be128N, be32N] using this
  have hUl : U.length = 8 := by
    have := congrArg List.length hU; simpa [be16N] using this
  have hmax : 48 + D.length ≤ Usize.max := by
    have := len.hBounds; simp only [UScalarTy.U16_numBits_eq] at this; scalar_tac
  have hvals : (H ++ U ++ D).map (·.val) = H.map (·.val) ++ U.map (·.val) ++ D.map (·.val) := by
    simp
  have hend : ipv6.payloadEnd (H ++ U ++ D) = 40 + len.val := by
    unfold ipv6.payloadEnd; rw [beNat_eq, take_map, drop_map, hvals, hH]
    simp [beNatN, be16N]; omega
  have hpay : ipv6.payloadOf (H ++ U ++ D) = U ++ D := by
    unfold ipv6.payloadOf
    rw [hend, hlen, List.take_of_length_le (by simp; omega), List.append_assoc,
      List.drop_left' hHl]
  have htake : (H ++ U ++ D).take 40 = H := by
    rw [List.append_assoc, List.take_left' hHl]
  let hdr := hdr6 src dst len 17#u8
  let ip : ipv6.Ipv6Packet :=
    { header := hdr, payload := Slice.from (U ++ D) (by simp; omega),
      padding := Slice.from [] (by simp) }
  let uh := udpHdr sp dp len ucs
  refine ⟨{ ip, header := uh, payload := Slice.from D (by omega) }, ?_, rfl, rfl, rfl, rfl,
    Slice.from_val _ _⟩
  refine ⟨⟨by simp [hHl, hUl], by rw [hend]; simp [hHl, hUl]; omega, ?_, ?_, ?_⟩,
    rfl, by rw [hpay]; simp; omega, ?_, ?_, hucs, ?_, ?_⟩
  · rw [htake]
    have := decodes_of_vals ipv6.Ipv6Header.Insts.UntrustedWriterEncode
      ipv6.Ipv6Header.Insts.UntrustedReaderDecode hdr (hdr6_valid ..) H (by rw [hH, hdr6_vals]; simp)
    rwa [hHl] at this
  · show (Slice.from (U ++ D) _).val = _; rw [Slice.from_val, hpay]
  · show (Slice.from [] _).val = _
    rw [Slice.from_val, hend, hlen, List.drop_eq_nil_of_le (by simp; omega)]
  · rw [hpay, List.take_left' hUl]
    have := decodes_of_vals UdpHeader.Insts.UntrustedWriterEncode
      UdpHeader.Insts.UntrustedReaderDecode uh (by unfold untrusted.writer.FmtV; simp [untrusted.writer.Vseq, untrusted.writer.Vnil])
      U (by rw [hU, udpHdr_vals])
    rwa [hUl] at this
  · show len.val = _; rw [hpay]; simp; omega
  · rw [hpay]; exact hUc
  · show (Slice.from D _).val = _; rw [Slice.from_val, hpay, List.drop_left' hUl]

/-! ## The encoders -/

theorem vals_lt (l : List U8) : ∀ x ∈ l.map (·.val), x < 256 := by
  intro x hx; simp at hx; obtain ⟨a, -, rfl⟩ := hx; have := a.hBounds; simpa using this

/-- The checksum algebra on bytes: `P`, then a checksum field, then `Q`. -/
theorem fix_bytes (acc : Nat) (hacc : acc ≤ 65535) (P Q : List Nat) (hP : P.length % 2 = 0)
    (hPb : ∀ x ∈ P, x < 256) (hQb : ∀ x ∈ Q, x < 256) (c : Nat) (hc0 : c ≤ 65535)
    (hc : c = 65535 - (inet.wordsN (P ++ be16N 0 ++ Q)).foldl inet.add1c acc ∨
      ((inet.wordsN (P ++ be16N 0 ++ Q)).foldl inet.add1c acc = 65535 ∧ c = 65535)) :
    (inet.wordsN (P ++ be16N c ++ Q)).foldl inet.add1c acc = 65535 := by
  have hw : ∀ v : Nat, v ≤ 65535 →
      inet.wordsN (P ++ be16N v ++ Q) = inet.wordsN P ++ v :: inet.wordsN Q := by
    intro v hv
    rw [List.append_assoc, inet.wordsN_append _ _ hP]
    simp only [be16N, List.cons_append, List.nil_append, inet.wordsN]
    congr 2; omega
  rw [hw 0 (by omega)] at hc
  rw [hw c hc0]
  apply inet.fix_checksum acc hacc _ _ _ c hc
  intro w h
  simp only [List.mem_append] at h
  rcases h with h | h
  · exact inet.wordsN_le P hPb w h
  · exact inet.wordsN_le Q hQb w h

/-- **Spec theorem for `encode_ipv4`**: writes, if `out` has room and the
    data fits in a packet, an IPv4 packet that `Ipv4Udp` accepts and decodes
    to these addresses, ports and data. -/
@[step]
theorem encode_ipv4.spec (src dst : U32) (sp dp : U16) (data out : Slice U8) :
    encode_ipv4 src dst sp dp data out ⦃ (r : Option Usize) (out' : Slice U8) =>
      out'.length = out.length ∧
      match r with
      | none => 65507 < data.length ∨ out.length < 28 + data.length
      | some n => n.val = 28 + data.length ∧
          ∃ u : Ipv4Udp, Ipv4Udp.Spec (out'.val.take n.val) u ∧ u.ip.header.src = src ∧
            u.ip.header.dst = dst ∧ u.header.src_port = sp ∧ u.header.dst_port = dp ∧
            (u.payload : Slice U8).val = data.val ⦄ := by
  unfold encode_ipv4
  step*
  · rw [s7_post]; simp only [Slice.length, out1_post, s6_post, List.length_append,
      List.length_take, List.length_drop, Array.length_to_slice]
    simp; scalar_tac
  · simp only [Slice.length, out2_post, out1_post, s6_post, s7_post, List.length_append,
      List.length_take, List.length_drop]
    simp; scalar_tac
  have hP : ipv4.PROTO_UDP.val = 17 := by simp [ipv4.PROTO_UDP]
  rw [hP] at header_post zero_post
  have hnv : n.val = 28 + data.length := by scalar_tac
  have hnl : n.val ≤ out.length := by scalar_tac
  have htot : total.val = n.val := by
    rw [total_post, UScalar.cast_val_eq]; simp only [UScalarTy.U16_numBits_eq]; scalar_tac
  have hlen : len.val = 8 + data.length := by
    rw [len_post, UScalar.cast_val_eq]; simp only [UScalarTy.U16_numBits_eq]; scalar_tac
  have hHl : header.val.length = 20 := by simp
  have hUl : datagram_header.val.length = 8 := by simp
  have hout3 : out3.val.take n.val = header.val ++ datagram_header.val ++ data.val := by
    have h1 : out1.val = header.val ++ out.val.drop 20 := by
      rw [out1_post, s6_post]; simp
    have h2 : out2.val = header.val ++ datagram_header.val ++ out.val.drop 28 := by
      rw [out2_post, s7_post, h1]
      simp only [Array.val_to_slice, Array.length_to_slice]
      rw [List.take_left' hHl]
      simp [List.drop_append, hHl]
    have h3 : out3.val = header.val ++ datagram_header.val ++ data.val ++ out.val.drop n.val := by
      rw [out3_post, h2]
      have e1 : (header.val ++ datagram_header.val ++ out.val.drop 28).take 28 =
          header.val ++ datagram_header.val := List.take_left' (by simp [hHl, hUl])
      have e2 : (header.val ++ datagram_header.val ++ out.val.drop 28).drop (28 + data.length) =
          out.val.drop n.val := by
        rw [show 28 + data.length = (header.val ++ datagram_header.val).length + data.length by
          simp [hHl, hUl], ← List.drop_drop, List.drop_left, List.drop_drop]
        congr 1; omega
      rw [e1, e2]
    rw [h3, List.take_left' (by simp [hHl, hUl, hnv]; omega)]
  refine ⟨?_, hnv, ?_⟩
  · simp only [Slice.length, out3_post, out2_post, out1_post, s6_post, s7_post,
      List.length_append, List.length_take, List.length_drop]
    simp; scalar_tac
  rw [hout3]
  -- The IP header checksum.
  have hHb := vals_lt header.val
  rw [header_post] at hHb
  have hi6 := i6.hBounds
  simp only [UScalarTy.U16_numBits_eq] at hi6
  have hHc : inet.spec 0 header.val = 65535 := by
    rw [inet.spec_eq, header_post]
    have := fix_bytes 0 (by omega) ([69, 0] ++ be16N total.val ++ [0, 0, 64, 0, 64, 17])
      (be32N src.val ++ be32N dst.val) (by simp [be16N])
      (fun x hx => hHb x (by simp only [List.mem_append] at hx ⊢; tauto))
      (fun x hx => hHb x (by simp only [List.mem_append] at hx ⊢; tauto)) i6.val (by omega)
      (Or.inl (by rw [i6_post, i5_post, s_post, inet.spec_eq, Array.val_to_slice, zero_post]; simp))
    simpa using this
  -- The UDP checksum: the validator's sum is the encoder's, piece by piece.
  have hUc : inet.spec 0 (ipv4Pseudo (header.val ++ datagram_header.val ++ data.val)
      (datagram_header.val ++ data.val) ++ (datagram_header.val ++ data.val)) = 65535 := by
    rw [sum_ipv4Pseudo _ _ (by simp [hHl]) (by simp [hUl]; omega)]
    have eX : ((header.val ++ datagram_header.val ++ data.val).drop 12).take 8 = s1.val := by
      rw [s1_post, List.append_assoc]; simp [List.slice, List.take_append, List.drop_append, hHl]
    have eY : (datagram_header.val ++ data.val).slice 4 6 = s3.val := by
      rw [s3_post]
      apply eq_of_vals
      simp only [List.slice, Array.val_to_slice, List.map_take, List.map_drop, List.map_append,
        datagram_header_post, udp0_post]
      simp [be16N]
    have eS2 : s2.val = [0#u8, 17#u8] := by rw [s2_post]; simp [Array.make, ipv4.PROTO_UDP]
    rw [eX, eY, ← eS2, ← acc_post, ← acc1_post, ← acc2_post, inet.spec_eq, List.map_append,
      datagram_header_post]
    have hUb := vals_lt datagram_header.val
    rw [datagram_header_post] at hUb
    have hi7 := i7.hBounds
    simp only [UScalarTy.U16_numBits_eq] at hi7
    have ha2 := acc2.hBounds
    simp only [UScalarTy.U16_numBits_eq] at ha2
    have hs5 : s5.val = (inet.wordsN (be16N sp.val ++ be16N dp.val ++ be16N len.val ++ be16N 0 ++
        data.val.map (·.val))).foldl inet.add1c acc2.val := by
      rw [s5_post, acc3_post, s4_post, ← inet.spec_append _ _ _ (by simp), inet.spec_eq,
        List.map_append, Array.val_to_slice, udp0_post]
    refine fix_bytes acc2.val (by omega) (be16N sp.val ++ be16N dp.val ++ be16N len.val) _
      (by simp [be16N]) (fun x hx => hUb x (by simp only [List.mem_append] at hx ⊢; tauto))
      (vals_lt _) i7.val (by omega) ?_
    rw [← hs5, i7_post]
    split
    · exact Or.inr ⟨by assumption, rfl⟩
    · exact Or.inl rfl
  exact ipv4_udp_of_bytes header.val datagram_header.val data.val src dst total i6 sp dp len i7
    header_post datagram_header_post (by rw [htot, hnv]) hlen hHc hUc

/-- **Spec theorem for `encode_ipv6`**: writes, if `out` has room and the
    data fits in a datagram, an IPv6 packet that `Ipv6Udp` accepts and decodes
    to these addresses, ports and data. -/
@[step]
theorem encode_ipv6.spec (src dst : U128) (sp dp : U16) (data out : Slice U8) :
    encode_ipv6 src dst sp dp data out ⦃ (r : Option Usize) (out' : Slice U8) =>
      out'.length = out.length ∧
      match r with
      | none => 65527 < data.length ∨ out.length < 48 + data.length
      | some n => n.val = 48 + data.length ∧
          ∃ u : Ipv6Udp, Ipv6Udp.Spec (out'.val.take n.val) u ∧ u.ip.header.src = src ∧
            u.ip.header.dst = dst ∧ u.header.src_port = sp ∧ u.header.dst_port = dp ∧
            (u.payload : Slice U8).val = data.val ⦄ := by
  unfold encode_ipv6
  step*
  all_goals try (simp only [Slice.length, out1_post, out2_post, s6_post, s7_post,
    List.length_append, List.length_take, List.length_drop, Array.val_to_slice]; simp; scalar_tac)
  have hN : ipv6.NEXT_UDP.val = 17 := by simp [ipv6.NEXT_UDP]
  rw [hN] at header_post
  have hnv : n.val = 48 + data.length := by scalar_tac
  have hnl : n.val ≤ out.length := by scalar_tac
  have hlen : len.val = 8 + data.length := by
    rw [len_post, UScalar.cast_val_eq]; simp only [UScalarTy.U16_numBits_eq]; scalar_tac
  have hHl : header.val.length = 40 := by simp
  have hUl : datagram_header.val.length = 8 := by simp
  have h1 : out1.val = header.val ++ out.val.drop 40 := by
    rw [out1_post, s6_post]; simp
  have h2 : out2.val = header.val ++ datagram_header.val ++ out.val.drop 48 := by
    rw [out2_post, s7_post, h1]
    simp only [Array.val_to_slice, Array.length_to_slice]
    rw [List.take_left' hHl]
    simp [List.drop_append, hHl]
  have h3 : out3.val = header.val ++ datagram_header.val ++ data.val ++ out.val.drop n.val := by
    rw [out3_post]
    have e1 : (header.val ++ datagram_header.val ++ out.val.drop 48).take 48 =
        header.val ++ datagram_header.val := List.take_left' (by simp [hHl, hUl])
    have e2 : (header.val ++ datagram_header.val ++ out.val.drop 48).drop (48 + data.length) =
        out.val.drop n.val := by
      rw [show 48 + data.length = (header.val ++ datagram_header.val).length + data.length by
        simp [hHl, hUl], ← List.drop_drop, List.drop_left, List.drop_drop]
      congr 1; omega
    rw [h2, e1, e2]
  have hnl' : n.val ≤ out.val.length := hnl
  refine ⟨by simp only [Slice.length, h3, List.length_append, List.length_drop]; simp [hHl, hUl]; have : n.val = 48 + data.val.length := hnv; omega,
    hnv, ?_⟩
  rw [h3, List.take_left' (by simp [hHl, hUl, hnv]; omega)]
  have hi5 := i5.hBounds
  simp only [UScalarTy.U16_numBits_eq] at hi5
  have hs5 := s5.hBounds
  simp only [UScalarTy.U16_numBits_eq] at hs5
  have hnz : i5.val ≠ 0 := by rw [i5_post]; split <;> omega
  have hUc : inet.spec 0 (ipv6.pseudo (header.val ++ datagram_header.val ++ data.val)
      (((datagram_header.val ++ data.val).drop 4).take 2) 17#u8 ++
      (datagram_header.val ++ data.val)) = 65535 := by
    rw [ipv6.sum_pseudo _ _ _ _ (by simp [hHl]) (by simp [hUl]; omega)]
    have eX : ((header.val ++ datagram_header.val ++ data.val).drop 8).take 32 = s.val := by
      rw [s_post, List.append_assoc]; simp [List.slice, List.take_append, List.drop_append, hHl]
    have eY : ((datagram_header.val ++ data.val).drop 4).take 2 = s2.val := by
      rw [s2_post]
      apply eq_of_vals
      simp only [List.slice, Array.val_to_slice, List.map_take, List.map_drop, List.map_append,
        datagram_header_post, udp0_post]
      simp [be16N]
    have eS1 : s1.val = [0#u8, 0#u8] := by rw [s1_post]; simp [Array.repeat_val]
    have eS3 : s3.val = [0#u8, 0#u8, 0#u8, 17#u8] := by
      rw [s3_post]; simp [Array.make, ipv6.NEXT_UDP]
    rw [eX, eY, ← eS1, ← eS3, ← acc_post, ← acc1_post, ← acc2_post, ← acc3_post, inet.spec_eq,
      List.map_append, datagram_header_post]
    have hUb := vals_lt datagram_header.val
    rw [datagram_header_post] at hUb
    have ha3 := acc3.hBounds
    simp only [UScalarTy.U16_numBits_eq] at ha3
    have hs5' : s5.val = (inet.wordsN (be16N sp.val ++ be16N dp.val ++ be16N len.val ++ be16N 0 ++
        data.val.map (·.val))).foldl inet.add1c acc3.val := by
      rw [s5_post, acc4_post, s4_post, ← inet.spec_append _ _ _ (by simp), inet.spec_eq,
        List.map_append, Array.val_to_slice, udp0_post]
    refine fix_bytes acc3.val (by omega) (be16N sp.val ++ be16N dp.val ++ be16N len.val) _
      (by simp [be16N]) (fun x hx => hUb x (by simp only [List.mem_append] at hx ⊢; tauto))
      (vals_lt _) i5.val (by omega) ?_
    rw [← hs5', i5_post]
    split
    · exact Or.inr ⟨by assumption, rfl⟩
    · exact Or.inl rfl
  exact ipv6_udp_of_bytes header.val datagram_header.val data.val src dst sp dp len i5
    header_post datagram_header_post hlen hnz hUc

end net.udp
