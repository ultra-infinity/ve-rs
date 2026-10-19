/- Hand-written spec of `<Ipv6Packet as Validate<&[u8]>>::validate`. -/
import Net.Manual
import Net.Specs.Ipv6Header

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.ipv6

/-- The payload of the IPv6 packet `l`: the bytes `[40, end)`. -/
def payloadOf (l : List U8) : List U8 := (l.take (payloadEnd l)).drop 40

/-- `l` is a well-formed IPv6 packet, possibly followed by link-layer padding,
    that decodes to `p`: it has at least `end = 40 + payload length` bytes,
    the first 40 decode as `p.header`, and `p.payload` and `p.padding` are the
    bytes `[40, end)` and `[end, …)`. -/
def Ipv6Packet.Spec (l : List U8) (p : Ipv6Packet) : Prop :=
  40 ≤ l.length ∧ payloadEnd l ≤ l.length ∧
    FmtD Ipv6Header.Insts.UntrustedReaderDecode (l.take 40) p.header 40 ∧
    (p.payload : Slice U8).val = payloadOf l ∧
    (p.padding : Slice U8).val = l.drop (payloadEnd l)

/-- **Spec theorem for `<Ipv6Packet as Validate<&[u8]>>::validate`**: accepts
    exactly the well-formed IPv6 packets, and returns their decoding. -/
@[step]
theorem _root_.net.ipv6.Ipv6Packet.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Ipv6Packet.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Ipv6Packet ValidationError) =>
        match r with
        | .Ok p => Ipv6Packet.Spec input.val p
        | .Err _ => ∀ p, ¬ Ipv6Packet.Spec input.val p ⦄ := by
  unfold Ipv6Packet.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  dsimp only
  split
  · simp only [WP.spec_ok]
    rintro p ⟨h40, -⟩
    scalar_tac
  · step*
    · rintro p ⟨-, hle, -⟩
      scalar_tac
    · have hu : (u : Slice U8).val = input.val.take 40 := by
        rw [u_post, s_post]; simp [List.slice]
      have hlen : (input.val.take 40).length = 40 := by
        simp only [List.length_take]; scalar_tac
      apply WP.spec_bind
        (UntrustedShared0SliceU8.read_all.spec_of Ipv6Header.Insts.UntrustedReaderDecode u)
      rintro (h | e) hres
      · simp only [hu, hlen] at hres
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step*
        · have : 40 ≤ «end».val := by rw [end_post, payloadEnd]; omega
          simp only [UScalar.le_equiv, HEADER_LEN_val]; exact this
        refine ⟨by scalar_tac, by scalar_tac, hres, ?_, ?_⟩
        · rw [u1_post, s1_post, end_post]; simp [payloadOf, List.slice, List.drop_take]
        · rw [u2_post, s2_post, end_post]
      · simp only [hu, hlen] at hres
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
        rintro p ⟨-, -, hD, -⟩
        exact hres p.header hD

/-! ## Consequences of the spec, for the layers above -/

/-- A well-formed IPv6 packet determines its header. -/
theorem Ipv6Packet.Spec.header_eq {l : List U8} {p p' : Ipv6Packet} (h : Ipv6Packet.Spec l p)
    (h' : Ipv6Packet.Spec l p') : p.header = p'.header :=
  ((FmtLaws Ipv6Header.Insts.UntrustedReaderDecode).functional _ _ _ _ _ h.2.2.1 h'.2.2.1).1

/-- The bytes `[40, end)` of a packet, as `Ipv6Packet::validate`'s callers
    slice them. -/
theorem slice_eq_payloadOf (l : List U8) : l.slice 40 (payloadEnd l) = payloadOf l := by
  simp [payloadOf, List.slice, List.drop_take]

/-- The IPv6 pseudo-header of an upper-layer message carried by the packet
    `l` (RFC 8200, section 8.1): the source and destination addresses, the
    message length as 32 bits (`len` holds its low 16), three zero bytes, and
    the next header `next`. -/
def pseudo (l len : List U8) (next : U8) : List U8 :=
  (l.drop 8).take 32 ++ [0#u8, 0#u8] ++ len ++ [0#u8, 0#u8, 0#u8, next]

/-- The checksum over the pseudo-header and a message `d`, as the validators
    compute it: piece by piece. -/
theorem sum_pseudo (l len d : List U8) (next : U8) (hl : 40 ≤ l.length) (hlen : len.length = 2) :
    inet.spec 0 (pseudo l len next ++ d) =
      inet.spec (inet.spec (inet.spec (inet.spec (inet.spec 0 ((l.drop 8).take 32)) [0#u8, 0#u8])
        len) [0#u8, 0#u8, 0#u8, next]) d := by
  have h1 : ((l.drop 8).take 32).length = 32 := by simp; omega
  simp only [pseudo]
  rw [inet.spec_append _ _ _ (by simp [h1, hlen]), inet.spec_append _ _ _ (by simp [h1, hlen]),
    inet.spec_append _ _ _ (by simp [h1]), inet.spec_append _ _ _ (by simp [h1])]

end net.ipv6
