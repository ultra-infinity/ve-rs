/- Hand-written spec of `<Ipv4Packet as Validate<&[u8]>>::validate`. -/
import Net.Manual
import Net.Specs.Ipv4Header

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.ipv4

/-- `l` is a well-formed IPv4 packet, possibly followed by link-layer padding,
    that decodes to `p`: its header length `hl` and total length `tl` satisfy
    `20 ≤ hl ≤ tl ≤ l.length`, the first `hl` bytes have a valid checksum, the
    first 20 decode as `p.header`, and `p.options`, `p.payload` and
    `p.padding` are the bytes `[20, hl)`, `[hl, tl)` and `[tl, …)`. -/
def Ipv4Packet.Spec (l : List U8) (p : Ipv4Packet) : Prop :=
  20 ≤ l.length ∧ 20 ≤ headerLen l ∧ headerLen l ≤ totalLen l ∧ totalLen l ≤ l.length ∧
    inet.spec 0 (l.take (headerLen l)) = 0xFFFF ∧
    FmtD Ipv4Header.Insts.UntrustedReaderDecode (l.take 20) p.header 20 ∧
    (p.options : Slice U8).val = (l.take (headerLen l)).drop 20 ∧
    (p.payload : Slice U8).val = (l.take (totalLen l)).drop (headerLen l) ∧
    (p.padding : Slice U8).val = l.drop (totalLen l)

/-- **Spec theorem for `<Ipv4Packet as Validate<&[u8]>>::validate`**: accepts
    exactly the well-formed IPv4 packets, and returns their decoding. -/
@[step]
theorem _root_.net.ipv4.Ipv4Packet.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Ipv4Packet.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Ipv4Packet ValidationError) =>
        match r with
        | .Ok p => Ipv4Packet.Spec input.val p
        | .Err _ => ∀ p, ¬ Ipv4Packet.Spec input.val p ⦄ := by
  unfold Ipv4Packet.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  dsimp only
  split
  · simp only [WP.spec_ok]
    rintro p ⟨h20, -⟩
    scalar_tac
  · step*
    · rintro p ⟨-, h20, -⟩
      scalar_tac
    · rintro p ⟨-, -, hle, -⟩
      scalar_tac
    · rintro p ⟨-, -, -, hle, -⟩
      scalar_tac
    · rename_i hne
      rintro p ⟨-, -, -, -, hck, -⟩
      have hs : s.val = input.val.take (headerLen input.val) := by
        rw [s_post, ← header_len_post]; simp [List.slice]
      have : i2 = inet.VALID := (UScalar.eq_equiv _ _).mpr (by rw [i2_post, hs, hck]; simp)
      simp [this] at hne
    · have hck := ‹¬(i2 != inet.VALID) = true›
      have hs : s.val = input.val.take (headerLen input.val) := by
        rw [s_post, ← header_len_post]; simp [List.slice]
      have hck : inet.spec 0 (input.val.take (headerLen input.val)) = 0xFFFF := by
        rw [← hs, ← i2_post]; simpa using hck
      have hu : (u : Slice U8).val = input.val.take 20 := by
        rw [u_post, s1_post]; simp [List.slice]
      have hlen : (input.val.take 20).length = 20 := by
        simp only [List.length_take]; scalar_tac
      apply WP.spec_bind
        (UntrustedShared0SliceU8.read_all.spec_of Ipv4Header.Insts.UntrustedReaderDecode u)
      rintro (h | e) hres
      · simp only [hu, hlen] at hres
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step*
        refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, hck, hres, ?_, ?_, ?_⟩
        · rw [u1_post, s2_post, ← header_len_post]; simp [List.slice, List.drop_take]
        · rw [u2_post, s3_post, ← header_len_post, ← header_len_post1]
          simp [List.slice, List.drop_take]
        · rw [u3_post, s4_post, ← header_len_post1]
      · simp only [hu, hlen] at hres
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
        rintro p ⟨-, -, -, -, -, hD, -⟩
        exact hres p.header hD

end net.ipv4
