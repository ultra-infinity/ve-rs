/- Hand-written specs for the `net` crate that build on derived types. Kept by
   `cargo untrusted verify`; imported by its audit. -/
import Net.Manual
import Net.Specs.EthernetHeader

open Aeneas Aeneas.Std Result untrusted untrusted.reader

namespace net.ethernet

/-- `l` is a well-formed Ethernet II frame that decodes to `f`: it is 60 to
    1514 bytes long, its first 14 bytes decode as `f.header` (two MAC addresses
    and an EtherType of at least `0x0600`), and `f.payload` is exactly the rest. -/
def Frame.Spec (l : List U8) (f : Frame) : Prop :=
  60 ≤ l.length ∧ l.length ≤ 1514 ∧
    FmtD EthernetHeader.Insts.UntrustedReaderDecode (l.take 14) f.header 14 ∧
    (f.payload : Slice U8).val = l.drop 14

/-- **Spec theorem for `<Frame as Validate<&[u8]>>::validate`**: accepts exactly
    the well-formed Ethernet II frames, and returns their decoding. -/
theorem _root_.net.ethernet.Frame.Insts.UntrustedValidateSharedASliceU8ValidationError.validate.spec
    (input : Slice U8) :
    Frame.Insts.UntrustedValidateSharedASliceU8ValidationError.validate input
      ⦃ (r : core.result.Result Frame ValidationError) =>
        match r with
        | .Ok f => Frame.Spec input.val f
        | .Err _ => ∀ f, ¬ Frame.Spec input.val f ⦄ := by
  unfold Frame.Insts.UntrustedValidateSharedASliceU8ValidationError.validate
  step*
  · rintro f ⟨h60, -⟩
    scalar_tac
  · rintro f ⟨h60, -⟩
    scalar_tac
  · rintro f ⟨-, h1514, -⟩
    scalar_tac
  · /- The header is the first 14 bytes, decoded with `read_all`. -/
    have hu : (u : Slice U8).val = input.val.take 14 := by
      rw [u_post, s_post]; simp [List.slice]
    have hlen : (input.val.take 14).length = 14 := by
      rw [← hu, u_post]; simpa using s_post1
    apply WP.spec_bind
      (UntrustedShared0SliceU8.read_all.spec_of EthernetHeader.Insts.UntrustedReaderDecode u)
    rintro (h | e) hres
    · simp only [hu, hlen] at hres
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step*
      refine ⟨by scalar_tac, by scalar_tac, hres, ?_⟩
      rw [u1_post, s1_post]
      simp
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      simp only [hu, hlen] at hres
      rintro f ⟨-, -, hD, -⟩
      exact hres f.header hD

end net.ethernet
