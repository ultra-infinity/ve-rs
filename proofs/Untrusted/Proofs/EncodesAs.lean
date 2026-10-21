/- `RoundTrip`: what an `Encode` impl writes, the matching `Decode` impl reads
   back; the combinators that build it for derived (sequential) formats; and
   the `Encode` impls of byte arrays and byte slices. -/
import Untrusted.Proofs.Writer

open Aeneas Aeneas.Std Result

namespace untrusted.writer

open reader

/-! ## Round trips -/

/-- `E` writes, for every `v` with `Valid v`, bytes that `D` decodes back to
    `v` consuming exactly them, whatever follows. -/
def RoundTrips {T : Type} (E : T → List U8) (D : List U8 → T → Nat → Prop) (Valid : T → Prop) :
    Prop :=
  ∀ v rest, Valid v → D (E v ++ rest) v (E v).length

/-- `dec` reads back what `enc` writes, for the values `Valid` accepts.

`Valid` is the set of values the decoder accepts: encoding is total (it only
fails when there is no room), so a value the decoder rejects, such as an IPv4
header length below 5, is still written, and is not covered. -/
class RoundTrip {T : Type} (enc : Encode T) (dec : Decode T) {E : T → List U8}
    {D : List U8 → T → Nat → Prop} {F : List U8 → Prop} [EncodesAs enc E] [DecodesAs dec D F]
    (Valid : outParam (T → Prop)) : Prop where
  roundtrip : RoundTrips E D Valid

/-- The values `enc` and `dec` round-trip, found through their `RoundTrip`
    instance. -/
abbrev FmtV {T : Type} (enc : Encode T) (dec : Decode T) {E : T → List U8}
    {D : List U8 → T → Nat → Prop} {F : List U8 → Prop} [EncodesAs enc E] [DecodesAs dec D F]
    {Valid : T → Prop} [RoundTrip enc dec Valid] : T → Prop := Valid

/-- The round trip of `enc` and `dec`, found through their `RoundTrip`
    instance. -/
theorem FmtRT {T : Type} (enc : Encode T) (dec : Decode T) {E : T → List U8}
    {D : List U8 → T → Nat → Prop} {F : List U8 → Prop} [EncodesAs enc E] [DecodesAs dec D F]
    {Valid : T → Prop} [h : RoundTrip enc dec Valid] : RoundTrips E D Valid :=
  h.roundtrip

/-! ## Sequential formats

A derived encoder writes its fields one after another: for
`struct S { a: A, b: B }`, `Eseq EA (Eseq EB Enil)` on `(s.a, s.b, ())`, the
counterpart of `Dseq DA (Dseq DB Dnil)`. -/

/-- Nothing. -/
def Enil : Unit → List U8 := fun _ => []

/-- `A`'s bytes, then `B`'s. -/
def Eseq {A B : Type} (EA : A → List U8) (EB : B → List U8) : A × B → List U8 :=
  fun v => EA v.1 ++ EB v.2

/-- Every value. -/
def Vnil : Unit → Prop := fun _ => True

/-- Both parts valid. -/
def Vseq {A B : Type} (VA : A → Prop) (VB : B → Prop) : A × B → Prop :=
  fun v => VA v.1 ∧ VB v.2

theorem RoundTrips.nil : RoundTrips Enil Dnil Vnil := fun _ _ _ => rfl

theorem RoundTrips.seq {A B : Type} {EA : A → List U8} {DA : List U8 → A → Nat → Prop} {VA}
    {EB : B → List U8} {DB : List U8 → B → Nat → Prop} {VB} (hA : RoundTrips EA DA VA)
    (hB : RoundTrips EB DB VB) : RoundTrips (Eseq EA EB) (Dseq DA DB) (Vseq VA VB) := by
  rintro ⟨a, b⟩ rest ⟨va, vb⟩
  refine ⟨(EA a).length, (EB b).length, ?_, ?_, by simp [Eseq]⟩
  · simpa [Eseq, List.append_assoc] using hA a (EB b ++ rest) va
  · simpa [Eseq, List.append_assoc, List.drop_left'] using hB b rest vb

/-- Transport a round trip along a view of the value, e.g. struct ↦ tuple. -/
theorem RoundTrips.map {S T : Type} {E : T → List U8} {D : List U8 → T → Nat → Prop} {V}
    (h : RoundTrips E D V) (f : S → T) :
    RoundTrips (fun s => E (f s)) (fun l s k => D l (f s) k) (fun s => V (f s)) :=
  fun s rest hv => h (f s) rest hv

/-! ## Reading back what was written -/

/-- **What `encode_into` writes, `read_all` reads back**: if `v` round-trips,
    reading the encoded bytes with `dec` gives `v` again. -/
theorem read_all_encoded {T : Type} (enc : Encode T) (dec : Decode T) {E : T → List U8}
    {D : List U8 → T → Nat → Prop} {F : List U8 → Prop} [EncodesAs enc E] [hd : DecodesAs dec D F]
    {Valid : T → Prop} [h : RoundTrip enc dec Valid] (v : T) (hv : Valid v)
    (s : Untrusted (Slice U8)) (hs : (s : Slice U8).val = E v) :
    UntrustedShared0SliceU8.read_all dec s ⦃ (res : core.result.Result T ValidationError) =>
      res = .Ok v ⦄ := by
  have hD : D (s : Slice U8).val v (s : Slice U8).val.length := by
    simpa [hs] using h.roundtrip v [] hv
  apply WP.spec_mono (UntrustedShared0SliceU8.read_all.spec_of dec s)
  rintro (v' | e) hpost
  · rw [(hd.functional _ _ _ _ _ hpost hD).1]
  · exact absurd hD (hpost v)

/-! ## Byte arrays and byte slices -/

/-- **Spec theorem for `<[u8; N] as Encode>::encode`**: the `N` bytes. -/
instance _root_.untrusted.ArrayU8N.Insts.UntrustedWriterEncode.encode.spec (N : Usize) :
    EncodesAs (ArrayU8N.Insts.UntrustedWriterEncode N) (fun a => (a : Array U8 N).val) where
  spec v w hinv := by
    simp only [ArrayU8N.Insts.UntrustedWriterEncode, ArrayU8N.Insts.UntrustedWriterEncode.encode,
      lift, bind_ok]
    apply WP.spec_bind (Writer.write_bytes.spec w (Array.to_slice v) hinv)
    rintro ⟨r, w1, b⟩ hw
    simp only [WP.uncurry'_pair, uncurry, WP.spec_ok] at hw ⊢
    simpa using hw.wrap

/-- `[u8; N]` round-trips every array. -/
instance _root_.untrusted.ArrayU8N.roundtrip (N : Usize) :
    RoundTrip (ArrayU8N.Insts.UntrustedWriterEncode N) (ArrayU8N.Insts.UntrustedReaderDecode N)
      (fun _ => True) where
  roundtrip a rest _ := by simp

/-- **Spec theorem for `<&[u8] as Encode>::encode`**: the bytes. -/
instance _root_.untrusted.Shared0SliceU8.Insts.UntrustedWriterEncode.encode.spec :
    EncodesAs Shared0SliceU8.Insts.UntrustedWriterEncode (fun s => (s : Slice U8).val) where
  spec v w hinv := by
    simp only [Shared0SliceU8.Insts.UntrustedWriterEncode,
      Shared0SliceU8.Insts.UntrustedWriterEncode.encode]
    apply WP.spec_bind (Writer.write_bytes.spec w v hinv)
    rintro ⟨r, w1, b⟩ hw
    simp only [WP.uncurry'_pair, uncurry, WP.spec_ok] at hw ⊢
    exact hw.wrap

end untrusted.writer
