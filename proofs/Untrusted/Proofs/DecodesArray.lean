/- Spec of `<[u8; N] as Decode>::decode`: exactly `N` bytes, copied. -/
import Untrusted.Proofs.DecodesAs

open Aeneas Aeneas.Std Result

namespace untrusted

open reader

theorem take_set_succ (l : List U8) (i : Nat) (x : U8) (h : i < l.length) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, List.getElem?_set_self (by omega)]
  simp [List.take_set_of_le]

/-- **Spec theorem for the loop of `<[u8; N] as Decode>::decode`**: with at
    least `N - i` bytes left, copies the next `N - i` of them into
    `out[i..N]`. -/
@[step]
theorem ArrayU8N.Insts.UntrustedReaderDecode.decode_loop.spec {N : Usize} (r : Reader)
    (out : Array U8 N) (i : Usize) (hinv : Reader.Inv r) (hi : i.val ≤ N.val)
    (hrem : N.val - i.val ≤ (Reader.rest r).length) :
    ArrayU8N.Insts.UntrustedReaderDecode.decode_loop r out i
      ⦃ (res : core.result.Result (Array U8 N) ValidationError) (r' : Reader) =>
        r'.input = r.input ∧ Reader.Inv r' ∧ r'.pos.val = r.pos.val + (N.val - i.val) ∧
        ∃ a : Array U8 N, res = .Ok a ∧
          a.val = out.val.take i.val ++ (Reader.rest r).take (N.val - i.val) ⦄ := by
  unfold ArrayU8N.Insts.UntrustedReaderDecode.decode_loop
  split
  · apply WP.spec_bind (Reader.read_byte.spec_cons r)
    rintro ⟨res1, r1⟩ h1
    simp only [WP.uncurry'_pair, uncurry] at h1 ⊢
    cases res1
    · rename_i b
      obtain ⟨hrest, hin1, hpos1, hinv1⟩ := h1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have hrem1 : N.val - (i.val + 1) ≤ (Reader.rest r1).length := by
        rw [hrest] at hrem; simp at hrem; omega
      step*
      refine ⟨by rw [res_post, hin1], res_post1, by scalar_tac, a, res_post3, ?_⟩
      have hlt : i.val < out.val.length := by simp; scalar_tac
      have hn : N.val - i.val = (N.val - i1.val) + 1 := by scalar_tac
      rw [res_post4, a_post, Array.set_val_eq, i1_post, take_set_succ _ _ _ hlt, hrest, hn,
        List.take_succ_cons, ← i1_post, List.append_assoc]
      rfl
    · exfalso
      obtain ⟨hnil, -, -⟩ := h1
      rw [hnil] at hrem
      simp at hrem
      scalar_tac
  · simp only [WP.spec_ok, WP.uncurry'_pair]
    have hiN : i.val = N.val := by scalar_tac
    refine ⟨by simp, hinv, by simp [hiN], out, rfl, ?_⟩
    simp [hiN]
termination_by N.val - i.val
decreasing_by all_goals scalar_tac

/-- **Spec theorem for `<[u8; N] as Decode>::decode`**: the next `N` bytes, as
    is. -/
instance ArrayU8N.Insts.UntrustedReaderDecode.decode.spec (N : Usize) :
    DecodesAs (ArrayU8N.Insts.UntrustedReaderDecode N)
      (fun l a k => k = N.val ∧ N.val ≤ l.length ∧ (a : Array U8 N).val = l.take N.val)
      (fun l => l.length < N.val) where
  spec r hinv := by
    simp only [ArrayU8N.Insts.UntrustedReaderDecode.decode]
    step*
    refine ⟨res_post, res_post1, ?_⟩
    rw [res_post3]
    simp only [List.take_zero, List.nil_append, Nat.sub_zero] at res_post4 res_post2
    exact ⟨by scalar_tac, res_post4, res_post2⟩
  disjoint _ _ _ hD hF := by have := hD.2.1; omega
  functional _ a _ a' _ hD hD' :=
    ⟨Aeneas.Std.Array.ext a a' (hD.2.2.trans hD'.2.2.symm), hD.1.trans hD'.1.symm⟩

end untrusted
