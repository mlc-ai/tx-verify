-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Round
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsKeepB
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
noncomputable section
set_option maxRecDepth 100000

private def maxima (seed : Option EReal) (w : Nat → EReal) (a : Nat) : Nat → EReal
  | 0 =>
    let x := w (2*a)
    let initial := if a = 0 then seed.elim x (fun z => max z x) else x
    max initial (w (2*a+1))
  | n+1 => max (max (maxima seed w a n) (w (8*(n+1)+2*a))) (w (8*(n+1)+2*a+1))

private def tree (seed : Option EReal) (w : Nat → EReal) :=
  let m a := maxima seed w a 15
  max (max (max (m 0) (m 1)) (m 2)) (m 3)

private theorem first_tree (m : BitVec 64) (e : Nat → EReal) :
    foldM m e = tree none (fun i => mre (i/32) m (i%32) (e i)) := by kernel_rfl

private theorem bias_tree (seed : EReal) (e : Nat → EReal) :
    foldB seed e = tree (some seed) e := by kernel_rfl

private theorem masked_stripe (seed : Option EReal) (w : Nat → EReal) (a n : Nat)
    (h : maxima seed w a n = ⊥) (u : Nat) (hu : u ≤ n) :
    w (8*u+2*a) = ⊥ ∧ w (8*u+2*a+1) = ⊥ := by
  induction n with
  | zero =>
    have eu : u = 0 := by omega
    subst u
    simp only [maxima, max_eq_bot] at h
    simp only [Nat.mul_zero, Nat.zero_add]
    refine ⟨?_,h.2⟩
    cases seed <;> by_cases ha : a = 0 <;>
      simp_all [Option.elim]
  | succ n ih =>
    simp only [maxima, max_eq_bot] at h
    rcases Nat.eq_or_lt_of_le hu with rfl | hlt
    · exact ⟨h.1.2,h.2⟩
    · exact ih h.1.1 (by omega)

private theorem masked_tree {seed : Option EReal} {w : Nat → EReal} (h : tree seed w = ⊥)
    {i : Nat} (hi : i < 128) : w i = ⊥ := by
  simp only [tree, max_eq_bot] at h
  have ha : i%8/2 < 4 := by omega
  have hs : maxima seed w (i%8/2) 15 = ⊥ := by
    generalize i%8/2 = a at ha ⊢
    interval_cases a <;> first | exact h.1.1.1 | exact h.1.1.2 | exact h.1.2 | exact h.2
  have t := masked_stripe seed w (i%8/2) 15 hs (i/8) (by omega)
  by_cases he : i%2 = 0
  · exact (show 8*(i/8)+2*(i%8/2) = i by omega) ▸ t.1
  · exact (show 8*(i/8)+2*(i%8/2)+1 = i by omega) ▸ t.2

theorem first_masked (p L g v) (h : maximum p L g v .first = ⊥) {i : Nat} (hi : i < 128) :
    score p L g v .first i = ⊥ := by
  change foldM _ _ = ⊥ at h
  rw [first_tree] at h
  exact masked_tree h hi

theorem bias_masked (p L g v) (h : maximum p L g v .bias = ⊥) :
    v.mf = false ∧ ∀ i < 128, score p L g v .bias i = ⊥ := by
  change maxB p v = ⊥ at h
  cases hm : v.mf
  · simp only [maxB, hm, Bool.false_and, Bool.false_eq_true, ite_false] at h
    obtain h' := (bias_tree (mxE v) (bpeB p v)).symm.trans h
    exact ⟨rfl, fun _ hi => masked_tree h' hi⟩
  · simp only [maxB, hm, Bool.true_and] at h
    split at h
    · exact (EReal.coe_ne_bot _ h).elim
    · rw [foldBE_real (p := p) hm] at h
      exact (EReal.coe_ne_bot _ h).elim

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
