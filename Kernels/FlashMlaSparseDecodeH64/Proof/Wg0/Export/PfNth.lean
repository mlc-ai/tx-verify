-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Closed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow

@[expose] public section

/-! # The peer reads of a block are the trace's events, in order

`w0Pf` of the block in progress at a prefix `N` lists the reads at the peer pc `477 + 5 k0` of
the block; entry `i` is the trace's event at an index `j < N` of the same block whose own prefix
has exactly `i` such reads before it (`w0Pf_nth`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

/-- **Entry `i` of the block's peer reads is an event of the trace** with `i` such reads of its
block before it. -/
theorem w0Pf_nth (X : Execution) (g k0 : Nat) : ∀ N i x,
    (Wg0.Data.w0Pf (w0Scan ((X.tr g).take N)).2 k0)[i]? = some x →
    ∃ j, j < N ∧ X.get (g, j) = some x ∧
      w0Closed ((X.tr g).take j) = w0Closed ((X.tr g).take N) ∧
      (Wg0.Data.w0Pf (w0Scan ((X.tr g).take j)).2 k0).length = i := by
  intro N
  induction N with
  | zero => intro i x hi; simp [w0Scan, Wg0.Data.w0Pf] at hi
  | succ N ih =>
    intro i x hi
    by_cases hN : N < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[N]? = some e := ⟨_, List.getElem?_eq_getElem hN⟩
      have hsp : (X.tr g).take (N + 1) = (X.tr g).take N ++ [e] := by
        rw [List.take_add_one, he]; rfl
      have hcs : w0Closed ((X.tr g).take (N + 1)) =
          w0Closed ((X.tr g).take N) + if e.pc = w0ArrSPc then 1 else 0 := by
        rw [hsp]; unfold w0Closed; rw [List.countP_append]; simp
      by_cases h1 : e.pc = w0ArrSPc
      · simp only [hsp, w0Scan_snoc, h1, ↓reduceIte, Wg0.Data.w0Pf, List.filter_nil] at hi
        simp at hi
      · simp only [h1, ↓reduceIte, add_zero] at hcs
        have hcs2 : w0Closed ((X.tr g).take N ++ [e]) = w0Closed ((X.tr g).take N) := by
          rw [← hsp]; exact hcs
        simp only [hsp, w0Scan_snoc, h1, ite_false] at hi ⊢
        rw [Wg0.Data.w0Pf_snoc] at hi
        by_cases hc : e.pc = 477 + 5 * k0 ∧ (w0RdVal e).isSome = true
        · simp only [hc, and_self, ↓reduceIte] at hi
          by_cases hlt : i < (Wg0.Data.w0Pf (w0Scan ((X.tr g).take N)).2 k0).length
          · rw [List.getElem?_append_left hlt] at hi
            obtain ⟨j, hj, hget, hcl, hlen⟩ := ih i x hi
            exact ⟨j, by omega, hget, by omega, hlen⟩
          · rw [List.getElem?_append_right (by omega)] at hi
            have hi0 : i - (Wg0.Data.w0Pf (w0Scan ((X.tr g).take N)).2 k0).length = 0 := by
              by_contra hne
              have : ([e] : List Event)[i - (Wg0.Data.w0Pf (w0Scan ((X.tr g).take N)).2 k0).length]?
                  = none := by
                rw [List.getElem?_eq_none_iff]; simp; omega
              rw [this] at hi; cases hi
            rw [hi0] at hi
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            have hlen : i = (Wg0.Data.w0Pf (w0Scan ((X.tr g).take N)).2 k0).length := by omega
            refine ⟨N, by omega, ?_, by omega, hlen.symm⟩
            exact he
        · simp only [hc, ↓reduceIte, List.append_nil] at hi
          obtain ⟨j, hj, hget, hcl, hlen⟩ := ih i x hi
          exact ⟨j, by omega, hget, by omega, hlen⟩
    · have hsp : (X.tr g).take (N + 1) = (X.tr g).take N := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [hsp] at hi ⊢
      obtain ⟨j, hj, hget, hcl, hlen⟩ := ih i x hi
      exact ⟨j, by omega, hget, hcl, hlen⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
