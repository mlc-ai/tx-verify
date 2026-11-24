-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.WaitOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0GemmTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GemmTrace

public section

/-! # Producer priority at a pending GEMM input wait -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

set_option linter.unusedSimpArgs false in
/-- A dequantizer that still owes the requested tile has priority over the MMA wait. -/
theorem dequant_before_mma_wait {P : Params} {L : Launch} {g h : Nat}
    {d : Wg1Mma.D} {q : Wg2.D} (hd : d.site = .kvWait) (hq : q.site ≠ .barrier)
    (hBlocks : Wg2GemmTrace.publishedBlocks q ≤ d.i) :
    priority P L h (.wg2 q) < priority P L g (.mma d) := by
  have hWait : priority P L g (.mma d) = blockTime d.i 434 := by
    simp [priority, matmulTime, mmaOrdinal, hd]
  rw [hWait]
  cases hSite : q.site
  all_goals simp only [hSite, reduceCtorEq, not_false_eq_true] at hq
  all_goals try exact (hq rfl).elim
  all_goals
    simp only [priority, quantTime, hSite, Wg2GemmTrace.publishedBlocks, wg2Ordinal,
      blockTime] at hBlocks ⊢
  all_goals first | omega | (split_ifs <;> omega)

set_option linter.unusedSimpArgs false in
/-- A softmax lane that still owes probability publication has priority over the MMA wait. -/
theorem softmax_before_mma_wait {P : Params} {L : Launch} {g h : Nat}
    {d : Wg1Mma.D} {q : Wg0.D} (hd : d.site = .soWait) (hq : q.site.inEpilogue = false)
    (hSub : q.sub < q.site.elems) (hBlocks : Wg0GemmTrace.publishedBlocks q ≤ d.i) :
    priority P L h (.wg0 q) < priority P L g (.mma d) := by
  have hWait : priority P L g (.mma d) = blockTime d.i 1453 := by
    simp [priority, matmulTime, mmaOrdinal, hd]
  rw [hWait]
  cases hSite : q.site
  all_goals simp only [hSite, Wg0.Site.inEpilogue, Bool.true_eq_false] at hq
  all_goals
    simp only [priority, softmaxTime, hSite, Wg0GemmTrace.publishedBlocks,
      Wg0.Site.inEpilogue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Wg0.Site.elems,
      wg0Ordinal, blockTime] at hSub hBlocks ⊢
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
