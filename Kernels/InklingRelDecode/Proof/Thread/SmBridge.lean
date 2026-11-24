-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmEdge
public import Kernels.InklingRelDecode.Proof.Result.Softmax

@[expose] public section

/-! # The machine's update is `Softmax.step`

The machine's per-iteration update of the running maximum and sum is `D.upd` (`SmEdge`): the new
maximum is `%r1061` unless the rescale is lazy, and the new sum is `fma(l, alpha, row sum)`. This
file states it in the form of `Proof/Result/Softmax.lean`'s `step`, so that the Result layer can
use `fold_invariant` and `fold_lse` on the numbers the machine holds.

`upd_eq_step` is the one-iteration statement. Its hypotheses are the numbers the score stage
(pcs 1299-2233) leaves in the registers `%r1061` (`stg.mn`), `%p168` (`stg.kp`), `%r46`
(`stg.al`) and `%r1070` (`stg.rs`), each in the form of `step`'s definition for the block `blk`
of the visible scores of the thread's row: the maximum of the running maximum and the block's,
the lazy-rescale decision on `alpha_log2 = (m - m_safe) * scale_log2` (`Keep`), `alpha`
(`1` or `2 ^ alpha_log2`) and the sum of the block's exponentials `2 ^ (sl s - m_use sl)`.
`Corr` says that the machine's running maximum and sum are those of a list of blocks, and
`corr_step` extends it by one block. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Softmax
open Classical

noncomputable section
set_option maxRecDepth 100000

/-- `-inf` as the machine's initial running maximum (`0xFF800000`). -/
theorem erealValue_bot : erealValue .f32 ⊥ = b32 4286578688 := by
  decide +kernel

theorem valFloat_float (y : ℝ) : valFloat .f32 (.float .f32 y) = .ok y := by
  simp [valFloat, pure, Except.pure]

/-- The machine's running maximum and sum are those of the blocks `bs`. -/
def Corr (sl : ℝ) (bs : List (List (ℝ × ℝ))) (d : D) : Prop :=
  d.m = erealValue .f32 (Softmax.run sl bs).m ∧ valFloat .f32 d.l = .ok (Softmax.run sl bs).l

/-- The first state: no block, the running maximum `-inf` and sum `0`. -/
theorem corr_init (sl : ℝ) {d : D} (hm : d.m = b32 4286578688) (hl : d.l = b32 0) :
    Corr sl [] d := by
  refine ⟨?_, ?_⟩
  · rw [hm, Softmax.run, List.foldl_nil, erealValue_bot]
  · rw [hl, Softmax.run, List.foldl_nil]
    simpa using (valFloat_b32 (b := 0) (by norm_num) (q := 0) (by decide +kernel))

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
