-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Result

@[expose] public section

/-! # The output values are the attention

An online softmax of an output row (`SoftmaxRun`) over the `sk / 128` key blocks, visited last
first, ends with the base-2 softmax average of `V` over all `sk` keys (`Numeric.softmax_final`):
the ratio of its final accumulator and row sum is `attn` (`run_attn`), whatever reference
exponents the run used. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

namespace Result

variable {P : Params}

/-- **The ratio of a run's final accumulator and row sum is the attention output.** -/
theorem run_attn (hsk : 0 < P.sk) (hdiv : P.sk % 128 = 0) {batch head row : Nat}
    {c l : Nat → ℝ} {O : Nat → Nat → ℝ} (hr : SoftmaxRun P batch head row c l O) {d : Nat}
    (hd : d < 128) :
    O (kvBlocks P - 1) d / l (kvBlocks P - 1) = attn P batch head row d := by
  have hn : 0 < kvBlocks P := by
    unfold kvBlocks
    omega
  have hkeys : 128 * kvBlocks P = P.sk := by
    unfold kvBlocks
    omega
  have h := Numeric.softmax_final (n := kvBlocks P) (b := 128) (s := score P batch head row)
    (v := fun k => P.v batch head k d) (sc := P.scale) (c := c) (O := fun τ => O τ d) (l := l) hn
    (by simpa [visitKey] using hr.acc0 d hd) (fun τ hτ => hr.accStep τ hτ d hd)
    (by simpa [visitKey] using hr.sum0) hr.sumStep
  rw [hkeys] at h
  exact h

end Result

end

end PTX.Kernels.FlashAttn4Fwd.Proof
