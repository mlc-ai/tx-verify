-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.LseBase
public import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

/-! # The LSE stores: the last final arrival, positive first and zero second row sum

The successors of the final stage's last arrival (`fdone 1 1`) when the first row sum is positive
and the second zero: the LSE registers' logarithms and `selp`s read the signs (`StepsLse.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_fdPZ (hp : Pre p L m) {s : Site} (hs : s = .fdone 1 1) (v : V)
    (h0 : 0 < v.rs0) (h1 : 0 = v.rs1) : (code p L g).StepAt ⟨s, v, 0⟩ := by
  have hparams := params hp
  have hsc := scale_read hp
  have h0' : v.rs0 ≠ 0 := ne_of_gt h0
  corr_sites s using [h0, h0.le, ← h1, le_refl, and_self, ite_true]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
