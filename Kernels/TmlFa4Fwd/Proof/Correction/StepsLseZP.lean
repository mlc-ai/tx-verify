-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Proof.Correction.LseBase
import Lemmas.Flow.Step.SiteIte
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

/-! # The LSE stores: the last final arrival, zero first and positive second row sum

The successors of the final stage's last arrival (`fdone 1 1`) when the first row sum is zero and
the second positive: the LSE registers' logarithms and `selp`s read the signs (`StepsLse.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_fdZP (hp : Pre p L m) {s : Site} (hs : s = .fdone 1 1) (v : V)
    (h0 : 0 = v.rs0) (h1 : 0 < v.rs1) : (code p L g).StepAt ⟨s, v, 0⟩ := by
  have hparams := params hp
  have hsc := scale_read hp
  have hr0 := readEReal_erealValue_f32 v.rm0.1
  have hr1 := readEReal_erealValue_f32 v.rm1.1
  have hs0 := scale_mul hp v.rm0.1
  have hs1 := scale_mul hp v.rm1.1
  have ht0 := add_log_bot hp v.rm0
  have ht1 := add_log_bot hp v.rm1
  have ha := add_log
  have hm := mul_ln2
  have h1' : v.rs1 ≠ 0 := ne_of_gt h1
  corr_sites s using [h1, h1.le, ← h0, le_refl, and_self, ite_true]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
