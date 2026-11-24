-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Proof.Correction.ScaleBase
import Kernels.TmlFa4Fwd.Proof.Correction.Loads
import Lemmas.Flow.Step.TcSteps
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

/-! # The implicit waits of the last four rescale loads of stage 1, at the pattern of one

The wait's segment packs the stage's factor and multiplies the chunk by it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_rldwBOneHi (hp : Pre p L m) {v : V} (hv : v.s1 = .one) (s : Site)
    (hs : ∃ c : Fin 8, 4 ≤ c.val ∧ s = .rldw 1 c) : (code p L g).StepAt ⟨s, v, 1⟩ := by
  have hparams := params hp
  rcases v with ⟨sc, ukw, trip, s0, s1, b0, b1, xs, rs0, rm0, rs1, rm1, ys⟩
  simp only at hv
  subst hv
  corr_sites s except [.rldw _ _ => (by corr_rldw)]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
