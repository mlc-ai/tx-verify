-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBB
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop
import Lemmas.Flow.Step.TcSteps
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # A bias round's arrival at the correction warps' named barrier

The arrival (`narr .bias`, pc 5683) and the exponent stretch to the first P store: the scaled
products (`Gen.expoB0_run`, framed), then per the branch at pc 5815 the hardware or the software
path and the tail (`narrB_pathA`, `narrB_pathB`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A bias round's arrival at the correction warps' named barrier.** -/
theorem stepAt_narrB (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.narr .bias, v, 0, []⟩ := by
  refine Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
  refine Code.step_issue (dn := D.mk' (.pst .bias 0) v) (by code_lookup)
    (fun hf => fires_barArrive_next hf) (fun _ => rfl) rfl rfl
    ⟨fun _ => ?_, rfl, rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩⟩
  refine Seg.comp_ex ⟨_, (seg_of_segD (Gen.expoB0_run L g (valueOfD p L g (narrB v)))
    (expoB0_ok (g := g) hp v).1).choose_spec.weaken_start fun R hR => by
      rw [expoB0_facts0_eq]; exact holds_sub hR (by kernel_rfl)⟩ ?_
  cases hc : Epilogue.scmp .lt .u v.bt (r301 p L g v)
  · exact narrB_pathA hp v hc
  · exact narrB_pathB hp v hc

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
