-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

/-! # The row-maximum reads

The load of a final stage's row maximum: the machine follows the pattern of an extended real below
`+∞` (`max32`) and stops on any other value. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
local macro "max_load " st:term " via " lookup:term : tactic => `(tactic| (
  refine Code.StepAt.of (by site_event (trivial)) ?_
  refine Code.step_load_sel (C := code p L g) (d := ⟨.fmax $st, v, 0⟩)
    (r := if $st = 0 then 6513 else 1654)
    (nv := fun w => max32 w fun x => D.mk' (.farr $st) (setRm v x $st))
    $lookup rfl rfl rfl rfl ?_ ?_ rfl rfl (fun w => max32_ne_none _ _) ?_
  · intro x bs w hw
    simp only [code, succ, hw]
  · intro x bs f hw
    refine .inl ?_
    simp only [code, succ, hw]
  · intro w d' hd
    obtain ⟨x, rfl, rfl⟩ := max32_some hd
    lands_auto (corr_seg) (corr_inv)))

theorem stepAt_fmax (hp : Pre p L m) (st : Fin 2) (v : V) :
    (code p L g).StepAt ⟨.fmax st, v, 0⟩ := by
  have hparams := params hp
  fin_cases st <;> dsimp only [Fin.zero_eta, Fin.mk_one]
  · max_load (0 : Fin 2) via Flow.code_8467
  · max_load (1 : Fin 2) via Flow.code_8763

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
