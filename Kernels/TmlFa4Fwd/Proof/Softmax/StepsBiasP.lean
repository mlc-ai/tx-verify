-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsP1
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasPCtl
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl

@[expose] public section

/-! # A bias round's P part: the control sites, lifted

The control sites of a bias round's P part (the last two stores, the store waits, the warp
barrier, the election and the elected lane's arrival) are stepped on the control machine
(`stepAt_bias_pctl`) and lifted to the data machine (`stepAt_lift`), as the first round's: their
event and the local code up to the next event write no data register the state names, and every
successor has the state's data table (`pBData`), so the exponent stretch's terms are never
walked. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- A control site of a bias round's P part, lifted (`pc` the site's, `hi` the next event's). -/
macro "lift_pb " pc:num hi:num : tactic => `(tactic| (
  refine stepAt_lift (stepAt_bias_pctl hp hg _ rfl rfl (by simp)) $pc $hi (by kernel_rfl)
    (by kernel_rfl) (by simp [Site.pc, Rd.pc])
    (by simp [Site.pc, Rd.pc]) (hev_of (by code_lookup) rfl (by kernel_rfl)) ?_
  lift_land))

theorem stepAt_pstB_2 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pst .bias 2, v, 0, []⟩ := by lift_pb 6526 6527
theorem stepAt_pwstB_0 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pwst .bias 0, v, 0, []⟩ := by lift_pb 6527 6532
theorem stepAt_pstB_3 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pst .bias 3, v, 0, []⟩ := by lift_pb 6541 6542
theorem stepAt_pwstB_1 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pwst .bias 1, v, 0, []⟩ := by lift_pb 6542 6543
theorem stepAt_pwsB (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pws .bias, v, 0, []⟩ := by lift_pb 6543 6544
theorem stepAt_pelB (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pel .bias, v, 0, []⟩ := by lift_pb 6544 6558
theorem stepAt_parr2B (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.parr2 .bias, v, 0, []⟩ := by lift_pb 6552 6558

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
