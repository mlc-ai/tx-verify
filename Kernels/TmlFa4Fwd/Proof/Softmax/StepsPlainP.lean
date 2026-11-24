-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsP1
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainCtl
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsP1Control
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # A plain round's P part: the control sites, lifted

The control sites of a plain round's P part (the last two stores, the store waits, the warp
barrier, the election and the elected lane's arrival) are stepped on the control machine
(`stepAt_plain_pctl`) and lifted to the data machine (`stepAt_lift`): their event and the local
code up to the next event write no data register the state names, and every successor has the
state's data table. The 128 weights a P state names are never walked. The landing check reads
the table's keys, which depend on the kind of the maximum before the round, so it runs once per
kind. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- A control site of a plain round's P part, lifted (`pc` the site's, `hi` the next event's). -/
macro "lift_pl " pc:num hi:num : tactic => `(tactic| (
  obtain ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩ := v
  cases mf <;>
  (refine stepAt_lift (stepAt_plain_pctl hp hg _ rfl rfl (by simp)) $pc $hi (by kernel_rfl)
      (by kernel_rfl) (by simp [Site.pc, Rd.pc]) (by simp [Site.pc, Rd.pc])
      (hev_of (by code_lookup) rfl (by kernel_rfl)) ?_
   lift_land)))

theorem stepAt_pstP_2 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pst .plain 2, v, 0, []⟩ := by lift_pl 7434 7435
theorem stepAt_pwstP_0 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pwst .plain 0, v, 0, []⟩ := by lift_pl 7435 7437
theorem stepAt_pstP_3 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pst .plain 3, v, 0, []⟩ := by lift_pl 7446 7447
theorem stepAt_pwstP_1 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pwst .plain 1, v, 0, []⟩ := by lift_pl 7447 7448

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
