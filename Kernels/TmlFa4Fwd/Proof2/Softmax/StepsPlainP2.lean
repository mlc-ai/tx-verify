-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsP1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainCtl

@[expose] public section

/-! # A plain round's P part: the warp barrier, the election and the elected lane's arrival,
lifted as in `StepsPlainP.lean` -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- A control site of a plain round's P part, lifted (`pc` the site's, `hi` the next event's). -/
macro "lift_pl2 " pc:num hi:num : tactic => `(tactic| (
  obtain ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩ := v
  cases mf <;>
  (refine stepAt_lift (stepAt_plain_pctl hp hg _ rfl rfl (by simp)) $pc $hi (by kernel_rfl)
      (by kernel_rfl) (by simp [Site.pc, Rd.pc]) (by simp [Site.pc, Rd.pc])
      (hev_of (by code_lookup) rfl (by kernel_rfl)) ?_
   lift_land)))

theorem stepAt_pwsP (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pws .plain, v, 0, []⟩ := by lift_pl2 7448 7449
theorem stepAt_pelP (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pel .plain, v, 0, []⟩ := by lift_pl2 7449 7463
theorem stepAt_parr2P (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.parr2 .plain, v, 0, []⟩ := by lift_pl2 7457 7463

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
