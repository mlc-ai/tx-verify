-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX PTX.Proof PTX.Flow
noncomputable section
macro "ctl_val" : tactic => `(tactic| (
  simp only [Control.valueOf, Control.values, finalControlRegs, Control.D.scheduler,
      Control.V.scheduler, valuesStart, valuesRole, valuesTile, valuesRound, valuesRescale,
    valuesFinal, Mma.sbi, Mma.sbW, Mma.w32, lookupLit, Option.getD_some, Option.getD_none]
  try simp (disch := decide) only [sb_addi' ‹Pre _ _ _›]
  try rfl))

set_option hygiene false in
/-- The role's side conditions of `site_shape`: the CTA size, the mbarrier addresses, the Tensor
Memory address registers and the assumptions that select no Tensor Memory site. -/
macro "ctl_addr" : tactic => `(tactic| first
  | (rw [‹Pre _ _ _›.block]; done)
  | (rw [‹Pre _ _ _›.block]; decide)
  | (rw [hat.1]; ld_wait)
  | (rw [hat.1, PTX.Kernels.TmlFa4Fwd.Assumptions.all_tcStWaitLd]; kernel_rfl)
  | exact hat.2.1
  | (refine (PTX.Flow.regs_of_factsFrom hF (by decide +kernel)).trans ?_; ctl_val)
  | with_reducible exact truncBits_lt _
  | with_reducible exact ori_lt _ _
  | with_reducible exact nb0_lt
  | with_reducible exact nb1_lt
  | (try simp only [bl, arrOff, pollOff]
     refine' Epilogue.loc_off ‹Pre _ _ _› (by decide) ?hk ?h8 ?hr
     case hr => exact (PTX.Flow.regs_of_factsFrom hF (by decide +kernel)).trans (by ctl_val)
     case hk => omega
     case h8 => have := ‹Pre _ _ _›.shared; omega)
  | (try simp only [bl, arrOff, pollOff]
     refine Epilogue.loc_off (k := 0) ‹Pre _ _ _› (by decide) ?hk ?h8 ?hr
     case hr => exact (PTX.Flow.regs_of_factsFrom hF (by decide +kernel)).trans (by ctl_val)
     case hk => omega
     case h8 => have := ‹Pre _ _ _›.shared; omega))

syntax "ctl_step" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ctl_step) => `(tactic|
  site_shape_step
    unfolding [Control.Ev, Correction.Ev, nb0_trunc, nb1_trunc, arrOff, pollOff, pollPar, nbW,
        barK, Site.toE, bl, rdOrUb,
      votePredR, Epilogue.Ev, Epilogue.partialAt]
    reg_vals [Control.valueOf, Control.values, finalControlRegs, Control.D.scheduler,
        Control.V.scheduler, valuesStart, valuesRole, valuesScan, valuesSelect, valuesSelect2,
      valuesTile, valuesRound, valuesRescale, valuesFinal, fAddrs, valuesLse, Epilogue.partials,
      loopRegsR, Epilogue.lanePreds, lookupLit]
    addr_by (ctl_addr))


end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
