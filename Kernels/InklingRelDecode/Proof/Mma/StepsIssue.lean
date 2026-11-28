-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Flow.Step.AdvancesTc
import Lemmas.Flow.SegPieces
import Lemmas.Flow.Footprint

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow
variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {regs : Nat → Value} {w : Value}

local macro "mma_issue" : tactic => `(tactic| (
  site_step trans [next, issueNext, Fin.val_zero, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceDIte]
    seg_by (intro t ht; seg_fp ht using
      try simp only [valueOf, values, lookupLit, Option.getD_some, Option.getD_none]
      all_goals seg_close [kLo, vLo, qLo, desc, vdesc, descHi])
    inv_by (intro hi; exact hi) guard_by (rfl)))

theorem qk_issue_step (hp : Pre Q L mem0) (j : Fin 8) (i : Nat) (v : Value) :
    (code L g regs w).StepAt ⟨.qk j,i,v⟩ := by
  have hsb := hp.sharedRange
  unfold sharedBytes at hsb
  fin_cases j <;> mma_issue

theorem pv_issue_step (hp : Pre Q L mem0) (j : Fin 8) (i : Nat) (v : Value) :
    (code L g regs w).StepAt ⟨.pv j,i,v⟩ := by
  have hsb := hp.sharedRange
  unfold sharedBytes at hsb
  fin_cases j <;> mma_issue

theorem pv_notify_step (hp : Pre Q L mem0) (i : Nat) (v : Value) :
    (code L g regs w).StepAt ⟨.pvCommit1,i,v⟩ := by
  have hsb := hp.sharedRange
  unfold sharedBytes at hsb
  mma_issue

theorem final_elect_step (hp : Pre Q L mem0) (i : Nat) (v : Value) :
    (code L g regs w).StepAt ⟨.finElect,i,v⟩ := by
  have hsb := hp.sharedRange
  unfold sharedBytes at hsb
  mma_issue

end PTX.Kernels.InklingRelDecode.Proof.Mma
