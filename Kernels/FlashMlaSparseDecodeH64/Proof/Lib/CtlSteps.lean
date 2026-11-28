-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RulesFrame
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Havoc
public import Lemmas.Flow.AdvanceU
public import Lemmas.Flow.SegCtl

@[expose] public section

/-! # The kernel's facts for control-machine steps

No assumption of the kernel reads a branch (`bra_rule`) or selects the implicit wait of a Tensor
Memory load (`noLdWait`). Tactics: `ctl_seg` proves a control segment with the kernel's rule
frame and hook table; `ctl_adv c by ev` steps a scalar event at code lemma `c` that continues at
the next instruction (`ev` proves the firing from `hf`), leaving the segment after it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g : Nat}

/-- No assumption reads a branch. -/
theorem bra_rule {target : Nat} {uni : Bool} (t : TState) (a : Assumption)
    (ha : a ∈ Assumptions.all) : a.localRule L g t (.bra target uni) = none := by
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (simp only [Assumptions.sharedBits, Assumptions.deadPackRule,
        Assumptions.peerPackRule_bra]; split <;> rfl)
    | (simp only [Assumptions.paramPointers]; split <;> simp only [ite_self])

/-- No assumption of the kernel selects the implicit wait of a Tensor Memory load. -/
theorem noLdWait (pc : Nat) : Assumptions.all.any (·.tcLdWait pc) = false := rfl

/-- A control segment of the kernel (`seg_ctl` with the kernel's rule frame and hooks). -/
macro "ctl_seg" : tactic => `(tactic| seg_ctl rulesFrame, KernelHavoc.hooks_ok)

set_option hygiene false in
/-- An event that continues at the next instruction (`ev` proves it from `hf`). -/
macro "ctl_adv " code:term:max " by " ev:tacticSeq : tactic => `(tactic| (
  refine Code.advanceU $code rfl (fun hf => by $ev) (fun _ => rfl) rfl rfl rfl rfl
    (Nat.zero_lt_succ _) ?_))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
