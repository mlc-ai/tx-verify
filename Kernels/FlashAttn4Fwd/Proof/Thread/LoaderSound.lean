-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderStart
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderK0
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderQ0
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderQ1
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderV0
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderK
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderV
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderDrain

@[expose] public section

/-! # The loader's obligations as a code machine

Every loader site is an unguarded event instruction (`site_ok`), and every event fired at a
loader state steps to the state `next` gives (`step`). `code` is the role as a code machine on
its own (from `setmaxnreg`), and `stepAt` its obligation for every state: the machine skeleton
composes the role through `Site.pc`, `facts`, `Inv`, `next` and these two lemmas. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The instruction of each loader site: an unguarded event instruction. -/
theorem site_ok {L : Launch} {g : Nat} (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨s, i, t, ks, ph, qp⟩ := d
  cases s with
  | setMaxReg => exact ⟨_, Flow.code_setMaxReg_1, rfl, trivial⟩
  | head => exact ⟨_, Flow.code_shfl_4, rfl, trivial⟩
  | wait u =>
    cases u
    · exact ⟨_, Flow.code_mbarWait_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_1, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_2, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_3, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_4, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_5, rfl, trivial⟩
  | elA u =>
    cases u
    · exact ⟨_, Flow.code_elect_15, rfl, trivial⟩
    · exact ⟨_, Flow.code_elect_18, rfl, trivial⟩
    · exact ⟨_, Flow.code_elect_21, rfl, trivial⟩
    · exact ⟨_, Flow.code_elect_24, rfl, trivial⟩
    · exact ⟨_, Flow.code_elect_26, rfl, trivial⟩
    · exact ⟨_, Flow.code_elect_29, rfl, trivial⟩
  | arrive u =>
    cases u
    · exact ⟨_, Flow.code_mbarArrive_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_1, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_2, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_3, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_4, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_5, rfl, trivial⟩
  | elC u j =>
    cases u
    · rcases Store.fin2_cases j with rfl | rfl
      · exact ⟨_, Flow.code_elect_16, rfl, trivial⟩
      · exact ⟨_, Flow.code_elect_17, rfl, trivial⟩
    · rcases Store.fin2_cases j with rfl | rfl
      · exact ⟨_, Flow.code_elect_19, rfl, trivial⟩
      · exact ⟨_, Flow.code_elect_20, rfl, trivial⟩
    · rcases Store.fin2_cases j with rfl | rfl
      · exact ⟨_, Flow.code_elect_22, rfl, trivial⟩
      · exact ⟨_, Flow.code_elect_23, rfl, trivial⟩
    · exact ⟨_, Flow.code_elect_25, rfl, trivial⟩
    · rcases Store.fin2_cases j with rfl | rfl
      · exact ⟨_, Flow.code_elect_27, rfl, trivial⟩
      · exact ⟨_, Flow.code_elect_28, rfl, trivial⟩
    · exact ⟨_, Flow.code_elect_30, rfl, trivial⟩
  | copy u j =>
    cases u
    · rcases Store.fin2_cases j with rfl | rfl
      · exact ⟨_, Flow.code_tensorCopy_0, rfl, trivial⟩
      · exact ⟨_, Flow.code_tensorCopy_1, rfl, trivial⟩
    · rcases Store.fin2_cases j with rfl | rfl
      · exact ⟨_, Flow.code_tensorCopy_2, rfl, trivial⟩
      · exact ⟨_, Flow.code_tensorCopy_3, rfl, trivial⟩
    · rcases Store.fin2_cases j with rfl | rfl
      · exact ⟨_, Flow.code_tensorCopy_4, rfl, trivial⟩
      · exact ⟨_, Flow.code_tensorCopy_5, rfl, trivial⟩
    · exact ⟨_, Flow.code_tensorCopy_6, rfl, trivial⟩
    · rcases Store.fin2_cases j with rfl | rfl
      · exact ⟨_, Flow.code_tensorCopy_7, rfl, trivial⟩
      · exact ⟨_, Flow.code_tensorCopy_8, rfl, trivial⟩
    · exact ⟨_, Flow.code_tensorCopy_9, rfl, trivial⟩
  | drain k =>
    fin_cases k
    · exact ⟨_, Flow.code_mbarWait_6, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_7, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_8, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_9, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_10, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_11, rfl, trivial⟩
  | drainQ => exact ⟨_, Flow.code_mbarWait_12, rfl, trivial⟩
  | elTail => exact ⟨_, Flow.code_elect_31, rfl, trivial⟩
  | arriveTail => exact ⟨_, Flow.code_mbarArrive_6, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- Every event fired at a loader state steps to its successor. -/
theorem step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t u : TState} {e : Event}
    {ins : Instr} (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨s, i, t, ks, ph, qp⟩ := d
  cases s with
  | setMaxReg => exact step_start hpre hg rfl h hc hf
  | head => exact step_head hpre rfl hi h hc hf
  | wait u =>
    cases u
    · exact step_wait_k0 hpre hg rfl hi h hc hf
    · exact step_wait_q0 hpre rfl hi h hc hf
    · exact step_wait_q1 hpre rfl hi h hc hf
    · exact step_wait_v0 hpre rfl hi h hc hf
    · exact step_wait_k hpre hg rfl hi h hc hf
    · exact step_wait_v hpre rfl hi h hc hf
  | elA u =>
    cases u
    · exact step_elA_k0 hpre hg rfl hi h hc hf
    · exact step_elA_q0 hpre rfl hi h hc hf
    · exact step_elA_q1 hpre rfl hi h hc hf
    · exact step_elA_v0 hpre rfl hi h hc hf
    · exact step_elA_k hpre hg rfl hi h hc hf
    · exact step_elA_v hpre rfl hi h hc hf
  | arrive u =>
    cases u
    · exact step_arrive_k0 hpre hg rfl hi h hc hf
    · exact step_arrive_q0 rfl hi h hc hf
    · exact step_arrive_q1 hpre rfl hi h hc hf
    · exact step_arrive_v0 rfl hi h hc hf
    · exact step_arrive_k hpre hg rfl hi h hc hf
    · exact step_arrive_v rfl hi h hc hf
  | elC u j =>
    cases u
    · rcases Store.fin2_cases j with rfl | rfl
      · exact step_elC_k0_0 hpre rfl hi h hc hf
      · exact step_elC_k0_1 hpre rfl hi h hc hf
    · rcases Store.fin2_cases j with rfl | rfl
      · exact step_elC_q0_0 hpre rfl hi h hc hf
      · exact step_elC_q0_1 hpre rfl hi h hc hf
    · rcases Store.fin2_cases j with rfl | rfl
      · exact step_elC_q1_0 hpre rfl hi h hc hf
      · exact step_elC_q1_1 hpre rfl hi h hc hf
    · exact step_elC_v0 hpre hg rfl hi h hc hf
    · rcases Store.fin2_cases j with rfl | rfl
      · exact step_elC_k_0 hpre rfl hi h hc hf
      · exact step_elC_k_1 hpre rfl hi h hc hf
    · exact step_elC_v hpre hg rfl hi h hc hf
  | copy u j =>
    cases u
    · rcases Store.fin2_cases j with rfl | rfl
      · exact step_copy_k0_0 rfl hi h hc hf
      · exact step_copy_k0_1 rfl hi h hc hf
    · rcases Store.fin2_cases j with rfl | rfl
      · exact step_copy_q0_0 rfl hi h hc hf
      · exact step_copy_q0_1 hpre rfl hi h hc hf
    · rcases Store.fin2_cases j with rfl | rfl
      · exact step_copy_q1_0 rfl hi h hc hf
      · exact step_copy_q1_1 hpre rfl hi h hc hf
    · exact step_copy_v0 hpre rfl hi h hc hf
    · rcases Store.fin2_cases j with rfl | rfl
      · exact step_copy_k_0 rfl hi h hc hf
      · exact step_copy_k_1 hpre rfl hi h hc hf
    · exact step_copy_v hpre rfl hi h hc hf
  | drain k =>
    fin_cases k
    · exact step_drain0 hpre rfl hi h hc hf
    · exact step_drain1 hpre rfl hi h hc hf
    · exact step_drain2 hpre rfl hi h hc hf
    · exact step_drain3 hpre rfl hi h hc hf
    · exact step_drain4 hpre rfl hi h hc hf
    · exact step_drain5 hpre rfl hi h hc hf
  | drainQ => exact step_drainQ hpre rfl hi h hc hf
  | elTail => exact step_elTail hpre rfl hi h hc hf
  | arriveTail => exact step_arriveTail hpre rfl hi h hc hf
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

/-- The loader role as a code machine. -/
@[reducible] def code (A : List Assumption) (L : Launch) (g : Nat) : Flow.Code kernel A L g where
  D := D
  init := ⟨.setMaxReg, 0, 0, 0, 1, 1⟩
  pc := (·.site.pc)
  facts := facts L g
  inv := Inv L g
  next := next L g

/-- Every loader state satisfies the code machine's obligation. -/
theorem stepAt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (d : D) : (code asms L g).StepAt d where
  site _ := site_ok d
  step := by
    intro t e u ins h hi hc hf
    have h' : At t d.site.pc (facts L g d) := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    rcases step hpre hg hi h' hc hf with hn | ⟨d', t', hn, hr, ht, hi'⟩
    · exact .inl (.inl hn)
    · exact .inl (.inr ⟨d', t', hn, hr,
        ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, hi'⟩)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
