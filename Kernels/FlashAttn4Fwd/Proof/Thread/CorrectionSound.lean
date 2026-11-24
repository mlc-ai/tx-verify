-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepStart
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepStraight
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepVote
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepWait
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepStat
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepRecip
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepFld
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepEnd
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepWaitLd
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepFree1
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepLoop

@[expose] public section

/-! # The correction warps' obligations as a code machine

Every correction site is an unguarded event instruction (`site_ok`), and every event fired at a
correction state steps to the state `next` gives, or the thread is dead where `next` stops
(`step`). The exit's `ret` ends the thread, so no step follows it. `code` is the role as a code
machine on its own (from `setmaxnreg`, item 0; the sub-step of a state is its site's: the
element of a vector store, the implicit wait of a load), and `stepAt` its obligation for every
state. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The instruction of each correction site: an unguarded event instruction. -/
theorem site_ok {L : Launch} {g : Nat} (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨s, i, tt, aw, a, o⟩ := d
  cases s with
  | rld st j => exact ⟨_, code_rld st j, rfl, trivial⟩
  | rldW st j => exact ⟨_, code_rld st j, rfl, trivial⟩
  | fld st j => exact ⟨_, code_fld st j, rfl, trivial⟩
  | fldW st j => exact ⟨_, code_fld st j, rfl, trivial⟩
  | rst st j =>
    obtain ⟨ss, hc⟩ := code_rst st j
    exact ⟨_, hc, rfl, trivial⟩
  | fst st j h el =>
    obtain ⟨base, off, srcs, hc, -⟩ := code_fst st j h el
    exact ⟨_, hc, rfl, trivial⟩
  | setMaxReg => exact ⟨_, Flow.code_setMaxReg_5, rfl, trivial⟩
  | bar0 => exact ⟨_, Flow.code_bar_3, rfl, trivial⟩
  | free st =>
    fin_cases st
    · exact ⟨_, Flow.code_mbarArrive_14, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_15, rfl, trivial⟩
  | sync st gen =>
    fin_cases st <;> cases gen
    · exact ⟨_, Flow.code_bar_4, rfl, trivial⟩
    · exact ⟨_, Flow.code_bar_6, rfl, trivial⟩
    · exact ⟨_, Flow.code_bar_8, rfl, trivial⟩
    · exact ⟨_, Flow.code_bar_5, rfl, trivial⟩
    · exact ⟨_, Flow.code_bar_7, rfl, trivial⟩
    · exact ⟨_, Flow.code_bar_9, rfl, trivial⟩
  | credit c =>
    fin_cases c
    · exact ⟨_, Flow.code_mbarArrive_16, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_18, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_20, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_21, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_22, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_25, rfl, trivial⟩
  | ldA st =>
    fin_cases st
    · exact ⟨_, Flow.code_load_1, rfl, trivial⟩
    · exact ⟨_, Flow.code_load_2, rfl, trivial⟩
  | vote st =>
    fin_cases st
    · exact ⟨_, Flow.code_vote_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_vote_1, rfl, trivial⟩
  | rwait st =>
    fin_cases st
    · exact ⟨_, Flow.code_tmemWait_4, rfl, trivial⟩
    · exact ⟨_, Flow.code_tmemWait_5, rfl, trivial⟩
  | oFree st fin =>
    fin_cases st <;> cases fin
    · exact ⟨_, Flow.code_mbarArrive_17, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_23, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_19, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_26, rfl, trivial⟩
  | ldL st =>
    fin_cases st
    · exact ⟨_, Flow.code_load_3, rfl, trivial⟩
    · exact ⟨_, Flow.code_load_4, rfl, trivial⟩
  | oWait st =>
    fin_cases st
    · exact ⟨_, Flow.code_mbarWait_36, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_38, rfl, trivial⟩
  | fWait st =>
    fin_cases st
    · exact ⟨_, Flow.code_mbarWait_37, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_39, rfl, trivial⟩
  | fence st =>
    fin_cases st
    · exact ⟨_, Flow.code_fenceProxy_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_fenceProxy_1, rfl, trivial⟩
  | staged st =>
    fin_cases st
    · exact ⟨_, Flow.code_mbarArrive_24, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_27, rfl, trivial⟩
  | tailWait => exact ⟨_, Flow.code_mbarWait_40, rfl, trivial⟩
  | barEnd => exact ⟨_, Flow.code_barArrive_4, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- A concrete state of a state at the first sub-step of its instruction. -/
theorem at_of {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d)) (h0 : d.site.sub = 0) : At t d.site.pc (facts L g d) :=
  ⟨h.1, h.2.1.trans h0, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Every event fired at a correction state steps to its successor, or the thread is dead. -/
theorem step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t u : TState} {e : Event}
    {ins : Instr} (hi : Inv L g d)
    (h : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨s, i, tt, aw, a, o⟩ := d
  cases s with
  | rldW st j => exact (step_rldW hpre st j rfl hi h hc hf).2
  | fldW st j => exact (step_fldW hpre st j rfl hi h hc hf).2
  | fst st j hh el => exact (step_fst hpre st j hh el rfl hi h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2 hc hf).2
  | rld st j => exact (step_rld st j rfl hi (at_of h rfl) hc hf).2
  | fld st j => exact (step_fld st j rfl hi (at_of h rfl) hc hf).2
  | rst st j => exact (step_rst hpre st j rfl hi (at_of h rfl) hc hf).2
  | setMaxReg => exact step_setMaxReg hpre rfl hi (at_of h rfl) hc hf
  | bar0 => exact step_bar0 hpre hg rfl hi (at_of h rfl) hc hf
  | barEnd => exact (step_barEnd hpre rfl hi (at_of h rfl) hc hf).2
  | exit => exact (step_exit rfl hc hf).elim
  | tailWait => exact step_tailWait hpre rfl hi (at_of h rfl) hc hf
  | free st =>
    fin_cases st
    · exact step_free0 hpre hg rfl hi (at_of h rfl) hc hf
    · exact step_free1 hpre hg rfl hi (at_of h rfl) hc hf
  | sync st gen =>
    fin_cases st <;> cases gen
    · exact step_sync0First hpre rfl hi (at_of h rfl) hc hf
    · exact step_sync0Loop hpre rfl hi (at_of h rfl) hc hf
    · exact step_sync0Last hpre rfl hi (at_of h rfl) hc hf
    · exact step_sync1First hpre rfl hi (at_of h rfl) hc hf
    · exact step_sync1Loop hpre rfl hi (at_of h rfl) hc hf
    · exact step_sync1Last hpre rfl hi (at_of h rfl) hc hf
  | credit c =>
    fin_cases c
    · exact step_credit0 hpre rfl hi (at_of h rfl) hc hf
    · exact step_credit1 hpre rfl hi (at_of h rfl) hc hf
    · exact step_credit2 hpre rfl hi (at_of h rfl) hc hf
    · exact step_credit3 hpre rfl hi (at_of h rfl) hc hf
    · exact step_credit4 hpre rfl hi (at_of h rfl) hc hf
    · exact step_credit5 hpre rfl hi (at_of h rfl) hc hf
  | ldA st =>
    fin_cases st
    · exact (step_ldA0 hpre rfl hi (at_of h rfl) hc hf).2
    · exact (step_ldA1 hpre rfl hi (at_of h rfl) hc hf).2
  | ldL st =>
    fin_cases st
    · exact (step_ldL0 hpre rfl hi (at_of h rfl) hc hf).2
    · exact (step_ldL1 hpre rfl hi (at_of h rfl) hc hf).2
  | vote st =>
    fin_cases st
    · exact (step_vote0 hpre rfl hi (at_of h rfl) hc hf).2
    · exact (step_vote1 hpre rfl hi (at_of h rfl) hc hf).2
  | rwait st =>
    fin_cases st
    · exact step_rwait0 hpre rfl hi (at_of h rfl) hc hf
    · exact step_rwait1 hpre rfl hi (at_of h rfl) hc hf
  | oFree st fin =>
    fin_cases st <;> cases fin
    · exact step_oFree0 hpre rfl hi (at_of h rfl) hc hf
    · exact step_oFree0Fin hpre rfl hi (at_of h rfl) hc hf
    · exact step_oFree1 hpre rfl hi (at_of h rfl) hc hf
    · exact step_oFree1Fin hpre rfl hi (at_of h rfl) hc hf
  | oWait st =>
    fin_cases st
    · exact step_oWait0 hpre rfl hi (at_of h rfl) hc hf
    · exact step_oWait1 hpre rfl hi (at_of h rfl) hc hf
  | fWait st =>
    fin_cases st
    · exact step_fWait0 hpre rfl hi (at_of h rfl) hc hf
    · exact step_fWait1 hpre rfl hi (at_of h rfl) hc hf
  | fence st =>
    fin_cases st
    · exact step_fence0 hpre rfl hi (at_of h rfl) hc hf
    · exact step_fence1 hpre rfl hi (at_of h rfl) hc hf
  | staged st =>
    fin_cases st
    · exact step_staged0 hpre rfl hi (at_of h rfl) hc hf
    · exact step_staged1 hpre rfl hi (at_of h rfl) hc hf

/-- The correction role as a code machine. -/
@[reducible] def code (A : List Assumption) (L : Launch) (g : Nat) : Flow.Code kernel A L g where
  D := D
  init := ⟨.setMaxReg, 0, 0, b32 0, 0, []⟩
  pc := (·.site.pc)
  facts := facts L g
  sub := (·.site.sub)
  inv := Inv L g
  next := next L g

/-- Every correction state satisfies the code machine's obligation. -/
theorem stepAt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (d : D) : (code asms L g).StepAt d where
  site _ := site_ok d
  step := by
    intro t e u ins h hi hc hf
    exact step hpre hg hi ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hc hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
