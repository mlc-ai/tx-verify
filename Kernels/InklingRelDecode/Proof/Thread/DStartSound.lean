-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartStepC
public import Lemmas.Flow.Compose

@[expose] public section

/-! # The common start's obligations as a code machine

Every site is an event instruction whose guard holds by the facts (`site_ok`: the allocation and
the relinquishment are guarded by `%p3`, which holds in the states of warp 0 by `Inv.lane0`), and
every event fired at a state steps to the state `next` gives, or leaves the machine, or is a
fault (`step`). `code` is the machine from the thread's first event, `stepAt` its obligation for
every state. -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {Q : Params} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- Every site is an event instruction whose guard holds by its facts. -/
theorem site_ok (hi : Inv L g Q d) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g Q d) ins.guard := by
  obtain ⟨s, tm⟩ := d
  cases s
  · have hl : g % L.block < 32 := hi.lane0 (.inl rfl)
    exact ⟨_, Flow.code_tmemAlloc_0, rfl, tbl_mem (by live_dec) (by simp [valueOf, table, hl])⟩
  · have hl : g % L.block < 32 := hi.lane0 (.inr (.inl rfl))
    exact ⟨_, Flow.code_tmemAlloc_0, rfl, tbl_mem (by live_dec) (by simp [valueOf, table, hl])⟩
  · exact ⟨_, Flow.code_bar_0, rfl, trivial⟩
  · exact ⟨_, Flow.code_load_0, rfl, trivial⟩
  · exact ⟨_, Flow.code_bar_1, rfl, trivial⟩
  · have hl : g % L.block < 32 := hi.lane0 (.inr (.inr rfl))
    exact ⟨_, Flow.code_tmemRelinquish_0, rfl,
      tbl_mem (by live_dec) (by simp [valueOf, table, hl])⟩
  · exact ⟨_, Flow.code_shfl_0, rfl, trivial⟩
  · exact ⟨_, Flow.code_setMaxReg_0, rfl, trivial⟩

/-- Every event fired at a state steps to its successor. -/
theorem step (hi : Inv L g Q d) (h : AtS L g Q d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g Q d e u := by
  obtain ⟨s, tm⟩ := d
  cases s
  · exact step_alloc rfl hi h hc hf
  · exact step_allocWr rfl hi h hc hf
  · exact step_bar0 rfl hi h hc hf
  · exact step_ld0 rfl hi h hc hf
  · exact step_bar1 rfl hi h hc hf
  · exact step_relinq rfl hi h hc hf
  · exact step_shfl rfl hi h hc hf
  · exact .inl (.inl (by simp [next]))

/-- The first state of a thread: the allocation for the threads of warp 0 (`%p3` holds), the first
barrier for the others (which skip the allocation). -/
def D.start (L : Launch) (g : Nat) : D :=
  if g % L.block < 32 then ⟨.alloc, b32 0⟩ else ⟨.bar0, b32 0⟩

/-- The common start as a code machine from the thread's first event. -/
@[reducible] def code (L : Launch) (g : Nat) (Q : Params) : Flow.Code kernel asms L g where
  D := D
  init := D.start L g
  pc := (·.site.pc)
  facts := facts L g Q
  sub := (·.site.sub)
  inv := Inv L g Q
  next := next L g

/-- Every state satisfies the code machine's obligation. -/
theorem stepAt (Q : Params) (d : D) : (code L g Q).StepAt d where
  site hi := site_ok hi
  step := by
    intro t e u ins h hi hc hf
    exact step hi h hc hf

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
