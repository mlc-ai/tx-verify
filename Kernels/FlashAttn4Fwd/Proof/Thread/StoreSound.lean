-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreSteps
public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreLoop

@[expose] public section

/-! # The store warp's obligations as a code machine

Every store site is an unguarded event instruction (`site_ok`), and every event fired at a
store state steps to the state `next` gives (`step`). The exit's `ret` ends the thread, so no
step follows it. `code` is the role as a code machine on its own (from `setmaxnreg`, item 0),
with `Inv` from its first event on, and `stepAt` its obligation for every state: the machine
skeleton composes the role through `Site.pc`, `facts`, `Inv`, `next` and these two lemmas. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Store
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The instruction of each store site: an unguarded event instruction. -/
theorem site_ok {L : Launch} {g : Nat} (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨s, i⟩ := d
  cases s with
  | setMaxReg => exact ⟨_, Flow.code_setMaxReg_3, rfl, trivial⟩
  | wait st =>
    rcases fin2_cases st with rfl | rfl
    · exact ⟨_, Flow.code_mbarWait_28, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarWait_29, rfl, trivial⟩
  | tma st h =>
    rcases fin2_cases st with rfl | rfl <;> rcases fin2_cases h with rfl | rfl
    · exact ⟨_, Flow.code_tensorCopy_10, rfl, trivial⟩
    · exact ⟨_, Flow.code_tensorCopy_11, rfl, trivial⟩
    · exact ⟨_, Flow.code_tensorCopy_12, rfl, trivial⟩
    · exact ⟨_, Flow.code_tensorCopy_13, rfl, trivial⟩
  | commit st =>
    rcases fin2_cases st with rfl | rfl
    · exact ⟨_, Flow.code_bulkCommit_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_bulkCommit_1, rfl, trivial⟩
  | drain r =>
    rcases fin2_cases r with rfl | rfl
    · exact ⟨_, Flow.code_bulkWait_0, rfl, trivial⟩
    · exact ⟨_, Flow.code_bulkWait_1, rfl, trivial⟩
  | free st =>
    rcases fin2_cases st with rfl | rfl
    · exact ⟨_, Flow.code_mbarArrive_8, rfl, trivial⟩
    · exact ⟨_, Flow.code_mbarArrive_9, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- Every event fired at a store state steps to its successor: the first event by
`step_start`, the others under the invariant. -/
theorem step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t u : TState} {e : Event}
    {ins : Instr} (hi : d.site = .setMaxReg ∨ Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  rcases hi with hs | hi
  · exact step_start hpre hg hs h hc hf
  obtain ⟨s, i⟩ := d
  cases s with
  | setMaxReg => exact step_start hpre hg rfl h hc hf
  | wait st => exact step_wait hpre st rfl hi h hc hf
  | tma st hh => exact step_tma hpre st hh rfl hi h hc hf
  | commit st => exact step_commit hpre st rfl hi h hc hf
  | drain r => exact step_drain hpre r rfl hi h hc hf
  | free st =>
    rcases fin2_cases st with rfl | rfl
    · exact step_free0 hpre rfl hi h hc hf
    · exact step_free1 hpre rfl hi h hc hf
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

/-- The store role as a code machine. -/
@[reducible] def code (A : List Assumption) (L : Launch) (g : Nat) : Flow.Code kernel A L g where
  D := D
  init := ⟨.setMaxReg, 0⟩
  pc := (·.site.pc)
  facts := facts L g
  inv d := d.site = .setMaxReg ∨ Inv L g d
  next := next L g

/-- Every store state satisfies the code machine's obligation. -/
theorem stepAt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (d : D) : (code asms L g).StepAt d where
  site _ := site_ok d
  step := by
    intro t e u ins h hi hc hf
    have h' : At t d.site.pc (facts L g d) := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    rcases step hpre hg hi h' hc hf with hn | ⟨d', t', hn, hr, ht, hi'⟩
    · exact .inl (.inl hn)
    · exact .inl (.inr ⟨d', t', hn, hr,
        ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, .inr hi'⟩)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Store
