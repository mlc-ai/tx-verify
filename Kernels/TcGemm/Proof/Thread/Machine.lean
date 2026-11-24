-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Thread.StepsTail
public import Kernels.TcGemm.Proof.Thread.Start

@[expose] public section

/-! # `tc_gemm`: the thread's machine is sound

The obligations of the site machine (`Flow.Code.Sound`): the start reaches the allocation on
warp 0 and the first barrier elsewhere, and every site is an unguarded event instruction whose
step reaches its successor or a dead state. -/

namespace PTX.Kernels.TcGemm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {g : Nat}

/-- Each site is an unguarded event instruction. -/
theorem site_ok (d : ThreadD) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L A B D g d) ins.guard := by
  obtain ⟨s, c, vals⟩ := d
  cases s with
  | alloc | allocSt => exact ⟨_, Flow.code_tmemAlloc_0, rfl, trivial⟩
  | init0 => exact ⟨_, Flow.code_mbarInit_0, rfl, trivial⟩
  | init1 => exact ⟨_, Flow.code_mbarInit_1, rfl, trivial⟩
  | fence => exact ⟨_, Flow.code_fenceProxy_0, rfl, trivial⟩
  | arrive => exact ⟨_, Flow.code_mbarArrive_0, rfl, trivial⟩
  | bulkA => exact ⟨_, Flow.code_bulkCopy_0, rfl, trivial⟩
  | bulkB => exact ⟨_, Flow.code_bulkCopy_1, rfl, trivial⟩
  | bar0 => exact ⟨_, Flow.code_bar_0, rfl, trivial⟩
  | load => exact ⟨_, Flow.code_load_0, rfl, trivial⟩
  | wait0 => exact ⟨_, Flow.code_mbarWait_0, rfl, trivial⟩
  | mma => exact ⟨_, Flow.code_mma_0, rfl, trivial⟩
  | commit => exact ⟨_, Flow.code_tcCommit_0, rfl, trivial⟩
  | wait1 => exact ⟨_, Flow.code_mbarWait_1, rfl, trivial⟩
  | fence1 => exact ⟨_, Flow.code_tcFence_0, rfl, trivial⟩
  | ld => exact ⟨_, Flow.code_tmemLoad_0, rfl, trivial⟩
  | waitLd => exact ⟨_, Flow.code_tmemWait_0, rfl, trivial⟩
  | st j =>
    by_cases hj : j < 4
    · refine ⟨⟨none, storeLo⟩, ?_, rfl, trivial⟩
      simp only [Site.pc, hj, ↓reduceIte]; exact Flow.code_store_0
    · refine ⟨⟨none, storeHi⟩, ?_, rfl,
        trivial⟩
      simp only [Site.pc, hj, ↓reduceIte]; exact Flow.code_store_1
  | fenceB => exact ⟨_, Flow.code_tcFence_1, rfl, trivial⟩
  | bar1 => exact ⟨_, Flow.code_bar_1, rfl, trivial⟩
  | fence2 => exact ⟨_, Flow.code_tcFence_2, rfl, trivial⟩
  | dealloc => exact ⟨_, Flow.code_tmemDealloc_0, rfl, trivial⟩
  | exit => exact ⟨_, Flow.code_exit_0, rfl, trivial⟩

/-- Every site's event reaches its successor or a dead state. -/
theorem step (hpre : Pre L A B D a b mem0) (hg : g < L.threads) {d : ThreadD} {t u : TState}
    {e : Event} {ins : Instr} (h : (code L A B D g).AtD d t) (hi : Inv g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl [] L g t ins.op) e (some u)) : Step L A B D g d u e := by
  obtain ⟨s, c, vals⟩ := d
  cases s with
  | alloc => exact step_alloc hpre hg h hi hc hf
  | allocSt => exact step_allocSt hpre hg h hi hc hf
  | init0 => exact step_init0 hpre hg h hi hc hf
  | init1 => exact step_init1 hpre hg h hi hc hf
  | fence => exact step_fence h hi hc hf
  | arrive => exact step_arrive hpre hg h hi hc hf
  | bulkA => exact step_bulkA hpre hg h hi hc hf
  | bulkB => exact step_bulkB hpre hg h hi hc hf
  | bar0 => exact step_bar0 h hi hc hf
  | load => exact step_load hpre hg h hi hc hf
  | wait0 => exact step_wait0 hpre hg h hi hc hf
  | mma => exact step_mma hpre hg h hi hc hf
  | commit => exact step_commit hpre hg h hi hc hf
  | wait1 => exact step_wait1 hpre hg h hi hc hf
  | fence1 => exact step_fence1 hpre hg h hi hc hf
  | ld => exact step_ld hpre hg h hi hc hf
  | waitLd => exact step_waitLd hpre hg h hi hc hf
  | st j => exact step_st hpre hg h hi hc hf
  | fenceB => exact step_fenceB h hi hc hf
  | bar1 => exact step_bar1 h hi hc hf
  | fence2 => exact step_fence2 h hi hc hf
  | dealloc => exact step_dealloc hpre h hi hc hf
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    exact absurd hf.2 (by simp)

/-- **Every thread of a launch satisfying the precondition is simulated by its machine.** -/
theorem sound (hpre : Pre L A B D a b mem0) (hg : g < L.threads) : (code L A B D g).Sound where
  start := start hpre hg
  steps := fun d => ⟨fun _ => site_ok d, fun _ h hi hc hf => step hpre hg h hi hc hf⟩

end
end PTX.Kernels.TcGemm.Proof
