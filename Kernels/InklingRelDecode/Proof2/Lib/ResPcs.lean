-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Common.Roles
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.Resource
public import Lemmas.Flow.NotClc

@[expose] public section

/-! # The positions of the Tensor Memory resource instructions and of the return

Read off the decoded program: the kernel's `tcgen05.alloc`, `tcgen05.relinquish_alloc_permit` and
two `tcgen05.dealloc` are at pcs 11, 15, 2851 and 2854 (`kernel_res_pcs`), its only `ret` at
pc 2855 (`kernel_ret_pcs`). Each machine's sites at these positions are listed per site type
(`*_special`): the startup's allocation (with its store sub-step) and relinquishment, the
epilogue's deallocation and return, the worker exit path's return. No prologue, softmax,
dispatch, idle, loader or MMA site is at one of them, and no worker site is at the second
deallocation (pc 2854, skipped by the worker's false `%p3`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The positions of the paired Tensor Memory instructions. -/
def resPcs : List Nat := [11, 15, 2851, 2854]

/-- **The kernel's paired Tensor Memory instructions are at four positions.** -/
theorem kernel_res_pcs : OpPcsFast kernel.code tmemOp resPcs = true := by decide +kernel

/-- A `ret` or `exit` instruction. -/
def isRet : Op → Bool
  | .ret => true
  | .exit => true
  | _ => false

/-- The position of the kernel's return. -/
def retPcs : List Nat := [2855]

/-- **The kernel's only return is at pc 2855.** -/
theorem kernel_ret_pcs : OpPcsFast kernel.code isRet retPcs = true := by decide +kernel

/-- The positions of both lists. -/
def specialPcs : List Nat := resPcs ++ retPcs

local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_special : ∀ s : Startup.Site, s.pc ∈ specialPcs →
    s ∈ ([.alloc, .allocWr, .relinq] : List Startup.Site) := by
  intro s h; revert h
  cases s with
  | enter r => cases r <;> decide
  | _ => decide

theorem proA_special (s : ProA.Site) : s.pc ∉ specialPcs := fun h => by
  have hm := ProA.site_mem s
  revert hm h
  generalize s.pc = p
  intro h hm
  simp only [specialPcs, resPcs, retPcs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> revert hm <;> decide

theorem sm_special : ∀ s : Proof.Sm.Site, s.pc ∈ specialPcs → s ∈ ([] : List Proof.Sm.Site) := by
  site_cls

theorem epi_special : ∀ s : Proof.Epi.Site, s.pc ∈ specialPcs →
    s ∈ ([.dealloc, .exit] : List Proof.Epi.Site) := by site_cls

theorem worker_special : ∀ s : Proof.Worker.Site, s.pc ∈ specialPcs →
    s ∈ ([] : List Proof.Worker.Site) := by site_cls

theorem idle_special : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ specialPcs →
    s ∈ ([] : List Proof.Worker.Idle.Site) := by site_cls

theorem loader_special : ∀ s : Proof.Loader.Site, s.pc ∈ specialPcs →
    s ∈ ([] : List Proof.Loader.Site) := by site_cls

theorem mma_special : ∀ s : Proof.Mma.Site, s.pc ∈ specialPcs →
    s ∈ ([] : List Proof.Mma.Site) := by site_cls

theorem exitsite_special : ∀ s : Proof.WComp.ExitSite, s.pc ∈ specialPcs →
    s ∈ ([.ret] : List Proof.WComp.ExitSite) := by site_cls

/-- **A worker state at a special position is the exit path's return.** -/
theorem worker_state_special (σ : Proof.WComp.WSt) (h : Proof.WComp.pc σ ∈ specialPcs) :
    ∃ P, σ = .exit ⟨.ret, P⟩ := by
  cases σ with
  | worker w => simpa using worker_special w.site h
  | idle d => simpa using idle_special d.site h
  | loader d _ => simpa using loader_special d.site h
  | mma d _ => simpa using mma_special d.site h
  | exit x =>
    obtain ⟨site, P⟩ := x
    have := exitsite_special site h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    subst this
    exact ⟨P, rfl⟩

/-- A resource event's instruction is at a position of `resPcs`. -/
theorem res_pc' {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {grp : CtaGroup}
    {dst : Option Loc} {act : Tmem.Request} (hk : e.kind = .tc (.resource grp dst act)) :
    pc ∈ resPcs :=
  OpPcsFast.mem kernel_res_pcs hc (fires_resource_op hf hk)

/-- A resource event's instruction is at a special position. -/
theorem res_pc {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {grp : CtaGroup}
    {dst : Option Loc} {act : Tmem.Request} (hk : e.kind = .tc (.resource grp dst act)) :
    pc ∈ specialPcs :=
  List.mem_append_left _ (res_pc' hc hf hk)

/-- An exit event's instruction is the return. -/
theorem ret_pc' {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hk : e.kind = .exit) :
    pc ∈ retPcs := by
  refine OpPcsFast.mem kernel_ret_pcs hc ?_
  rcases fires_exit_op hf hk with h | h <;> rw [h] <;> rfl

/-- An exit event's instruction is at a special position. -/
theorem ret_pc {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hk : e.kind = .exit) :
    pc ∈ specialPcs :=
  List.mem_append_right _ (ret_pc' hc hf hk)

end
end PTX.Kernels.InklingRelDecode.Proof2
