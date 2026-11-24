-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Reach
public import Lemmas.Flow.WriteSpace
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.NotClc

@[expose] public section

/-!
# Which instructions of the kernel write memory the thread machines cannot place

The instructions that write global memory, or that write through a symbolic address, are exactly
the epilogue's 65 output stores (`Epi.Site.stLse`, `Epi.Site.stO`), the epilogue's write of the
dispatch table (`Epi.Site.stTab`) and the prologue's two writes of shared variables
(`ProA.Site.st8`, `ProA.Site.st9_0`, `ProA.Site.st9_1`). The audit is a `decide +kernel` over the
decoded program, stated through the machines' site accessors (`Site.pc`, `Epi.stPc`), so that no
literal program counter occurs.

From it, a state of the thread machine whose program counter is one of these is one of those
sites (`write_state`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The positions of the instructions that may write global memory: the output stores, the
dispatch-table write, and the prologue's shared-variable writes. -/
def writePcs : List Nat :=
  [Epi.Site.stLse.pc, Epi.Site.stTab.pc, ProA.Site.st8.pc, ProA.Site.st9_0.pc,
    ProA.Site.st9_1.pc] ++ (List.range 64).map Epi.stPc

/-- Instructions that write global memory or write through a symbolic address. -/
def globalWriteOp (op : Op) : Bool :=
  storeSpace op == some .global || (dynamicAccess op && writeOp op)

/-- **The writes of the program are the epilogue's and the prologue's.** -/
theorem kernel_write_pcs : OpPcsFast kernel.code globalWriteOp writePcs = true := by
  decide +kernel

/-- **A write event is fired at a write position**: a write to global memory by an instruction
of the program comes from one of `writePcs`. -/
theorem write_pc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ins : Instr}
    {pc : Nat} {e : Event} {o : Option TState} {a : Acc} {bs : List Byte}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl A L g t ins.op) e o)
    (hk : e.kind = .wr a bs) (hsp : a.loc.space = .global) : pc ∈ writePcs := by
  refine OpPcsFast.mem kernel_write_pcs hc ?_
  have hw := fires_write_op hf hk
  rcases fires_write_space hf hk with h | h
  · simp [globalWriteOp, h, hsp]
  · simp [globalWriteOp, h, hw]

/-! ### The sites of each machine at those positions -/

theorem epi_write_site (s : Epi.Site) (h : s.pc ∈ writePcs) :
    s = .stLse ∨ s = .stTab ∨ ∃ k, s = .stO k := by
  cases s
  all_goals first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; exact ⟨_, rfl⟩)
    | (exfalso; revert h; decide +kernel)

theorem pro_write_site (s : ProA.Site) (h : s.pc ∈ writePcs) :
    s = .st8 ∨ s = .st9_0 ∨ s = .st9_1 := by
  cases s
  all_goals first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; rfl)
    | (exfalso; revert h; decide +kernel)

theorem sm_pc_notWrite (s : Sm.Site) : s.pc ∉ writePcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem dstart_pc_notWrite (s : DStart.Site) : s.pc ∉ writePcs := by
  cases s
  all_goals decide +kernel

theorem worker_pc_notWrite (s : Worker.Site) : s.pc ∉ writePcs := by
  cases s
  all_goals decide +kernel

theorem idle_pc_notWrite (s : Worker.Idle.Site) : s.pc ∉ writePcs := by
  cases s
  all_goals decide +kernel

theorem loader_pc_notWrite (s : Loader.Site) : s.pc ∉ writePcs := by
  cases s
  all_goals decide +kernel

theorem mma_pc_notWrite (s : Mma.Site) : s.pc ∉ writePcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem exit_pc_notWrite (s : WComp.ExitSite) : s.pc ∉ writePcs := by
  cases s
  all_goals decide +kernel

/-- **A worker state is at no write position.** -/
theorem worker_state_notWrite (s : WComp.WSt) : WComp.pc s ∉ writePcs := by
  cases s with
  | worker w => exact worker_pc_notWrite w.site
  | idle d => exact idle_pc_notWrite d.site
  | loader d _ => exact loader_pc_notWrite d.site
  | mma d _ => exact mma_pc_notWrite d.site
  | exit x => exact exit_pc_notWrite x.site

/-- **A state at a write position is one of the epilogue's or the prologue's write sites.** -/
theorem write_state {s : TSt} (h : TSt.pc s ∈ writePcs) :
    (∃ d : Epi.D, s = .d (.epi d) ∧
      (d.site = .stLse ∨ d.site = .stTab ∨ ∃ k, d.site = .stO k)) ∨
    (∃ d : ProA.D, s = .d (.pro d) ∧
      (d.site = .st8 ∨ d.site = .st9_0 ∨ d.site = .st9_1)) := by
  cases s with
  | w s => exact absurd h (worker_state_notWrite s)
  | d s =>
    cases s with
    | dstart d => exact absurd h (dstart_pc_notWrite d.site)
    | pro d => exact .inr ⟨d, rfl, pro_write_site d.site h⟩
    | sm d => exact absurd h (sm_pc_notWrite d.site)
    | epi d => exact .inl ⟨d, rfl, epi_write_site d.site h⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
