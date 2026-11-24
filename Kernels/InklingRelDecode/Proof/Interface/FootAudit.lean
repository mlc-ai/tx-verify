-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Writes
public import Kernels.InklingRelDecode.Proof.Thread.FootAll

@[expose] public section

/-!
# Which instructions write shared memory

`Interface/Writes.lean` audits the instructions that write global memory or write through a
symbolic address (`writePcs`): the epilogue's stores, the prologue's two writes of shared variables
and the dispatch table's. The instructions that write shared memory through a register are the
eight query stores (`ProA.stqSites`), the softmax region's scratch store (`Sm.Site.store10`) and
the Tensor Memory allocation's store of its address (`DStart.Site.alloc`, `allocWr`: one
instruction, two sub-steps). `kernel_shared_direct_pcs` is the audit, by `decide +kernel` through
the site accessors; `write_pc_shared` says a shared write event comes from one of these or from
`writePcs`.

The sites of each machine at those positions are `ProA.stqSites`, `Sm.Site.store10` and the two
allocation sites; no site of another machine is at one (`pro_pc_direct` and the `*_pc_notDirect`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The positions of the instructions that write shared memory through a register: the eight
query stores, the scratch store and the allocation's store. -/
def sharedDirectPcs : List Nat :=
  ProA.stqSites.map (·.pc) ++ [Sm.Site.store10.pc, DStart.Site.alloc.pc]

/-- Instructions that store to shared memory with a direct location rule. -/
def sharedStoreOp (op : Op) : Bool := storeSpace op == some .shared

/-- **The register-addressed shared writes of the program are the query stores, the scratch store
and the allocation.** -/
theorem kernel_shared_direct_pcs : OpPcsFast kernel.code sharedStoreOp sharedDirectPcs = true := by
  decide +kernel

/-- **A shared write event is fired at a write position**: a shared write by an instruction of the
program comes from `writePcs` (a store through a symbolic address) or `sharedDirectPcs`. -/
theorem write_pc_shared {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ins : Instr}
    {pc : Nat} {e : Event} {o : Option TState} {a : Acc} {bs : List Byte}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl A L g t ins.op) e o)
    (hk : e.kind = .wr a bs) (hsp : a.loc.space = .shared) :
    pc ∈ writePcs ∨ pc ∈ sharedDirectPcs := by
  rcases fires_write_space hf hk with h | h
  · right
    refine OpPcsFast.mem kernel_shared_direct_pcs hc ?_
    simp [sharedStoreOp, h, hsp]
  · left
    refine OpPcsFast.mem kernel_write_pcs hc ?_
    have hw := fires_write_op hf hk
    simp [globalWriteOp, h, hw]

/-! ### The sites of each machine at those positions -/

theorem pro_pc_direct (s : ProA.Site) (h : s.pc ∈ sharedDirectPcs) : s ∈ ProA.stqSites := by
  revert h
  cases s
  all_goals decide +kernel

theorem dstart_pc_direct (s : DStart.Site) (h : s.pc ∈ sharedDirectPcs) :
    s = .alloc ∨ s = .allocWr := by
  revert h
  cases s
  all_goals first
    | (intro _; first | (left; rfl) | (right; rfl))
    | (intro h; exfalso; revert h; decide +kernel)

theorem sm_pc_direct (s : Sm.Site) (h : s.pc ∈ sharedDirectPcs) : s = .store10 := by
  revert h
  cases s
  all_goals try (rename_i j; revert j)
  all_goals first
    | (intro _; rfl)
    | (intro h; exfalso; revert h; decide +kernel)
    | (intro j h; exfalso; revert j h; decide +kernel)

theorem epi_pc_notDirect (s : Epi.Site) : s.pc ∉ sharedDirectPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem worker_pc_notDirect (s : Worker.Site) : s.pc ∉ sharedDirectPcs := by
  cases s
  all_goals decide +kernel

theorem idle_pc_notDirect (s : Worker.Idle.Site) : s.pc ∉ sharedDirectPcs := by
  cases s
  all_goals decide +kernel

theorem loader_pc_notDirect (s : Loader.Site) : s.pc ∉ sharedDirectPcs := by
  cases s
  all_goals decide +kernel

theorem mma_pc_notDirect (s : Mma.Site) : s.pc ∉ sharedDirectPcs := by
  cases s
  all_goals try (rename_i j; revert j)
  all_goals decide +kernel

theorem exit_pc_notDirect (s : WComp.ExitSite) : s.pc ∉ sharedDirectPcs := by
  cases s
  all_goals decide +kernel

/-- **A worker state is at no register-addressed shared write position.** -/
theorem worker_state_notDirect (s : WComp.WSt) : WComp.pc s ∉ sharedDirectPcs := by
  cases s with
  | worker w => exact worker_pc_notDirect w.site
  | idle d => exact idle_pc_notDirect d.site
  | loader d _ => exact loader_pc_notDirect d.site
  | mma d _ => exact mma_pc_notDirect d.site
  | exit x => exact exit_pc_notDirect x.site

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
