-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Lemmas.Flow.NotInit
public import Lemmas.Flow.NotArrive
public import Lemmas.Flow.NotWait

@[expose] public section

/-!
# Which instructions of the kernel initialize, arrive on and poll an mbarrier

An audit of the decoded program by `decide +kernel`, through the machines' site accessors: the
initializations are the prologue's 12 (`ProA.inSites`); the arrivals are the prologue's three
`expect_tx` arrivals, the softmax region's `p_ready` arrival and the loader's `kv_ready` arrival;
the polls are the softmax region's `s_ready` and `o_done` polls, the loader's `kv_empty` poll, the
MMA warp's `kv_ready` and `p_ready` polls and the epilogue's `o_final` poll (the commits are
`MmaFacts`). Then, for each kind, the states of the thread machines at those positions
(`init_state`, `arrive_state`, `wait_state`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- Prove a statement about the sites of one machine at a list of positions: by cases on the
site, deciding each. -/
local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

def initPcs : List Nat := ProA.inSites.map (·.pc)

def arrivePcs : List Nat :=
  [ProA.Site.arr0.pc, ProA.Site.arr1.pc, ProA.Site.arr2.pc, Sm.Site.arrive.pc,
    Loader.Site.arrive.pc]

def waitPcs : List Nat :=
  [Sm.Site.waitS.pc, Sm.Site.waitO.pc, Loader.Site.wait.pc, Mma.Site.kvWait.pc,
    Mma.Site.pWait.pc, Epi.Site.wait.pc]

/-- Instructions that are an `mbarrier.try_wait`. -/
def isWaitOp : Op → Bool
  | .mbarWait .. => true
  | _ => false

theorem kernel_init_pcs : OpPcsFast kernel.code initOp initPcs = true := by decide +kernel

theorem kernel_arrive_pcs : OpPcsFast kernel.code arriveOp arrivePcs = true := by decide +kernel

theorem kernel_wait_pcs : OpPcsFast kernel.code isWaitOp waitPcs = true := by decide +kernel

/-! ### Initializations -/

theorem dstart_init : ∀ s : DStart.Site, s.pc ∈ initPcs → s ∈ ([] : List DStart.Site) := by
  site_cls
theorem pro_init : ∀ s : ProA.Site, s.pc ∈ initPcs → s ∈ ProA.inSites := by site_cls
theorem sm_init : ∀ s : Sm.Site, s.pc ∈ initPcs → s ∈ ([] : List Sm.Site) := by site_cls
theorem epi_init : ∀ s : Epi.Site, s.pc ∈ initPcs → s ∈ ([] : List Epi.Site) := by site_cls
theorem worker_init : ∀ s : Worker.Site, s.pc ∈ initPcs → s ∈ ([] : List Worker.Site) := by
  site_cls
theorem idle_init : ∀ s : Worker.Idle.Site, s.pc ∈ initPcs → s ∈ ([] : List Worker.Idle.Site) := by
  site_cls
theorem loader_init : ∀ s : Loader.Site, s.pc ∈ initPcs → s ∈ ([] : List Loader.Site) := by
  site_cls
theorem mma_init : ∀ s : Mma.Site, s.pc ∈ initPcs → s ∈ ([] : List Mma.Site) := by site_cls
theorem exit_init : ∀ s : WComp.ExitSite, s.pc ∈ initPcs → s ∈ ([] : List WComp.ExitSite) := by
  site_cls

/-! ### Arrivals -/

theorem dstart_arrive : ∀ s : DStart.Site, s.pc ∈ arrivePcs → s ∈ ([] : List DStart.Site) := by
  site_cls
theorem pro_arrive : ∀ s : ProA.Site, s.pc ∈ arrivePcs →
    s ∈ ([.arr0, .arr1, .arr2] : List ProA.Site) := by site_cls
theorem sm_arrive : ∀ s : Sm.Site, s.pc ∈ arrivePcs → s ∈ ([.arrive] : List Sm.Site) := by
  site_cls
theorem epi_arrive : ∀ s : Epi.Site, s.pc ∈ arrivePcs → s ∈ ([] : List Epi.Site) := by site_cls
theorem worker_arrive : ∀ s : Worker.Site, s.pc ∈ arrivePcs → s ∈ ([] : List Worker.Site) := by
  site_cls
theorem idle_arrive : ∀ s : Worker.Idle.Site, s.pc ∈ arrivePcs →
    s ∈ ([] : List Worker.Idle.Site) := by site_cls
theorem loader_arrive : ∀ s : Loader.Site, s.pc ∈ arrivePcs →
    s ∈ ([.arrive] : List Loader.Site) := by site_cls
theorem mma_arrive : ∀ s : Mma.Site, s.pc ∈ arrivePcs → s ∈ ([] : List Mma.Site) := by site_cls
theorem exit_arrive : ∀ s : WComp.ExitSite, s.pc ∈ arrivePcs →
    s ∈ ([] : List WComp.ExitSite) := by site_cls

/-! ### Polls -/

theorem dstart_wait : ∀ s : DStart.Site, s.pc ∈ waitPcs → s ∈ ([] : List DStart.Site) := by
  site_cls
theorem pro_wait : ∀ s : ProA.Site, s.pc ∈ waitPcs → s ∈ ([] : List ProA.Site) := by site_cls
theorem sm_wait : ∀ s : Sm.Site, s.pc ∈ waitPcs → s ∈ ([.waitS, .waitO] : List Sm.Site) := by
  site_cls
theorem epi_wait : ∀ s : Epi.Site, s.pc ∈ waitPcs → s ∈ ([.wait] : List Epi.Site) := by site_cls
theorem worker_wait : ∀ s : Worker.Site, s.pc ∈ waitPcs → s ∈ ([] : List Worker.Site) := by
  site_cls
theorem idle_wait : ∀ s : Worker.Idle.Site, s.pc ∈ waitPcs → s ∈ ([] : List Worker.Idle.Site) := by
  site_cls
theorem loader_wait : ∀ s : Loader.Site, s.pc ∈ waitPcs → s ∈ ([.wait] : List Loader.Site) := by
  site_cls
theorem mma_wait : ∀ s : Mma.Site, s.pc ∈ waitPcs →
    s ∈ ([.kvWait, .pWait] : List Mma.Site) := by site_cls
theorem exit_wait : ∀ s : WComp.ExitSite, s.pc ∈ waitPcs → s ∈ ([] : List WComp.ExitSite) := by
  site_cls

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
