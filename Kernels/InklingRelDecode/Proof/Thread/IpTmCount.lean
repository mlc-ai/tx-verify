-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ShapeBarOrd
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.Resource

@[expose] public section

/-!
# The paired Tensor Memory operations of a thread, as a measure of its abstract state

The kernel's `tcgen05.alloc`, `tcgen05.relinquish_alloc_permit` and `tcgen05.dealloc` are guarded
by `%p3` (`tid < 32`), so only the threads of warp 0 make them: the common start's allocation and
permit relinquishment, and the epilogue's deallocation. (The second `tcgen05.dealloc`, pc 2854,
belongs to the exit role, which no state of a machine is at: it is guarded by the false `%p3` of a
worker and skipped.)

`resPcs` lists the positions of the four paired instructions; each machine's sites outside the
three states that fire them have other positions (`dstart_res_pc` …). `dBase` is the number of
paired operations a warp-0 thread has made before the event of a default-partition state: 0 at the
allocation, 1 from the allocation's store to the permit relinquishment, 2 from there to the
deallocation, 3 at the return. `dInc` is the operations the state's event makes. A step adds the
state's increment (`dBase_next`), given that the epilogue's guard register is the thread's `%p3`.
A thread outside warp 0 makes no operation at all.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.IpTm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

/-- The positions of the paired Tensor Memory instructions: the allocation, the permit
relinquishment and the two deallocations. -/
def resPcs : List Nat :=
  [DStart.Site.alloc.pc, DStart.Site.relinq.pc, Epi.Site.dealloc.pc, Flow.tmemDealloc_1]

/-- **The kernel's paired Tensor Memory instructions are at four positions.** -/
theorem kernel_res_pcs : OpPcsFast kernel.code tmemOp resPcs = true := by decide +kernel

/-- Prove a statement about the sites of one machine at a list of positions: by cases on the
site, deciding each. -/
local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem dstart_res_pc : ∀ s : DStart.Site, s.pc ∈ resPcs →
    s ∈ ([.alloc, .allocWr, .relinq] : List DStart.Site) := by site_cls
theorem pro_res_pc : ∀ s : ProA.Site, s.pc ∈ resPcs → s ∈ ([] : List ProA.Site) := by site_cls
theorem sm_res_pc : ∀ s : Sm.Site, s.pc ∈ resPcs → s ∈ ([] : List Sm.Site) := by site_cls
theorem epi_res_pc : ∀ s : Epi.Site, s.pc ∈ resPcs → s ∈ ([.dealloc] : List Epi.Site) := by
  site_cls
theorem worker_res_pc : ∀ s : Worker.Site, s.pc ∈ resPcs → s ∈ ([] : List Worker.Site) := by
  site_cls
theorem idle_res_pc : ∀ s : Worker.Idle.Site, s.pc ∈ resPcs →
    s ∈ ([] : List Worker.Idle.Site) := by site_cls
theorem loader_res_pc : ∀ s : Loader.Site, s.pc ∈ resPcs → s ∈ ([] : List Loader.Site) := by
  site_cls
theorem mma_res_pc : ∀ s : Mma.Site, s.pc ∈ resPcs → s ∈ ([] : List Mma.Site) := by site_cls
theorem exitsite_res_pc : ∀ s : WComp.ExitSite, s.pc ∈ resPcs →
    s ∈ ([] : List WComp.ExitSite) := by site_cls

/-- **No worker state is at a paired Tensor Memory instruction.** -/
theorem worker_notRes (s : WComp.WSt) : WComp.pc s ∉ resPcs := by
  cases s with
  | worker w => exact fun h => by simpa using worker_res_pc w.site h
  | idle d => exact fun h => by simpa using idle_res_pc d.site h
  | loader d _ => exact fun h => by simpa using loader_res_pc d.site h
  | mma d _ => exact fun h => by simpa using mma_res_pc d.site h
  | exit x => exact fun h => by simpa using exitsite_res_pc x.site h

/-! ### The count of a warp-0 thread -/

/-- The paired operations a warp-0 thread has made before the event of a default-partition
state. -/
def dBase : DComp.St → Nat
  | .dstart d =>
    match d.site with
    | .alloc => 0
    | .allocWr | .bar0 | .ld0 | .bar1 | .relinq => 1
    | .shfl | .toProA => 2
  | .pro _ => 2
  | .sm _ => 2
  | .epi d => if d.site = .exit then 3 else 2

/-- The paired operations the event of a default-partition state makes (when its guard holds). -/
def dInc : DComp.St → Nat
  | .dstart d =>
    match d.site with
    | .alloc | .relinq => 1
    | _ => 0
  | .epi d => if d.site = .dealloc then 1 else 0
  | _ => 0

/-- The paired operations a thread has made before the event of a state of the default
partition: `dBase` for the threads of warp 0, none for the others. -/
def dCnt (L : Launch) (g : Nat) (s : DComp.St) : Nat :=
  if g % L.block < 32 then dBase s else 0

/-! ### The steps -/

/-- A successor of `none` or `some none` under `Option.map` stays so. -/
theorem map_map_eq {α β : Type} {x : Option (Option α)} {f : α → β} {y : β}
    (h : x.map (Option.map f) = some (some y)) : ∃ a, x = some (some a) ∧ f a = y := by
  cases x with
  | none => simp at h
  | some o =>
    cases o with
    | none => simp at h
    | some a => exact ⟨a, rfl, by simpa using h⟩

theorem epi_next_base {d d' : Epi.D} {e : Event} (hp : d.pr.p3 = true)
    (h : Epi.next d e = some (some d')) :
    dBase (.epi d') = dBase (.epi d) + dInc (.epi d) := by
  unfold Epi.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [dBase, dInc, Epi.D.stores, Epi.stNext]
       done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [dBase, dInc, Epi.D.stores, Epi.stNext]
       split_ifs <;> simp_all)

theorem dBase_start (p : Epi.Prm) (sk : Bool) :
    dBase (.epi (if sk then Epi.D.startSk p else Epi.D.start p)) = 2 := by
  split <;> rfl

/-- **A step of the default partition's machine adds the state's increment**, for a thread of
warp 0 whose epilogue's guard register is its `%p3`. -/
theorem dBase_next {L : Launch} {g : Nat} {Q : Params} {s s' : DComp.St} {e : Event}
    (hl : g % L.block < 32)
    (hp : ∀ d, s = .epi d → d.pr.p3 = true)
    (h : DComp.next L g Q s e = some (some s')) : dBase s' = dBase s + dInc s := by
  cases s with
  | dstart d =>
    obtain ⟨site, tm⟩ := d
    have hlane : laneOf L g = 0 ∨ ¬ laneOf L g = 0 := by omega
    cases site
    · rcases hlane with hl0 | hl0 <;>
        simp [DComp.next, DComp.dstartNext, DStart.next, hl0] at h <;> subst h <;>
        simp [dBase, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      subst h
      simp [dBase, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      subst h
      simp [dBase, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      obtain ⟨a, ha, rfl⟩ := h
      have hb : a.site = DStart.Site.bar1 := by
        repeat' split at ha
        all_goals first
          | (simp at ha; done)
          | (simp only [Option.some.injEq] at ha; subst ha; rfl)
      simp [hb, dBase, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next, hl] at h
      subst h
      simp [dBase, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      subst h
      simp [dBase, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
      obtain ⟨a, ha, rfl⟩ := h
      have hb : a.site = DStart.Site.toProA := by
        repeat' split at ha
        all_goals first
          | (simp at ha; done)
          | (simp only [Option.some.injEq] at ha; subst ha; rfl)
      simp [hb, dBase, dInc]
    · simp [DComp.next, DComp.dstartNext, DStart.next] at h
  | pro d =>
    have hne := pro_ne h
    simp only [DComp.next, DComp.proNext] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [dBase, dInc]
      · simp at h
    · obtain ⟨a, ha, rfl⟩ := map_map_eq h
      simp [dBase, dInc]
  | sm d =>
    simp only [DComp.next, DComp.smNext] at h
    split at h
    · simp only [DComp.exitNext] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rw [dBase_start]
        simp [dBase, dInc]
      · simp at h
    · obtain ⟨a, ha, rfl⟩ := map_map_eq h
      simp [dBase, dInc]
  | epi d =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq (show (Epi.next d e).map
      (Option.map DComp.St.epi) = some (some s') from h)
    exact epi_next_base (hp d rfl) ha

end
end PTX.Kernels.InklingRelDecode.Proof.IpTm
