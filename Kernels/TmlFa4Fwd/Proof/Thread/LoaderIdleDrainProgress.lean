-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderIdleProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.IdleLoaderObjects
public import Kernels.TmlFa4Fwd.Proof.LoaderIdleQDrain
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.MBarrier Prologue Epilogue Thread.Loader

noncomputable section

/-- Every idle release wait sees its object's initialized generation. -/
def IdleDrainReady (l : Launch) (X : Execution) (cta : Nat) : Prop :=
  ∀ obj : IdleReleaseObject,
    let log := X.objects (obj.loc l cta)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

private theorem waitCacheSlot (hMax : Maximal l kernel Assumptions.all m X) {g warp shuffles : Nat}
    (hg : g < l.threads) (hReady : IdleDrainReady l X (g/l.block)) (slot : Fin 3)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (drainWaitSite ⟨slot.val,by omega⟩).pc
      (fun _ => idleSlotFacts l warp slot) shuffles 0 ends) :
    Nonempty (SchedulerWarpReached l X g ((drainWaitSite ⟨slot.val,by omega⟩).pc+3)
      (fun _ => idleSlotFacts l warp slot) shuffles 0 ends) := by
  let idx : Fin 4 := ⟨slot.val,by omega⟩
  let addr := l.sharedBase+56+8*slot.val
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSize : addr < 2^32 := by have := hp.shared.2.1; have := slot.isLt; dsimp [addr]; omega
  have hAlign : addr % 8 = 0 := by have := hp.shared.1; dsimp [addr]; omega
  obtain ⟨s,hs,hPhase⟩ := hReady (.cache slot)
  have hLoc : (IdleReleaseObject.cache slot).loc l (g/l.block) = ⟨.shared,g/l.block,addr⟩ := by
    rw [IdleReleaseObject.cacheLoc]
    change initObject l (g/l.block) (emptySlot slot) = _
    rw [emptySlot_address]
    congr 1
    dsimp [addr]
    omega
  rw [hLoc] at hs
  apply loaderWarpWaitOfPhaseZero hMax hg hBlock (drainWaitCode idx) ?_ hSize hAlign cur
    ?_ ?_ ?_ hs hPhase
  · have h := drainWaitRange idx
    omega
  · intro lane hl pair hm hEq
    have hMap := List.mem_map_of_mem (f := Prod.fst) hm
    rw [hEq] at hMap
    exact (show (drainWaitSite idx).result ∉ (idleSlotFacts l warp slot).map Prod.fst by
      fin_cases slot <;> exact of_decide_eq_true rfl) hMap
  · intro lane hl
    fin_cases slot <;> simp [idleSlotFacts,drainWaitSite,idx,addr]
  · intro lane hl
    fin_cases slot <;> simp [idleSlotFacts,drainWaitSite,idx]

private theorem advanceCacheSlot {g warp shuffles : Nat} (slot : Fin 2) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g ((drainWaitSite ⟨slot.val,by omega⟩).pc+3)
      (fun _ => idleSlotFacts l warp ⟨slot.val,by omega⟩) shuffles 0 ends) :
    Nonempty (SchedulerWarpReached l X g (drainWaitSite ⟨slot.val+1,by omega⟩).pc
      (fun _ => idleSlotFacts l warp ⟨slot.val+1,by omega⟩) shuffles 0 ends) := by
  have hSize : l.sharedBase + 72 < 2^32 := by have := hp.shared.2.1; omega
  apply cur.advanceLocal
  intro lane hl
  have ht := cur.checkpoint lane hl
  obtain ⟨u,hu,huAt⟩ := idleAdvance slot l (warpLane l g lane) warp hSize _ ht
  obtain ⟨huA,_⟩ := loaderLinear (regs := []) (n := 8)
    (by fin_cases slot <;> decide) (by fin_cases slot <;> decide) ht.1
    (by fin_cases slot <;> (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases slot <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu
  exact ⟨u,run_rtg huA,huAt⟩

private theorem idleCacheFromDrain (hMax : Maximal l kernel Assumptions.all m X) {g shuffles : Nat}
    (hg : g < l.threads) (hReady : IdleDrainReady l X (g / l.block)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1862 (fun _ => loaderIdleDrainFacts l (warpIndex l g))
      shuffles 0 ends) :
    Nonempty (SchedulerWarpReached l X g 1891 (fun _ => idleDrainCarry l (warpIndex l g))
      shuffles 0 ends) := by
  have hSize : l.sharedBase + 72 < 2^32 := by have := hp.shared.2.1; omega
  obtain ⟨start⟩ := cur.advanceLocal (G := fun _ => idleSlotFacts l (warpIndex l g) 0)
    (pc' := 1866) (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      obtain ⟨u,hu,hAt⟩ := idleFirst l (warpLane l g lane) (warpIndex_lt hp g) hSize _ ht
      have huA := (loaderLinear (regs := []) (by decide) (by decide) ht.1
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hu).1
      exact ⟨u,run_rtg huA,hAt⟩)
  obtain ⟨done0⟩ := waitCacheSlot hp hMax hg hReady 0 start
  obtain ⟨start1⟩ := advanceCacheSlot hp 0 done0
  obtain ⟨done1⟩ := waitCacheSlot hp hMax hg hReady 1 start1
  obtain ⟨start2⟩ := advanceCacheSlot hp 1 done1
  obtain ⟨done2⟩ := waitCacheSlot hp hMax hg hReady 2 start2
  exact done2.advanceLocal (fun lane hl =>
    ⟨_, .refl, (done2.checkpoint lane hl).mono (done2.checkpoint lane hl).2.2.2.2.2.2.2⟩)

/-- Both idle loader warps drain the cache slots after searching every request group. -/
theorem idleCacheDrainedForBatchesOfMaximal (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block)
    (hReady : IdleDrainReady l X (g / l.block)) :
    ∃ shuffles ends, Nonempty (SchedulerWarpReached l X g 1891
      (fun _ => idleDrainCarry l (warpIndex l g)) shuffles 0 ends) := by
  obtain ⟨shuffles,ends,⟨cur⟩⟩ := idleDrainForBatchesOfMaximal hp hMax hg hw hCuQ hIdle
  exact ⟨shuffles,ends,idleCacheFromDrain hp hMax hg hReady cur⟩

/-- The idle second-query release is observed by every warp-fourteen lane before election. -/
theorem idleQueryDrainedAtOrdinal (hMax : Maximal l kernel Assumptions.all m X) {g shuffles : Nat}
    (hg : g < l.threads) (hReady : IdleDrainReady l X (g/l.block)) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1891 (fun _ => idleDrainCarry l 14) shuffles 0 ends) :
    Nonempty (SchedulerWarpReached l X g 1896 (fun _ => idleQCarry l) shuffles 0 ends) := by
  obtain ⟨start⟩ := cur.advanceLocal (pc' := 1893)
    (G := fun _ => (2305,b32 (l.sharedBase+24)) :: (7192,b32 1) :: idleQCarry l) (by
      intro lane hl
      obtain ⟨u,hu,hAt⟩ := qDrainReady hp (cur.checkpoint lane hl)
      exact ⟨u,run_rtg hu,hAt⟩)
  obtain ⟨s,hs,hPhase⟩ := hReady .secondQuery
  have hObject : (IdleReleaseObject.secondQuery).loc l (g/l.block) =
      ⟨.shared,g/l.block,l.sharedBase+24⟩ := rfl
  rw [hObject] at hs
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSize : l.sharedBase+24 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+24) % 8 = 0 := by have := hp.shared.1; omega
  obtain ⟨done⟩ := loaderWarpWaitOfPhaseZero hMax hg hBlock (drainWaitCode 3)
    (by decide) hSize hAlign start (by simp [drainWaitSite,idleQCarry]) (by simp [drainWaitSite])
    (by simp [drainWaitSite]) hs hPhase
  exact done.advanceLocal (fun lane hl =>
    ⟨_, .refl, (done.checkpoint lane hl).mono (done.checkpoint lane hl).2.2.2.2.2.2⟩)

end

/-- The value-loader warp skips the query drain and returns once its cache slots are released. -/
theorem valueLoaderExitOfDrained {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes phase : Nat}
    (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1891 (fun _ => terminalLoaderFrame l 15 phase)
      shuffles votes ends) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hu := cur.checkpoint lane hl
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := warpLane l g lane)
    Flow.code_1891 true hu hu.2.2.2.2.2.1 (by simp)
  obtain ⟨hvA,_⟩ := loaderLinear (regs := []) (by decide) (by decide) hu.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hv
  have hAt : At v 1901 [(2535,b32 l.sharedBase),(1062,b32 15)] :=
    hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨u,_,hn⟩ := loaderRoleExit (g := warpLane l g lane) 1 hAt
  have hn' : Next kernel Assumptions.all l (warpLane l g lane) (cur.before lane) u .exit :=
    ⟨(cur.localSteps lane hl).trans ((run_rtg hvA).trans hn.steps),hn.stop⟩
  have hnG : Next kernel Assumptions.all l g (cur.before lane) u .exit := by
    simpa only [hSelf] using hn'
  refine ⟨cur.pos lane,_,Thread.exitAtMaximalCursor (o := ends lane) hMax hg
    (cur.positive lane hl) ?_ ?_ ?_ hnG ?_,rfl⟩
  · simpa only [hSelf] using cur.bounded lane hl
  · simpa only [hSelf] using cur.recorded lane hl
  · simpa only [hSelf] using cur.continuation lane hl
  · simpa only [hSelf] using cur.released lane hl

theorem idleWarp15ExitsAtOrdinal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1891 (fun _ => idleDrainCarry l 15) shuffles 0 ends) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit :=
  valueLoaderExitOfDrained hMax hg cur

end
end PTX.Kernels.TmlFa4Fwd.Loader
