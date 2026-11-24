-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainLaterSelection
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCacheLoopProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Loader
  (loaderLinear loaderSteadyCounterInitCore loaderSteadyCounterGateWithFrame)

private def drainSchedulerRoots (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (1062,b32 (warpIndex l g))::drainSchedulerFrame p l g

private theorem drainTailOfCarry {p : Params} {l : Launch} {g use : Nat}
    {regs : Nat → Option Value} (hCarry : Holds regs (drainCarry l use))
    (hRoots : Holds regs (drainSchedulerRoots p l g)) :
    Holds regs (firstDrainTail p l g use) :=
  ⟨hRoots.1,(holds_append ..).mpr ⟨hCarry,hRoots.2⟩⟩

/-- The steady exit carries the final ring cursor into the scheduler's terminal request scan. -/
theorem cacheDrainEntryOfSteadyDone {p : Params} {l : Launch} {X : Execution}
    {g trips shuffles votes : Nat} {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (cur : SteadyCacheDone l X g trips F shuffles votes ends)
    (hRoots : ∀ lane < 32, Holds (cur.state lane).regs
      ((1062,b32 (warpIndex l (warpLane l g lane)))::drainSchedulerFrame p l (warpLane l g lane))) :
    CacheDrainEntry p l X g (cacheUseOfRound trips) := by
  refine ⟨shuffles,votes,ends,cur.advanceLocal ?_⟩
  intro lane hl
  have ht := cur.checkpoint lane hl
  have hCarry : Holds (cur.state lane).regs (drainCarry l (cacheUseOfRound trips)) :=
    ((holds_append ..).mp ht.2.2.2.2.2.2).1
  exact ⟨_,.refl,ht.mono (drainTailOfCarry hCarry (hRoots lane hl))⟩

set_option maxRecDepth 4096 in
private theorem warmExhaustedLocal {p : Params} {l : Launch} {g trips : Nat}
    (hSmall : trips ≤ 9) (hw : warpIndex l g = 14 ∨ warpIndex l g = 15)
    {t : TState}
    (ht : At t 1353 ([(1091,b32 trips),(7,.pred false)] ++
      firstDrainTail p l g (cacheUseOfRound trips))) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 1744 (firstDrainTail p l g (cacheUseOfRound trips)) := by
  let E := firstDrainTail p l g (cacheUseOfRound trips)
  let warp := warpIndex l g
  have hTrip : trips < 2^31 := by omega
  obtain ⟨s,hs,hS⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (loaderSteadyCounterInitCore (l := l) (g := g) hTrip) ht
  let G := [(7181,b32 (min trips 9)),(1091,b32 trips)]++E
  have hsIn : At s 1355 ([(1062,b32 warp),(7,.pred false)]++G) := by
    apply hS.mono
    have hr := hS.2.2.2.2
    exact ⟨hr.2.2.2.1,hr.2.2.1,hr.1,hr.2.1,hr.2.2.2⟩
  have hSeg : Seg kernel [] l g 3 1355 [(1062,b32 warp),(7,.pred false)] 1358
      [(202,.pred true)] := by
    intro a ha
    rcases hw with hw | hw <;> simp only [warp,hw] at ha <;> seg_fp ha using rfl
  obtain ⟨v,hv,hV⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSeg hsIn
  obtain ⟨w,hwRun,hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1358 true hV hV.2.2.2.2.1 (by simp)
  have hwAll := (loaderLinear (regs := []) (by decide) (by decide) hV.1
    (by simp) (by decide) hwRun).1
  have hwIn : At w 1384 ([(7181,b32 (min trips 9)),(1091,b32 trips)]++E) :=
    hW.mono hW.2.2.2.2.2
  obtain ⟨u,hu,hU⟩ := loaderSteadyCounterGateWithFrame (g := g) hTrip
    ((Nat.min_le_left trips 9).trans_lt hTrip)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) w hwIn
  have huAt := hU.mono hU.2.2.2.2.2.2
  rw [Nat.min_eq_left hSmall,ite_eq_right (Nat.lt_irrefl _)] at huAt
  exact ⟨u,(run_rtg hs).trans ((run_rtg hv).trans ((run_rtg hwAll).trans (run_rtg hu))),huAt⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
