-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmOpeningProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import all Kernels.TmlFa4Fwd.Proof.LoaderRingTail
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmIterationCursor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (kvUseStage kvEmptyPhase loaderPhaseWord loaderNextRingFacts loaderRingWordsOfUse
    warmRingStage steadyRingStage warmCounterWithFrame steadyRingCondition loaderLinear)

def cacheUseOfRound (round : Nat) : Nat := 2+2*round

def warmCacheHeadFrame (l : Launch) (round trips : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  [(7174,b32 round),(1091,b32 trips)] ++ drainCarry l (cacheUseOfRound round) ++ F

def warmCachePublishedFrame (round trips : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  let use := cacheUseOfRound round+1
  [(1139,b32 (kvUseStage use).val),(2064,loaderPhaseWord (kvEmptyPhase use)),
    (7174,b32 round),(1091,b32 trips)] ++ F

set_option maxRecDepth 4096 in
theorem warmCacheTailLocal {l : Launch} {g round trips : Nat} {t : TState}
    {F : List (Nat × Value)} (hTrips : trips < 2^31) (hRound : round < min trips 9)
    (hStage : ((kernel.code.drop 1343).take 5).all
      (fun ins => ([7174,1091]++F.map Prod.fst).all
        (fun r => !(writesRegs ins.op).contains r)) = true)
    (hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => ([7179,7180]++F.map Prod.fst).all
        (fun r => !(writesRegs ins.op).contains r)) = true)
    (hBase : (2535,b32 l.sharedBase) ∈ F)
    (ht : At t 1343 (warmCachePublishedFrame round trips F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if round+1 < min trips 9 then 917 else 1353)
        (warmCacheHeadFrame l (round+1) trips F) := by
  let use := cacheUseOfRound round+1
  let slot := kvUseStage use
  let phase := kvEmptyPhase use
  let E := [(7174,b32 round),(1091,b32 trips)]++F
  have hKeep : ((kernel.code.drop 1343).take 5).all
      (fun ins => (E.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := hStage
  obtain ⟨v,hv,hV⟩ := linearFramed (by decide) (by decide) hKeep
    (by set_option maxRecDepth 100000 in kernel_rfl) (warmRingStage l g slot phase) ht
  have hIn : At v 1348
      ([(7174,b32 round),(1091,b32 trips)]++loaderNextRingFacts slot phase++F) := by
    apply hV.mono
    have h := (holds_append ..).mp hV.2.2.2.2
    exact ⟨h.2.1,h.2.2.1,(holds_append ..).mpr ⟨h.1,h.2.2.2⟩⟩
  obtain ⟨u,hu,hU⟩ := warmCounterWithFrame (F := loaderNextRingFacts slot phase++F)
    hTrips hRound hTail hIn
  have hh := hU.2.2.2.2
  have parts := (holds_append u.regs (loaderNextRingFacts slot phase) F).mp hh.2.2
  have hBase' := holds_mem parts.2 hBase
  have hNext : use+1 = cacheUseOfRound (round+1) := by dsimp [use,cacheUseOfRound]; omega
  refine ⟨u,(run_rtg hv).trans (run_rtg hu),hU.mono ?_⟩
  refine ⟨hh.1,hh.2.1,hBase',?_⟩
  rw [← hNext]
  have hRegs : Holds u.regs (loaderNextRingFacts (kvUseStage use) (kvEmptyPhase use)++F) :=
    hh.2.2
  rw [loaderRingWordsOfUse] at hRegs
  exact hRegs

set_option maxRecDepth 4096 in
private theorem steadyCounterWithFrame {l : Launch} {g i trips : Nat} {t : TState}
    {F : List (Nat × Value)} (hTrips : trips < 2^31) (hi : i < trips)
    (hKeep : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (ht : At t 1741 ([(7181,b32 i),(1091,b32 trips)]++F)) :
    ∃ u, run kernel Assumptions.all l g 3 t = some u ∧
      At u (if i+1 < trips then 1396 else 1744)
        ([(7181,b32 (i+1)),(1091,b32 trips)]++F) := by
  let E := (1091,b32 trips)::F
  have hFrame : ((kernel.code.drop 1741).take 2).all
      (fun ins => (E.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hTripReg : ((kernel.code.drop 1741).take 2).all
        (fun ins => !(writesRegs ins.op).contains 1091) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    exact Bool.and_eq_true_iff.mpr
      ⟨List.all_eq_true.mp hTripReg _ hm,List.all_eq_true.mp hKeep _ hm⟩
  have hIn : At t 1741 ([(7181,b32 i),(1091,b32 trips)]++E) :=
    ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,ht.2.2.2.2.2⟩
  obtain ⟨w,hw,hW⟩ := linearFramed (by decide) (by decide) hFrame
    (by set_option maxRecDepth 100000 in kernel_rfl) (steadyRingCondition l g hTrips hi) hIn
  let pick := decide (i+1 < trips)
  have hw' : At w 1743 ((230,.pred pick)::[(7181,b32 (i+1)),(1091,b32 trips)]++F) := by
    apply hW.mono
    have h := hW.2.2.2.2
    exact ⟨h.1,h.2.1,h.2.2⟩
  obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1743 pick hw' hw'.2.2.2.2.1 (by simp)
  have huAll := (loaderLinear (regs := []) (by decide) (by decide) hw'.1
    (by simp) (by decide) hu).1
  refine ⟨u,run_comp hw huAll,?_⟩
  have hPc := hU.1
  change u.pc = (if pick = true then 1396 else 1743+1) at hPc
  refine ⟨?_,hU.2.1,hU.2.2.1,hU.2.2.2.1,hU.2.2.2.2.2⟩
  simpa only [pick,decide_eq_true_eq,Nat.reduceAdd] using hPc

def steadyCacheHeadFrame (l : Launch) (round trips : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  [(7181,b32 round),(1091,b32 trips)] ++ drainCarry l (cacheUseOfRound round) ++ F

def steadyCachePublishedFrame (round trips : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  let use := cacheUseOfRound round+1
  [(1170,b32 (kvUseStage use).val),(2141,loaderPhaseWord (kvEmptyPhase use)),
    (7181,b32 round),(1091,b32 trips)] ++ F

set_option maxRecDepth 4096 in
theorem steadyCacheTailLocal {l : Launch} {g round trips : Nat} {t : TState}
    {F : List (Nat × Value)} (hTrips : trips < 2^31) (hRound : round < trips)
    (hStage : ((kernel.code.drop 1736).take 5).all
      (fun ins => ([7181,1091]++F.map Prod.fst).all
        (fun r => !(writesRegs ins.op).contains r)) = true)
    (hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => ([7179,7180]++F.map Prod.fst).all
        (fun r => !(writesRegs ins.op).contains r)) = true)
    (hBase : (2535,b32 l.sharedBase) ∈ F)
    (ht : At t 1736 (steadyCachePublishedFrame round trips F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if round+1 < trips then 1396 else 1744)
        (steadyCacheHeadFrame l (round+1) trips F) := by
  let use := cacheUseOfRound round+1
  let slot := kvUseStage use
  let phase := kvEmptyPhase use
  let E := [(7181,b32 round),(1091,b32 trips)]++F
  have hKeep : ((kernel.code.drop 1736).take 5).all
      (fun ins => (E.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := hStage
  obtain ⟨v,hv,hV⟩ := linearFramed (by decide) (by decide) hKeep
    (by set_option maxRecDepth 100000 in kernel_rfl) (steadyRingStage l g slot phase) ht
  have hIn : At v 1741
      ([(7181,b32 round),(1091,b32 trips)]++loaderNextRingFacts slot phase++F) := by
    apply hV.mono
    have h := (holds_append ..).mp hV.2.2.2.2
    exact ⟨h.2.1,h.2.2.1,(holds_append ..).mpr ⟨h.1,h.2.2.2⟩⟩
  obtain ⟨u,hu,hU⟩ := steadyCounterWithFrame (F := loaderNextRingFacts slot phase++F)
    hTrips hRound hTail hIn
  have hh := hU.2.2.2.2
  have parts := (holds_append u.regs (loaderNextRingFacts slot phase) F).mp hh.2.2
  have hBase' := holds_mem parts.2 hBase
  have hNext : use+1 = cacheUseOfRound (round+1) := by dsimp [use,cacheUseOfRound]; omega
  refine ⟨u,(run_rtg hv).trans (run_rtg hu),hU.mono ?_⟩
  refine ⟨hh.1,hh.2.1,hBase',?_⟩
  rw [← hNext]
  have hRegs : Holds u.regs (loaderNextRingFacts (kvUseStage use) (kvEmptyPhase use)++F) :=
    hh.2.2
  rw [loaderRingWordsOfUse] at hRegs
  exact hRegs

/-- At the steady head, the warp agrees on the next physical ring use and remaining trips. -/
abbrev SteadyCacheHead (l : Launch) (X : Execution) (g round trips : Nat)
    (F : Nat → List (Nat × Value)) (shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 1396 (fun lane => steadyCacheHeadFrame l round trips (F lane))
    shuffles votes ends

/-- Both packets of this steady iteration have been published at the recorded checkpoint. -/
abbrev SteadyCachePublished (l : Launch) (X : Execution) (g round trips : Nat)
    (F : Nat → List (Nat × Value)) (shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 1736 (fun lane => steadyCachePublishedFrame round trips (F lane))
    shuffles votes ends

/-- The steady cutoff carries the next ring use into the actual terminal drain. -/
abbrev SteadyCacheDone (l : Launch) (X : Execution) (g trips : Nat)
    (F : Nat → List (Nat × Value)) (shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 1744 (fun lane => steadyCacheHeadFrame l (trips) trips (F lane))
    shuffles votes ends

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
