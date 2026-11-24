-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailValueProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpPollProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.MmaValueDescriptorWord
import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerElectProgress
import Kernels.TmlFa4Fwd.Proof.MmaQkBroadcast
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.TcIssueProgress
public import Kernels.TmlFa4Fwd.Proof.MmaPvEntry
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part040

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Epilogue Prologue

/-- The actual single-visit warp checkpoint at the first joint probability acquire. -/
abbrev OpeningTailProbabilityReached (l : Launch) (X : Execution)
    (g shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 2548 (fun _ => tailValueWaitFrame l) shuffles votes ends

/-- A ready opening V packet carries every MMA lane to the next joint-probability wait. -/
theorem openingTailProbabilityReachedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : OpeningTailValueReached l X g shuffles votes ends)
    (hReady : let log := X.objects (Thread.Mma.Observation.readyObject l g 1)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    ∃ next : OpeningTailProbabilityReached l X g shuffles votes ends,
      ∀ lane < 32,
        Thread.Mma.ReadyPoll l X (warpLane l g lane) (next.pos lane-1) 1 0 true .cta := by
  have hWidth : l.sharedBase+40 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+40)%8 = 0 := by have := hp.shared.1; omega
  obtain ⟨s,hs,hPhase⟩ := hReady
  obtain ⟨next,hGet⟩ := mmaWarpPollOfMaximal (phase := 0) hp hMax hg 9 hWidth hAlign (by decide) cur
    (fun _ _ => ⟨by simp [tailValueWaitFrame,tailValueCommitFrame,waitSite],
      List.mem_cons_self,by simp [tailValueWaitFrame,tailValueCommitFrame,waitSite]⟩)
    (fun _ _ => by intro _ _ _ _ _; exact ⟨s,hs,by rw [hPhase]; decide⟩)
  refine ⟨next,fun lane hl => ⟨_,(hGet lane hl).2,?_⟩⟩
  have hCta : warpLane l g lane / l.block = g/l.block :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.2.symm
  rw [Thread.Mma.Observation.readyObject,hCta]
  rfl

/-- In the lane's actual one-visit route, any recorded score notification is opening. -/
theorem scoreOrdinalZeroOfSingleVisitOpening {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j shuffles votes cta : Nat} {ends : Nat → Option TState}
    (cur : OpeningKeyReturnedWithTrip l X g 1 shuffles votes ends)
    {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hScore : Thread.Scores.ScoreCommit l X (g,j) cta stage spec rank) :
    Thread.Scores.scoreCommitOrdinal l X cta stage (g,j) = 0 := by
  by_contra hPositive
  obtain ⟨bank,_,hBank,he⟩ :=
    Thread.Scores.positiveScoreCommitRepeats hp hX hScore (Nat.pos_of_ne_zero hPositive)
  have hg := event_thread_lt hX he
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hRegion : 2285 ≤ (commitSite (qkCommitSite bank)).pc ∧
      (commitSite (qkCommitSite bank)).pc < 2534 := by
    revert hBank
    fin_cases bank <;> decide
  exact noSteadyEventOfSingleVisitOpening hp hLane cur
    (by rw [hSelf]; exact he) hRegion.1 hRegion.2

/-- Both the initial V and the stage-zero main probability packet have been acquired. -/
abbrev OpeningTailMainReturned (l : Launch) (X : Execution)
    (g shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 2551 (fun _ => tailValueWaitFrame l) shuffles votes ends

/-- The first joint probability phase enables every lane's main probability acquire. -/
theorem openingTailMainReturnedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : OpeningTailProbabilityReached l X g shuffles votes ends)
    (hReady : let log := X.objects (Thread.Scores.probabilityObject l (g/l.block) 0 0)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    Nonempty (OpeningTailMainReturned l X g shuffles votes ends) := by
  have hWidth : l.sharedBase+96 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+96)%8 = 0 := by have := hp.shared.1; omega
  obtain ⟨s,hs,hPhase⟩ := hReady
  obtain ⟨next,_⟩ := mmaWarpPollOfMaximal (phase := 0) hp hMax hg 10 hWidth hAlign
    (by decide) cur
    (fun _ _ => by simp [tailValueWaitFrame,tailValueCommitFrame,waitSite])
    (fun _ _ => by intro _ _ _ _ _; exact ⟨s,hs,by rw [hPhase]; decide⟩)
  exact ⟨next⟩

private def firstTailDescriptors (l : Launch) : List (Nat × Value) :=
  [(2626,b32 64),(2625,b32 (valueDescriptorLow l 1))] ++ tailValueWaitFrame l

private theorem firstTailDescriptorSetup {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (g : Nat) {t : TState}
    (ht : At t 2551 (tailValueWaitFrame l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2558 (firstTailDescriptors l) := by
  have ht' : At t 2551 [(7207,b32 (kvSlot 1)),(2535,b32 l.sharedBase)] :=
    ht.mono ⟨holds_mem ht.2.2.2.2 (by simp [tailValueWaitFrame,tailValueCommitFrame,kvSlot]),
      holds_mem ht.2.2.2.2 (by simp [tailValueWaitFrame,tailValueCommitFrame]),trivial⟩
  obtain ⟨u,hr,hu⟩ := valueDescriptorLocalWithProbabilityFrame hp g false 1 none t ht'
  have hAll : run kernel Assumptions.all l g 7 t = some u :=
    localRun (by decide) (by decide) ht.1
      (by set_option maxRecDepth 100000 in kernel_rfl) hr
  refine ⟨u,run_rtg hAll,hu.mono
    ⟨hu.2.2.2.2.1,hu.2.2.2.2.2.1,?_⟩⟩
  apply holdsSchedulerFrame (regs := (tailValueWaitFrame l).map Prod.fst) ht.2.2.2.2
  · intro r h
    apply schedulerLocalFrame (lo := 2551) (len := 7) (by
      simp only [tailValueWaitFrame,tailValueCommitFrame,List.cons_append,List.nil_append,List.map]
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hr
      (by rw [ht.1]) (by rw [ht.1]) h
  · exact fun _ => List.mem_map_of_mem

/-- The first tail PV block's actual descriptor and two Tensor Memory columns are ready
at its election. The next three shuffle ordinals belong to these broadcasts. -/
abbrev OpeningTailFirstPvElection (l : Launch) (X : Execution)
    (g shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 2562
    (fun _ => pvEntryFacts l 2 1 0 false ++ tailValueWaitFrame l) shuffles votes ends

/-- All three actual lane-zero broadcasts prepare the probability, value and output descriptors. -/
theorem firstTailPvElectionOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : OpeningTailMainReturned l X g shuffles votes ends) :
    Nonempty (OpeningTailFirstPvElection l X g (shuffles+3) votes ends) := by
  obtain ⟨s⟩ := cur.advanceLocal
    (fun lane hl => firstTailDescriptorSetup hp _ (cur.checkpoint lane hl))
  obtain ⟨q⟩ := s.consumeShuffle (dst := 2611) hp hMax hg .idx (fun _ => b32 64)
    (fun _ => 0) (fun _ => 31) (by
      simp [firstTailDescriptors,tailValueWaitFrame,tailValueCommitFrame]) (by
        intro lane hl
        have h := s.checkpoint lane hl
        exact valueProbabilityShuffle hp false (h.mono ⟨h.2.2.2.2.1,trivial⟩))
  obtain ⟨v⟩ := q.consumeShuffle (dst := 2612) hp hMax hg .idx
    (fun _ => b32 (valueDescriptorLow l 1)) (fun _ => 0) (fun _ => 31) (by
      simp [firstTailDescriptors,tailValueWaitFrame,tailValueCommitFrame]) (by
        intro lane hl
        have h := q.checkpoint lane hl
        exact valueDescriptorShuffle hp false 1 (h.mono ⟨h.2.2.2.2.2.2.1,trivial⟩))
  let F := (2627,b32 256) :: (2612,b32 (valueDescriptorLow l 1)) :: (2611,b32 64) ::
    firstTailDescriptors l
  obtain ⟨u⟩ := v.advanceLocal (pc' := 2561) (G := fun _ => F) (by
    intro lane hl
    have hAt := v.checkpoint lane hl
    let u := next (setReg (v.state lane) 2627 (b32 256))
    have hCore : run kernel [] l (warpLane l g lane) 1 (v.state lane) = some u := by
      apply run_local Flow.code_2560 rfl hAt
      rfl
    have hRun := localRun (by decide) (by decide) hAt.1 (by decide) hCore
    exact ⟨u,run_rtg hRun,hAt.set (by
      simp [firstTailDescriptors,tailValueWaitFrame,tailValueCommitFrame])⟩)
  obtain ⟨w⟩ := u.consumeShuffle (dst := 2613) hp hMax hg .idx
    (fun _ => b32 256) (fun _ => 0) (fun _ => 31) (by
      simp [F,firstTailDescriptors,tailValueWaitFrame,tailValueCommitFrame]) (by
        intro lane hl
        have ht := u.checkpoint lane hl
        have h : (u.state lane).regs 2627 = some (b32 256) := ht.2.2.2.2.1
        rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
          out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_2561) rfl rfl]
        change Out.ev (shflTmpl l (warpLane l g lane) (u.state lane) .idx 2613 none
          (.reg 2627) (.imm 0) (.imm 31) (.imm (-1))) = _
        have hBlock : l.block%32 = 0 := by rw [hp.block]
        simp [shflTmpl,readValue,readReg,h,hBlock,Value.bytes,b32,readBits,pure,Except.pure]
        rfl)
  apply w.advanceLocal
  intro lane hl
  have ht := w.checkpoint lane hl
  refine ⟨w.state lane,.refl,ht.mono ?_⟩
  unfold pvEntryFacts
  exact ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,
    holds_mem ht.2.2.2.2 (by simp [F,firstTailDescriptors,tailValueWaitFrame,tailValueCommitFrame]),
    holds_mem ht.2.2.2.2 (by
      change (2614,b32 (l.sharedBase+112)) ∈ _
      simp [F,firstTailDescriptors,tailValueWaitFrame,tailValueCommitFrame]),
    holds_mem ht.2.2.2.2 (by
      change (7205,b32 0) ∈ _
      simp [F,firstTailDescriptors,tailValueWaitFrame,tailValueCommitFrame]),
    ht.2.2.2.2.2.2.2.2.2.2⟩

/-- The first tail PV block uses a full-warp elect with a fresh event ordinal. -/
theorem firstTailPvElectedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : OpeningTailFirstPvElection l X g shuffles votes ends) :
    ∃ leader : Fin 32, ∃ next : SchedulerWarpReached l X g 2563
      (fun lane => (9727,.pred (laneOf l (warpLane l g lane) == leader.val)) ::
        (pvEntryFacts l 2 1 0 false ++ tailValueWaitFrame l)) shuffles votes ends,
      ∀ lane < 32, next.pos lane = cur.pos lane+1 ∧
        ∃ inst, X.Elect (warpLane l g lane,cur.pos lane) 2562 4294967295 inst leader := by
  let F := pvEntryFacts l 2 1 0 false ++ tailValueWaitFrame l
  have hPred : ∀ pair ∈ F, pair.1 ≠ 9727 := by
    intro pair hm he
    have hReg := List.mem_map_of_mem (f := Prod.fst) hm
    rw [he] at hReg
    exact (of_decide_eq_true rfl : 9727 ∉ F.map Prod.fst) hReg
  exact cur.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (cur.state lane) 15)
    (fun lane leader => (9727,.pred (laneOf l (warpLane l g lane) == leader)) :: F)
    (fun lane hl _ hj _ _ _ he =>
      noEarlierMmaElection 15 Flow.code_2562
        (by set_option maxRecDepth 100000 in kernel_rfl) (by kernel_rfl)
        (cur.checkpoint lane hl) (cur.recorded lane hl) (cur.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 15 (cur.checkpoint lane hl))
    (fun lane hl leader => electStateFrame 15 (cur.checkpoint lane hl) leader hPred
      (by simp [electSite]))

/-- The elected leader and real returning lane cursors of the first tail PV block. -/
structure OpeningTailFirstPvElected (l : Launch) (X : Execution)
    (g shuffles votes : Nat) (ends : Nat → Option TState) where
  leader : Fin 32
  cursor : SchedulerWarpReached l X g 2563
    (fun lane => (9727,.pred (laneOf l (warpLane l g lane) == leader.val)) ::
      (pvEntryFacts l 2 1 0 false ++ tailValueWaitFrame l)) shuffles votes ends
  elected : ∀ lane < 32, ∃ inst,
    X.Elect (warpLane l g lane,cursor.pos lane-1) 2562 4294967295 inst leader

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

theorem firstTailPvLeaderOfMaximal {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState} (cur : OpeningTailMainReturned l X g shuffles votes ends) :
    Nonempty (OpeningTailFirstPvElected l X g (shuffles+3) votes ends) := by
  obtain ⟨ready⟩ := firstTailPvElectionOfMaximal hp hMax hg cur
  obtain ⟨leader,next,hElect⟩ := firstTailPvElectedOfMaximal hp hMax hg ready
  refine ⟨⟨leader,next,fun lane hl => ?_⟩⟩
  obtain ⟨hPos,he⟩ := hElect lane hl
  rw [hPos,Nat.add_sub_cancel]
  exact he

end PTX.Kernels.TmlFa4Fwd.Mma
