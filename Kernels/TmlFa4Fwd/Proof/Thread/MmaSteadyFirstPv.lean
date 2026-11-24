-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyOpeningPolls
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyRoots
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaWarpPvPacket
import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerElectProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Proof.MmaValueDescriptorWord
import Kernels.TmlFa4Fwd.Proof.MmaQkBroadcast
import Kernels.TmlFa4Fwd.Flow.Code.Part036
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread (actualFullElectionMask electionCountAtMatchedShuffle)

noncomputable section

private def steadyPvDescriptors (l : Launch) (visit remaining : Nat) : List (Nat × Value) :=
  (2582,b32 64)::(2581,b32 (valueDescriptorLow l (2*visit+1)))::
    steadyValueFrame l visit remaining

private theorem computeSteadyPvDescriptors {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g visit remaining : Nat} {t : TState}
    {extra : List (Nat × Value)}
    (ht : At t 2300 (steadyValueFrame l visit remaining ++ extra))
    (hExtra : ∀ pair ∈ extra, pair.1 ∈ steadyIterationRootRegs) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 2307 (steadyPvDescriptors l visit remaining ++ extra) := by
  let use := 2*visit+1
  have hSplit := (holds_append ..).mp ht.2.2.2.2
  have ht' : At t 2300 [(7207,b32 (kvSlot use)),(2535,b32 l.sharedBase)] :=
    ht.mono ⟨holds_lookup hSplit.1 rfl,holds_lookup hSplit.1 rfl,trivial⟩
  obtain ⟨u,hu,hU⟩ := (valueDescriptorLocalWithProbabilityFrame hp g true use none).apply ht'
  obtain ⟨hPath,hF⟩ := activeDrainLocalKeep (ht.mono hSplit.1) (by decide) (by decide) (by
    change ((kernel.code.drop 2300).take 7).all
      (fun ins => [2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,2615,2618,1190].all
        fun r => !(writesRegs ins.op).contains r) = true
    decide +kernel) (by decide +kernel) hu
  obtain ⟨_,hCarry⟩ := activeDrainLocalKeep (ht.mono hSplit.2) (by decide) (by decide)
    (knownRegisterFrameAudit hExtra (by decide +kernel)) (by decide +kernel) hu
  exact ⟨u,hPath,hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.1,
    (holds_append ..).mpr ⟨hF,hCarry⟩⟩⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g visit remaining shuffles votes : Nat}
    (hg : g < l.threads) {ends : Nat → Option TState} {extra : List (Nat × Value)}
    (cur : SchedulerWarpReached l X g 2300
      (fun _ => steadyValueFrame l visit remaining ++ extra) shuffles votes ends)
    (hExtra : ∀ pair ∈ extra, pair.1 ∈ steadyIterationRootRegs)
include hp hMax hg cur hExtra

private theorem steadyFirstPvElectionWithPolls :
    ∃ leader : Fin 32, ∃ elected : SchedulerWarpReached l X g 2312
      (fun lane => pvElectedFrame l g 0 (2*visit+1) (visit%2) (decide (0<visit))
        (((2595,b32 (valueDescriptorLow l (2*visit+1)))::steadyValueFrame l visit remaining) ++
          extra) lane leader) (shuffles+3) votes ends,
      ∀ lane < 32, cur.pos lane ≤ elected.pos lane ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (elected.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) := by
  let use := 2*visit+1
  let vl := valueDescriptorLow l use
  let D := steadyPvDescriptors l visit remaining
  let F := steadyValueFrame l visit remaining
  have hFreshIn (r : Nat) {base : List (Nat × Value)}
      (hBase : ∀ pair ∈ base, pair.1 ≠ r) (hRoot : r ∉ steadyIterationRootRegs) :
      ∀ pair ∈ base ++ extra, pair.1 ≠ r := by
    intro pair hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hBase pair hm
    · exact fun he => hRoot (he ▸ hExtra pair hm)
  have hBegin : ∃ beginning : SchedulerWarpReached l X g 2307
      (fun _ => D ++ extra) shuffles votes ends, beginning.pos = cur.pos := by
    apply cur.advanceLocalWithPosition
    intro lane hl
    exact computeSteadyPvDescriptors hp (g := warpLane l g lane) (cur.checkpoint lane hl) hExtra
  obtain ⟨beginning,hBeginPos⟩ := hBegin
  obtain ⟨q,hQ⟩ := beginning.consumeShuffleWithEvents (dst := 2569) hp hMax hg .idx
    (fun _ => b32 64) (fun _ => 0) (fun _ => 31)
    (fun _ _ => hFreshIn 2569 (base := D)
      (by simp [D,steadyPvDescriptors,steadyValueFrame,steadyFrame,steadyPorts]) (by decide))
    (fun lane hl => by
      have h := beginning.checkpoint lane hl
      exact valueProbabilityShuffle hp true (h.mono ⟨h.2.2.2.2.1,trivial⟩))
  obtain ⟨v,hV⟩ := q.consumeShuffleWithEvents (dst := 2595) hp hMax hg .idx
    (fun _ => b32 vl) (fun _ => 0) (fun _ => 31)
    (fun _ _ => hFreshIn 2595 (base := (2569,b32 64)::D)
      (by simp [D,steadyPvDescriptors,steadyValueFrame,steadyFrame,steadyPorts]) (by decide))
    (fun lane hl => by
      have h := q.checkpoint lane hl
      exact valueDescriptorShuffle hp true use (h.mono ⟨h.2.2.2.2.2.2.1,trivial⟩))
  let S := (2583,b32 256)::(2595,b32 vl)::(2569,b32 64)::D
  obtain ⟨u,hU⟩ := v.advanceLocalWithPosition (pc' := 2310) (G := fun _ => S ++ extra) (by
    intro lane hl
    have h := v.checkpoint lane hl
    let after := next (setReg (v.state lane) 2583 (b32 256))
    have hRun : run kernel [] l (warpLane l g lane) 1 (v.state lane) = some after := by
      apply run_local Flow.code_2309 rfl h
      rfl
    exact ⟨after,run_rtg (localRun (by decide) (by decide) h.1 rfl hRun),
      h.set (hFreshIn 2583 (base := (2595,b32 vl)::(2569,b32 64)::D)
        (by simp [D,steadyPvDescriptors,steadyValueFrame,steadyFrame,steadyPorts]) (by decide))⟩)
  obtain ⟨a,ha⟩ := u.consumeShuffleWithEvents (dst := 2570) hp hMax hg .idx
    (fun _ => b32 256) (fun _ => 0) (fun _ => 31)
    (fun _ _ => hFreshIn 2570 (base := S)
      (by simp [S,D,steadyPvDescriptors,steadyValueFrame,steadyFrame,steadyPorts]) (by decide))
    (fun lane hl => by
      have h := u.checkpoint lane hl
      exact laneZeroBroadcast hp (by decide) (h.mono ⟨h.2.2.2.2.1,trivial⟩) Flow.code_2310)
  have hb : l.block%32 = 0 := by rw [hp.block]
  let n := elections X (warpLane l g 0) (u.pos 0)
  have hCut (lane : Nat) (hl : lane < 32) :
      elections X (warpLane l g lane) (a.pos lane) = n := by
    obtain ⟨hPos,_,_,he,hk⟩ := ha lane hl
    obtain ⟨_,_,_,he',hk'⟩ := ha 0 (by decide)
    have hw := Step.sameWarp_trans (sameWarp_symm (Step.sameWarp_lane hb hg hl).1)
      (Step.sameWarp_lane hb hg (show 0<32 by decide)).1
    have hEq := electionCountAtMatchedShuffle hMax.1 hw he hk he' hk'
    unfold elections
    rw [hPos,countP_take_succ_false he rfl]
    exact hEq
  let E := (2570,b32 256)::S
  have hFresh : ∀ pair ∈ E ++ extra, pair.1 ≠ 9671 :=
    hFreshIn _ (by simp [E,S,D,steadyPvDescriptors,steadyValueFrame,steadyFrame,steadyPorts])
      (by decide)
  have hOrd : ElectOrdinal l X := electOrdinal hMax.1
    (ElectMutual.of_full (fun e => actualFullElectionMask hMax.1 e))
  obtain ⟨lead,after,hElect⟩ := a.consumeElectionAtOrdinal hp hMax hg
    (fun lane => electState l (warpLane l g lane) (a.state lane) 5)
    (fun lane lead => (9671,.pred (laneOf l (warpLane l g lane) == lead))::E ++ extra)
    hOrd n hCut (fun lane hl => electTemplate 5 (a.checkpoint lane hl))
    (fun lane hl lead => electStateFrame 5 (a.checkpoint lane hl) lead hFresh (by simp [electSite]))
  have hFrame : ∃ elected : SchedulerWarpReached l X g 2312
      (fun lane => pvElectedFrame l g 0 (2*visit+1) (visit%2) (decide (0<visit))
        ((2595,b32 vl)::F ++ extra) lane lead) (shuffles+3) votes ends,
      elected.pos = after.pos := by
    apply after.advanceLocalWithPosition
    intro lane hl
    have ht := after.checkpoint lane hl
    have H := ht.2.2.2.2
    refine ⟨_,.refl,ht.mono ⟨H.1,(holds_append _ _ _).mpr ⟨?_,?_⟩⟩⟩
    · have hAcc : (if decide (0<visit) = true then 1 else 0) =
          (if 0<visit then 1 else 0) := by simp
      change Holds (after.state lane).regs
        [(2570,b32 256),(2569,b32 64),(2595,b32 vl),
          (7206,b32 (if decide (0<visit) = true then 1 else 0)),
          (2614,b32 (l.sharedBase+112)),(7205,b32 (visit%2))]
      rw [hAcc]
      exact ⟨holds_lookup H rfl,holds_lookup H rfl,holds_lookup H rfl,holds_lookup H rfl,
        holds_lookup H rfl,holds_lookup H rfl,trivial⟩
    · exact ⟨holds_lookup H rfl,H.2.2.2.2.2.2.2⟩

  obtain ⟨elected,hElected⟩ := hFrame
  refine ⟨lead,elected,?_⟩
  intro lane hl
  obtain ⟨hPosQ,_,_,heQ,_⟩ := hQ lane hl
  obtain ⟨hPosV,_,_,heV,_⟩ := hV lane hl
  obtain ⟨hPosA,_,_,heA,_⟩ := ha lane hl
  obtain ⟨hPosE,_,heE⟩ := hElect lane hl
  refine ⟨by rw [hElected,hPosE,hPosA,hU,hPosV,hPosQ,hBeginPos]; omega,?_⟩
  intro other
  unfold okPolls
  rw [hElected,hPosE,countP_take_succ_false heE rfl,
    hPosA,countP_take_succ_false heA rfl,hU,hPosV,countP_take_succ_false heV rfl,
    hPosQ,countP_take_succ_false heQ rfl,hBeginPos]

/-- The actual first steady PV packet issues under the recurring value and probability acquires. -/
theorem steadyFirstPvPacketWithPollCounts
    (hTail : ∀ lane < 32, PvTailReadyWithOrdinal l X (warpLane l g lane) 0 (visit%2)
      (((2595,b32 (valueDescriptorLow l (2*visit+1)))::steadyValueFrame l visit remaining) ++
        extra) (cur.pos lane)) :
    ∃ newEnds, ∃ next : SchedulerWarpReached l X g 2344
      (fun _ => ((2595,b32 (valueDescriptorLow l (2*visit+1)))::
        steadyValueFrame l visit remaining) ++
        extra) (shuffles+3) votes newEnds,
      PvPacketIssues l X g 0 (2*visit+1) (decide (0<visit)) ∧
      ∀ lane < 32, cur.pos lane ≤ next.pos lane ∧
        PvPollDelta X (warpLane l g lane) (cur.pos lane) (next.pos lane)
          (Thread.Scores.probabilityObject l (g/l.block) 0 1) true := by
  obtain ⟨lead,elected,hElect⟩ := steadyFirstPvElectionWithPolls hp hMax hg cur hExtra
  let E := ((2595,b32 (valueDescriptorLow l (2*visit+1)))::steadyValueFrame l visit remaining) ++
    extra
  have hFresh : ∀ pair ∈ E,
      pair.1 ≠ (pvSite 0).b-2 ∧ pair.1 ≠ (pvSite 0).b ∧
        pair.1 ≠ (waitSite (pvTailWait 0)).result := by
    intro pair hm
    rcases List.mem_append.mp hm with hm | hm
    · simp [steadyValueFrame,steadyFrame,steadyPorts] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> simp [pvSite,pvTailWait,waitSite]
    · have hx : ∀ r ∈ steadyIterationRootRegs,
          r ≠ (pvSite 0).b-2 ∧ r ≠ (pvSite 0).b ∧ r ≠ (waitSite (pvTailWait 0)).result := by
        decide
      exact hx _ (hExtra pair hm)
  have hSetup : ((kernel.code.drop 2312).take 7).all
      (fun ins => (E.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    have hAll : ((kernel.code.drop 2312).take 7).all
        (fun ins => ([2595,2568,1191,7207,7208,7205,7206,7204,2535,2610,2614,2615,2618,1190] ++
          steadyIterationRootRegs).all (fun r => !(writesRegs ins.op).contains r)) = true := by
      decide +kernel
    apply knownRegisterFrameAudit (F := E) _ hAll
    intro pair hm
    rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append_left _ (List.mem_map_of_mem (f := Prod.fst) hm)
    · exact List.mem_append_right _ (hExtra pair hm)
  obtain ⟨ends,next,hIssue,hP⟩ := pvWarpPacketWithPollCounts hp hMax hg 0
    (2*visit+1) (visit%2) (decide (0<visit)) (Nat.mod_lt _ (by decide)) lead
    hFresh hSetup elected (fun lane hl => by
      unfold PvTailReadyWithOrdinal
      dsimp only
      rw [(hElect lane hl).2]
      exact hTail lane hl)
  refine ⟨ends,next,hIssue,?_⟩
  intro lane hl
  have hCta : (warpLane l g lane)/l.block = g/l.block :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.2.symm
  have hDelta := (hP lane hl).2.2
  rw [hCta] at hDelta
  refine ⟨(hElect lane hl).1.trans (hP lane hl).2.1,?_⟩
  intro other
  exact (hDelta other).trans
    (congrArg (· + if true = true ∧ other = _ then 1 else 0) ((hElect lane hl).2 other))

end

end
end PTX.Kernels.TmlFa4Fwd.Mma
