-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCohortPolls
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyIteration
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyFirstPv
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyOpeningPolls

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : Protocol.Scores.CorrectionJointGuards l X) {g visit remaining shuffles votes : Nat}
    (hg : g < l.threads) (hWarp : warpIndex l g = 12) {ends : Nat → Option TState}
    (cur : SteadyIterationCursor l X g visit remaining shuffles votes ends)
    (hDelivered : Protocol.LoaderReady.DeliveredCohort l X g
      (readyStage (2*visit+1)) ((2*visit+1)/3))
include hp hMax hGuard hg hWarp cur hDelivered

/-- The opening cut of a specified recurring visit consumes its delivered V and
first main-P packets, advancing the local generations of precisely those two
objects and preserving the remaining poll and collective ordinals. -/
theorem steadyVisitOpeningOfCohorts
    (hCohort : Protocol.Scores.ProbabilityCohort l X (g/l.block) 0 0 visit)
    (hValue : ∀ lane < 32, okPolls ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩
      ((X.tr (warpLane l g lane)).take (cur.pos lane)) = (2*visit+1)/3)
    (hProbability : ∀ lane < 32, okPolls (Thread.Scores.probabilityObject l (g/l.block) 0 0)
      ((X.tr (warpLane l g lane)).take (cur.pos lane)) = visit) :
    ∃ next : SchedulerWarpReached l X g 2300
      (fun _ => steadyValueFrame l visit remaining ++ steadyIterationRoots l) shuffles votes ends,
      ∀ lane < 32, cur.pos lane < next.pos lane ∧
        (∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) +
            (if other = ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ then 1 else 0) +
            (if other = Thread.Scores.probabilityObject l (g/l.block) 0 0 then 1 else 0)) ∧
        elections X (warpLane l g lane) (next.pos lane) =
          elections X (warpLane l g lane) (cur.pos lane) := by
  obtain ⟨poll,hPos⟩ := steadyValueWaitReachedFramedWithPosition hp cur (by
    rw [steadyIterationRoots_regs]
    decide +kernel)
  have hValInputs : ∀ lane < 32,
      let F := steadyValueFrame l visit remaining ++ steadyIterationRoots l
      (∀ pair ∈ F, pair.1 ≠ (waitSite 3).result) ∧
      ((waitSite 3).base,b32 (readyAddr l (2*visit+1))) ∈ F ∧
      ((waitSite 3).phase,b32 (readyWord (2*visit+1))) ∈ F := by
    intro _ _
    refine ⟨?_,?_,?_⟩
    · intro pair hm
      rcases List.mem_append.mp hm with hm | hm
      · simp [steadyValueFrame,steadyFrame,steadyPorts,waitSite] at hm ⊢
        aesop
      · exact fun h => (by decide : (waitSite 3).result ∉ steadyIterationRootRegs)
          (h ▸ steadyIterationRoots_valid l pair hm)
    · simp [steadyValueFrame,waitSite]
    · simp [steadyValueFrame,steadyFrame,waitSite]
  obtain ⟨value,hVal⟩ := mmaWarpCachePollOfDelivered hp hMax hg hWarp 3 poll hValInputs
    (by rw [hPos]; exact hValue) hDelivered
  have hMainInputs : ∀ lane < 32,
      let F := steadyValueFrame l visit remaining ++ steadyIterationRoots l
      (∀ pair ∈ F, pair.1 ≠ (waitSite 4).result) ∧
      ((waitSite 4).base,b32 (l.sharedBase+96)) ∈ F ∧
      ((waitSite 4).phase,b32 (visit%2)) ∈ F := by
    intro _ _
    refine ⟨?_,?_,?_⟩
    · intro pair hm
      rcases List.mem_append.mp hm with hm | hm
      · simp [steadyValueFrame,steadyFrame,steadyPorts,waitSite] at hm ⊢
        aesop
      · exact fun h => (by decide : (waitSite 4).result ∉ steadyIterationRootRegs)
          (h ▸ steadyIterationRoots_valid l pair hm)
    · simp [steadyValueFrame,steadyFrame,steadyPorts,waitSite]
    · simp [steadyValueFrame,steadyFrame,waitSite]
  have hSeparated : Thread.Scores.probabilityObject l (g/l.block) 0 0 ≠
      ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ := by
    intro h
    have hs := (readyStage (2*visit+1)).isLt
    have he := congrArg Loc.addr h
    change l.sharedBase+96 = l.sharedBase+(8*(readyStage (2*visit+1)).val+32) at he
    omega
  obtain ⟨next,hMain⟩ := mmaWarpProbabilityPollOfCohort hp hMax hGuard hg hWarp 4 0 0
    value hMainInputs (fun lane hl => by
      rw [(hVal lane hl).2.2.1,ite_eq_right hSeparated,Nat.add_zero,hPos]
      exact hProbability lane hl) hCohort
  refine ⟨next,?_⟩
  intro lane hl
  have hV := hVal lane hl
  have hP := hMain lane hl
  exact ⟨(hPos ▸ hV.1).trans hP.1,fun other => by
    rw [hP.2.2.1,hV.2.2.1,hPos]
    rfl,
    by rw [hP.2.2.2,hV.2.2.2,hPos]⟩

/-- The first PV packet of any recurring visit consumes the delivered V and
stage-zero P pair, issues all its fragments, and reaches the next K prepare cut. -/
theorem steadyVisitFirstProductOfCohorts
    (hCohorts : ∀ packet : Fin 2, Protocol.Scores.ProbabilityCohort l X (g/l.block) 0 packet visit)
    (hValue : ∀ lane < 32, okPolls ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩
      ((X.tr (warpLane l g lane)).take (cur.pos lane)) = (2*visit+1)/3)
    (hProbability : ∀ packet : Fin 2, ∀ lane < 32,
      okPolls (Thread.Scores.probabilityObject l (g/l.block) 0 packet)
        ((X.tr (warpLane l g lane)).take (cur.pos lane)) = visit) :
    ∃ newEnds,
    ∃ next : SchedulerWarpReached l X g 2344
      (fun _ => ((2595,b32 (valueDescriptorLow l (2*visit+1)))::steadyValueFrame l visit remaining)
        ++ steadyIterationRoots l) (shuffles+3) votes newEnds,
      PvPacketIssues l X g 0 (2*visit+1) (decide (0<visit)) ∧
      ∀ lane < 32, cur.pos lane < next.pos lane ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane)) +
            (if other = ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ then 1 else 0) +
            (if other = Thread.Scores.probabilityObject l (g/l.block) 0 0 then 1 else 0) +
            (if other = Thread.Scores.probabilityObject l (g/l.block) 0 1 then 1 else 0) := by
  obtain ⟨start,hStart⟩ := steadyVisitOpeningOfCohorts hp hMax hGuard hg hWarp cur
    hDelivered (hCohorts 0) hValue (hProbability 0)
  let main := Thread.Scores.probabilityObject l (g/l.block) 0 0
  let tail := Thread.Scores.probabilityObject l (g/l.block) 0 1
  let value : Loc := ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩
  have hDifferent : tail ≠ main := by
    intro he
    have ha := congrArg Loc.addr he
    change l.sharedBase+112 = l.sharedBase+96 at ha
    omega
  have hAddr : tail ≠ value := by
    intro he
    have hs := (readyStage (2*visit+1)).isLt
    have ha := congrArg Loc.addr he
    change l.sharedBase+112 = l.sharedBase+(8*(readyStage (2*visit+1)).val+32) at ha
    omega
  obtain ⟨newEnds,next,hIssues,hFinish⟩ := steadyFirstPvPacketWithPollCounts hp hMax hg start
    (steadyIterationRoots_valid l) (fun lane hl => .inr (by
      have hPeer := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
      have hCta : (warpLane l g lane)/l.block = g/l.block := hPeer.1.2.2.symm
      have hRole : warpIndex l (warpLane l g lane) = 12 := hPeer.2.symm.trans hWarp
      change okPolls (Thread.Scores.probabilityObject l ((warpLane l g lane)/l.block) 0 1)
          (X.tr (warpLane l g lane)) =
        okPolls (Thread.Scores.probabilityObject l ((warpLane l g lane)/l.block) 0 1)
          ((X.tr (warpLane l g lane)).take (start.pos lane)) → _
      rw [hCta]
      change okPolls tail _ = okPolls tail _ → _
      rw [(hStart lane hl).2.1 tail,ite_eq_right hAddr,ite_eq_right hDifferent,Nat.add_zero,
        hProbability 1 lane hl]
      intro hTotal
      have hReady := Protocol.Scores.probabilityReadyOfUnconsumedCohort hp hMax.1 hGuard
        (g := warpLane l g lane) (gen := visit)
        hPeer.1.2.1 hRole 0 1 (by rw [hCta]; exact hCohorts 1) (by rwa [hCta])
      rw [hCta] at hReady
      exact hReady))
  refine ⟨newEnds,next,hIssues,?_⟩
  intro lane hl
  refine ⟨(hStart lane hl).1.trans_le (hFinish lane hl).1,?_⟩
  intro other
  rw [(hFinish lane hl).2 other,(hStart lane hl).2.1 other]
  simp

end
end PTX.Kernels.TmlFa4Fwd.Mma
