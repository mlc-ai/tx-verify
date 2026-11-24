-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyQkSetup
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
import Kernels.TmlFa4Fwd.Proof.MmaQkCommit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem holdsList {regs : Nat → Option Value} {facts : List (Nat × Value)}
    (h : ∀ pair ∈ facts, regs pair.1 = some pair.2) : Holds regs facts := by
  induction facts with
  | nil => trivial
  | cons pair rest ih =>
    exact ⟨h pair (by simp),ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

private def recurringIssueWords (l : Launch) (stage : Fin 2) (use : Nat) :
    List (Nat × Value) :=
  (List.finRange 8).flatMap fun i => qkIssueFacts l (recurringKeyBlock stage) i use

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g use shuffles votes base : Nat}
    (hg : g < l.threads) (stage : Fin 2) (leader : Fin 32) {F : List (Nat × Value)}
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (qkSetupPc (recurringKeyBlock stage) 0-3)
      (fun lane => recurringQkEntry l stage use (laneOf l (warpLane l g lane) == leader) ++ F)
      shuffles votes ends)
    (hFrame : ((kernel.code.drop (qkSetupPc (recurringKeyBlock stage) 0-3)).take 43).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
    (hOrdinal : ElectOrdinal l X) (count : Nat)
    (hCut : ∀ lane < 32, elections X (warpLane l g lane) (cur.pos lane) = count)
    (hPred : ∀ pair ∈ F ++ qDescriptorFacts l stage,
      pair.1 ≠ (electSite (commitElection (qkCommitSite (recurringKeyBlock stage)))).pred)
    (hAux : ∀ pair ∈ F ++ qDescriptorFacts l stage,
      pair.1 ≠ (electSite (commitElection (qkCommitSite (recurringKeyBlock stage)))).pred+1)
    (hResult : ∀ pair ∈ F ++ qDescriptorFacts l stage,
      pair.1 ∉ (electSite (commitElection (qkCommitSite (recurringKeyBlock stage)))).result.toList)
    (hBase : ((commitSite (qkCommitSite (recurringKeyBlock stage))).base,b32 base) ∈ F)
    (hWidth : base+(commitSite (qkCommitSite (recurringKeyBlock stage))).off < 2^32)
    (hAlign : (base+(commitSite (qkCommitSite (recurringKeyBlock stage))).off)%8 = 0)
include hp hMax hg stage leader cur hFrame hOrdinal count hCut hPred hAux hResult hBase hWidth
    hAlign

/-- A recorded recurring QK election leads to all eight fragment issues and its corresponding
score commit at the next election. Both the caller's frame and the advanced query bank survive. -/
theorem recurringQkPacketAndCommitWithPollCounts :
    ∃ next : SchedulerWarpReached l X g
      ((commitSite (qkCommitSite (recurringKeyBlock stage))).pc+1)
      (fun _ => F ++ qDescriptorFacts l stage) shuffles votes ends,
      (∀ lane < 32, cur.pos lane < next.pos lane ∧
        elections X (warpLane l g lane) (next.pos lane) = count+1 ∧
        ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
          okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
      (∀ i : Fin 8, X.get (warpLane l g leader.val,cur.pos leader.val+i.val) =
        some (qkIssueEvent l (warpLane l g leader.val) (recurringKeyBlock stage) i use)) ∧
      ∃ issuer idx, SameWarp l g issuer ∧ X.get (issuer,idx) =
        some ⟨(commitSite (qkCommitSite (recurringKeyBlock stage))).pc,.tc (.commit
          (commitSpec l issuer
            (base+(commitSite (qkCommitSite (recurringKeyBlock stage))).off)))⟩ ∧
        idx+1 = next.pos (laneOf l issuer) := by
  let block := recurringKeyBlock stage
  let site := qkCommitSite block
  let post := F ++ qDescriptorFacts l stage
  let facts (lane : Nat) := if lane = leader.val then recurringIssueWords l stage use else []
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨setup,hSetupPos⟩ := cur.advanceLocalWithPosition (pc' := qkPc block)
    (G := fun lane =>
      (qkGuard block,.pred (laneOf l (warpLane l g lane) == leader))::(post ++ facts lane)) (by
    intro lane hl
    obtain ⟨u,hu,hU,hWords⟩ := recurringQkSetupOfElected hp (warpLane l g lane) stage use
      _ (cur.checkpoint lane hl) hFrame
    have hs := hU.2.2.2.2
    refine ⟨u,hu,hU.mono ⟨hs.1,(holds_append ..).mpr ⟨hs.2,?_⟩⟩⟩
    by_cases h : lane = leader.val
    · simp only [facts,ite_eq_left h]
      have hLane := (Step.sameWarp_lane hBlock hg hl).2
      have hLead : (laneOf l (warpLane l g lane) == leader.val) = true :=
        beq_iff_eq.mpr (hLane.trans h)
      apply holdsList
      intro pair hm
      obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hm
      exact holds_mem (hWords hLead i) hi
    · simp only [facts,ite_eq_right h]
      trivial)
  have hOperands (i : Fin 8) :
      Holds (setup.state leader.val).regs (qkIssueFacts l block i use) := by
    have hh := (holds_append ..).mp (setup.checkpoint leader.val leader.isLt).2.2.2.2.2
    have hw : Holds (setup.state leader.val).regs (recurringIssueWords l stage use) := by
      simpa only [facts,↓reduceIte] using hh.2
    exact holdsList (fun pair hm => holds_mem hw
      (List.mem_flatMap.mpr ⟨i,by simp,hm⟩))
  obtain ⟨score,hScorePos,hElections,hPoll,hPackets⟩ :=
    qkWarpPacketWithPollCounts hp hMax hg block use leader setup hOperands
  have hScorePc : qkPc block+8 = (electSite (commitElection site)).pc := by
    dsimp only [block,site]; fin_cases stage <;> decide
  obtain ⟨line,hLinePos⟩ := score.advanceLocalWithPosition (G := fun _ => post)
    (pc' := (electSite (commitElection site)).pc) (by
      intro lane hl
      have ht := score.checkpoint lane hl
      exact ⟨_,.refl,hScorePc ▸ (ht.mono ((holds_append ..).mp ht.2.2.2.2).1)⟩)
  have hCut' (lane : Nat) (hl : lane < 32) :
      elections X (warpLane l g lane) (line.pos lane) = count := by
    rw [hLinePos,hElections lane hl,hSetupPos,hCut lane hl]
  obtain ⟨done,hCount,issuer,idx,hWarp,hCommit,hBound⟩ :=
    commitWarpFromOrdinalElectionWithPollCounts hp hMax hg site line hOrdinal count hCut'
      hPred hAux hResult
      (List.mem_append_left _ hBase) hWidth hAlign
  rw [hSetupPos] at hPackets
  refine ⟨done,?_,hPackets,issuer,idx,hWarp,hCommit,hBound⟩
  intro lane hl
  have hi := (hCount lane hl).1
  rw [hLinePos,hScorePos lane hl,hSetupPos] at hi
  refine ⟨by omega,(hCount lane hl).2.1,?_⟩
  intro other
  rw [(hCount lane hl).2.2 other,hLinePos,hPoll lane hl other,hSetupPos]

end
end PTX.Kernels.TmlFa4Fwd.Mma
