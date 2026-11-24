-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkBroadcast
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkIssueProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaScoreRounds
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitOpening
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.TcIssueProgress
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open Thread.Scores (ScoreCommit scoreCommitAtBlock OpeningScoreCommit)

noncomputable section

private def firstScoreCommitFrame (l : Launch) : List (Nat × Value) :=
  [(1188,b32 (l.sharedBase+80)),(2562,b32 (l.sharedBase+8))] ++ secondQKCommonOperands l

private theorem firstScoreCommitReg (l : Launch) (r : Nat) (hr : r ∈ [382,383,2561]) :
    ∀ pair ∈ firstScoreCommitFrame l, pair.1 ≠ r := by
  intro pair hm
  simp only [firstScoreCommitFrame,secondQKCommonOperands,secondQKRootFacts,List.cons_append,
    List.nil_append,List.mem_cons] at hm
  have hr' : r = 382 ∨ r = 383 ∨ r = 2561 := by simpa using hr
  rcases hm with rfl | rfl | rfl | rfl | rfl | hDescriptor
  all_goals try (omega)
  unfold qDescriptorFacts at hDescriptor
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hDescriptor
  change 9624+i.val ≠ r
  omega

private theorem openingQKAtScoreElection {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2153 (fun _ => firstQKInputFacts l) shuffles votes ends) :
    ∃ leader : Fin 32, ∃ index inst, ∃ next : SchedulerWarpReached l X g 2205
      (fun _ => firstScoreCommitFrame l) shuffles votes ends,
      X.Elect (warpLane l g leader,index) 2153 4294967295 inst leader.val ∧
      next.pos leader.val = index+1+8 ∧
      ∀ j : Fin 8, X.get (warpLane l g leader,index+1+j.val) =
        some (qkIssueEvent l (warpLane l g leader) 0 j 0) := by
  obtain ⟨leader,elected,hElect⟩ := firstQKElectedOfMaximal hp hMax hg cur
  let selected := leader.val
  let thread := warpLane l g
  let pos := fun lane => elected.pos lane + (if lane = selected then 8 else 0)
  let frame := firstScoreCommitFrame l
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hResult (lane : Nat) (hl : lane < 32) : ∃ before state,
      At state 2205 frame ∧
      Run kernel Assumptions.all l (thread lane) before ((X.tr (thread lane)).drop (pos lane))
        (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before state ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take (pos lane))
        (some before) ∧
      pos lane ≤ (X.tr (thread lane)).length ∧
      (pos lane = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      ((X.tr (thread lane)).take (pos lane)).countP Execution.isShfl = shuffles ∧
      ((X.tr (thread lane)).take (pos lane)).countP isFullWarpVote = votes ∧
      (lane = selected → ∀ j : Fin 8, X.get (thread lane,elected.pos lane+j.val) =
        some (qkIssueEvent l (thread lane) 0 j 0)) := by
    obtain ⟨hWarp,hLane⟩ := Step.sameWarp_lane hBlock hg hl
    obtain ⟨u,hu,hU,hCommon,hOps⟩ := firstQKAssemblyAtIssueWithRemainder hp (g := thread lane)
      (elected.checkpoint lane hl)
    have hAtFull : At u 2197 ((9636,.pred (laneOf l (thread lane) == leader.val)) :: frame) :=
      hU.mono ⟨hU.2.2.2.2.1,(holds_append ..).mpr ⟨hU.2.2.2.2.2,hCommon⟩⟩
    have hToIssue := (elected.localSteps lane hl).trans hu
    by_cases hLead : lane = selected
    · have hPred : (laneOf l (thread lane) == leader.val) = true := by
        apply beq_iff_eq.mpr
        exact hLane.trans hLead
      rw [hPred] at hOps
      have hAt : At u (qkPc 0) frame := hAtFull.mono hAtFull.2.2.2.2.2
      obtain ⟨before,ready,hReady,hPast,hRun,hSteps,hCounts,hEvents⟩ :=
        qkPacketOfMaximal hp hMax hWarp.1.2.1 0 0 hAt (hOps rfl)
          (elected.recorded lane hl) (elected.continuation lane hl) hToIssue
          (elected.positive lane hl) (elected.bounded lane hl) (elected.released lane hl)
      have hLength : elected.pos lane+8 = elected.pos lane+(7 : Fin 8).val+1 := by omega
      have he := hEvents 7
      have hBound : elected.pos lane+8 ≤ (X.tr (thread lane)).length :=
        hLength.symm ▸ Nat.succ_le_of_lt (len_of_get he)
      have hRelease : elected.pos lane+8 = (X.tr (thread lane)).length →
          Step.Released l X (thread lane) :=
        hLength.symm ▸ releasedIfLast he (by intro h; cases h)
      have hS := (hCounts Execution.isShfl (fun _ => rfl)).trans (elected.ordinals.shfl lane hl)
      have hV := (hCounts isFullWarpVote (fun _ => rfl)).trans (elected.ordinals.vote lane hl)
      simpa only [pos,ite_eq_left hLead] using
        ⟨before,ready,hReady,hRun,hSteps,hPast,hBound,hRelease,hS,hV,fun _ => hEvents⟩
    · have hPred : (laneOf l (thread lane) == leader.val) = false :=
        beq_eq_false_iff_ne.mpr (fun h => hLead (hLane.symm.trans h))
      rw [hPred] at hAtFull
      obtain ⟨ready,hReady,ht⟩ := skipQK (l := l) (g := thread lane) 0 hAtFull
      simpa only [pos,ite_eq_right hLead,Nat.add_zero] using
        ⟨elected.before lane,ready,hReady,elected.continuation lane hl,hToIssue.trans ht,
          elected.recorded lane hl,elected.bounded lane hl,elected.released lane hl,
          elected.ordinals.shfl lane hl,elected.ordinals.vote lane hl,
          fun h => (hLead h).elim⟩
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! before state hAt hRun hSteps hPast hBound hRelease hShuffle hVote hEvents using hResult
  let next : SchedulerWarpReached l X g 2205 (fun _ => frame) shuffles votes ends :=
    ⟨⟨pos,before,state,⟨hShuffle,hVote⟩,hRun,hSteps,hAt⟩,
      fun lane hl => (elected.positive lane hl).trans_le (Nat.le_add_right ..),
      hBound,hRelease,hPast⟩
  obtain ⟨hPos,inst,he⟩ := hElect selected leader.isLt
  have hStart : next.pos selected = cur.pos selected+1+8 := by
    change elected.pos selected + (if selected = selected then 8 else 0) = _
    rw [ite_eq_left (show selected = selected from rfl),hPos]
  have hPacket := hEvents selected leader.isLt rfl
  rw [hPos] at hPacket
  exact ⟨leader,cur.pos selected,inst,next,he,hStart,hPacket⟩

/-- The query barrier pointer retained after the first score commit. -/
def openingQueryAfterScoreFrame (l : Launch) : List (Nat × Value) :=
  [(2562,b32 (l.sharedBase+8))]

/-- The opening score commit has issued and the MMA warp can start its second query acquire. -/
abbrev OpeningSecondQueryMmaReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 2209 (fun _ => openingQueryAfterScoreFrame l)
    shuffles votes ends)

/-- After issuing the opening score commit, Q1 operands remain live in every MMA lane. -/
abbrev OpeningSecondQueryMmaReachedWithOperands (l : Launch) (X : Execution)
    (g shuffles votes : Nat) (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 2209
    (fun _ => openingQueryAfterScoreFrame l ++ secondQKCommonOperands l) shuffles votes ends)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2148 (fun _ => firstQKBroadcastFacts l) shuffles votes ends)
include hp hMax hg cur

/-- The elected opening stage-zero QK issuer records the following score-ready commit
and every lane returns to the second query prelude. -/
theorem openingScoreCommitAndQueryOperandsFromWarp :
    OpeningSecondQueryMmaReachedWithOperands l X g (shuffles+2) votes ends ∧
    ∃ issuer first,
      SameWarp l g issuer ∧
      (∀ j : Fin 8, Thread.Mma.InitialQueryFragment X 0 (issuer,first+j.val) ∧
        X.MmaIssue (issuer,first+j.val) (scoreColumn 0) (qkOperands l issuer 0 j 0)
          (decide (j.val ≠ 0)) (List.replicate 4 0)) ∧
        ScoreCommit l X (issuer,first+9) (issuer/l.block) 0
          (commitSpec l issuer (l.sharedBase+80)) 0 ∧
        OpeningScoreCommit X (issuer,first+9) 0 (commitSpec l issuer (l.sharedBase+80)) := by
  obtain ⟨broadcast⟩ := firstQKAfterBroadcastOfMaximal hp hMax hg cur
  obtain ⟨leader,index,inst,ready,hInitial,hReadyPos,hPacket⟩ :=
    openingQKAtScoreElection hp hMax hg broadcast
  let frame := firstScoreCommitFrame l
  let afterFrame := fun lane nextLeader =>
    ((electSite 1).pred,.pred (laneOf l (warpLane l g lane) == nextLeader)) :: frame
  have hPred : ∀ pair ∈ frame, pair.1 ≠ (electSite 1).pred :=
    firstScoreCommitReg l 382 (by decide)
  have hResult : ∀ pair ∈ frame, pair.1 ∉ (electSite 1).result.toList := by
    intro pair hm
    simpa [electSite] using firstScoreCommitReg l 2561 (by decide) pair hm
  obtain ⟨nextLeader,elected,hNextElect⟩ := ready.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (ready.state lane) 1) afterFrame
    (fun lane hl _ hj _ _ _ he => noEarlierMmaElection 1 Flow.code_2205
      (by decide +kernel) (by decide +kernel) (ready.checkpoint lane hl)
      (ready.recorded lane hl) (ready.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 1 (ready.checkpoint lane hl))
    (fun lane hl k => electStateFrame 1 (ready.checkpoint lane hl) k hPred hResult)
  let lane := leader.val
  let issuer := warpLane l g lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨hWarp,hLane⟩ := Step.sameWarp_lane hBlock hg leader.isLt
  obtain ⟨hPos,inst',he⟩ := hNextElect lane leader.isLt
  have hSelf : SameWarp l issuer issuer := ⟨⟨hWarp.1.2.1,hWarp.1.2.1,rfl⟩,rfl⟩
  have hSame := sameLeader hMax.1 hSelf hInitial he
  have hLead : (laneOf l issuer == nextLeader.val) = true := beq_iff_eq.mpr (hLane.trans hSame)
  have hAt := elected.checkpoint lane leader.isLt
  change At (elected.state lane) 2206
    (((electSite 1).pred,.pred (laneOf l issuer == nextLeader.val)) :: frame) at hAt
  rw [hLead] at hAt
  obtain ⟨u,hu,hU⟩ := commitGate 0 true hAt (firstScoreCommitReg l 383 (by decide))
  have hs := hp.shared.2.1
  have ha := hp.shared.1
  let spec := commitSpec l issuer (l.sharedBase+80)
  have hn : Next kernel Assumptions.all l issuer (elected.before lane) u
      (.tc (.commit spec) (next u)) :=
    ⟨(elected.localSteps lane leader.isLt).trans (run_rtg hu),
      commitTemplate hp hWarp.1.2.1 0 (a := l.sharedBase+80) hU List.mem_cons_self
        (by change l.sharedBase+80+0 < 2^32; omega)
        (by change (l.sharedBase+80+0)%8=0; omega)⟩
  obtain ⟨hCommit,hPrefix,hTail⟩ := Step.tc_issue_of_maximal hMax hWarp.1.2.1 hn rfl
    (elected.recorded lane leader.isLt) (elected.continuation lane leader.isLt)
    (elected.positive lane leader.isLt) (elected.bounded lane leader.isLt)
    (elected.released lane leader.isLt) (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
      (Execution.noNewRead_snoc rfl))
  have hReady : At (next u) 2209 (openingQueryAfterScoreFrame l ++ secondQKCommonOperands l) := by
    exact (hU.next).mono hU.2.2.2.2.2
  have hEvery (k : Nat) (hk : k < 32) :
      ∃ pos before state,
        let th := warpLane l g k
        0 < pos ∧ pos ≤ (X.tr th).length ∧ (pos = (X.tr th).length → Step.Released l X th) ∧
        Run kernel Assumptions.all l th {} ((X.tr th).take pos) (some before) ∧
        Run kernel Assumptions.all l th before ((X.tr th).drop pos) (ends k) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l th) before state ∧
        At state 2209 (openingQueryAfterScoreFrame l ++ secondQKCommonOperands l) ∧
        ((X.tr th).take pos).countP Execution.isShfl = shuffles+2 ∧
        ((X.tr th).take pos).countP isFullWarpVote = votes := by
    by_cases hCurrent : k = lane
    · subst k
      have hS := (countP_take_succ_false hCommit rfl).trans
        (elected.ordinals.shfl lane leader.isLt)
      have hV := (countP_take_succ_false hCommit rfl).trans
        (elected.ordinals.vote lane leader.isLt)
      exact ⟨_,next u,next u,Nat.succ_pos _,len_of_get hCommit,
        releasedIfLast hCommit (by intro h; cases h),hPrefix,hTail,.refl,hReady,hS,hV⟩
    · have hOther := elected.checkpoint k hk
      have hw : laneOf l (warpLane l g k) = k := (Step.sameWarp_lane hBlock hg hk).2
      have hLeaders : nextLeader.val = lane := hSame.symm
      have hNot : (laneOf l (warpLane l g k) == nextLeader.val) = false := by
        rw [hw,hLeaders]
        exact beq_eq_false_iff_ne.mpr hCurrent
      change At (elected.state k) 2206
        (((electSite 1).pred,.pred (laneOf l (warpLane l g k) == nextLeader.val)) :: frame)
        at hOther
      rw [hNot] at hOther
      obtain ⟨v,hv,hV⟩ := commitGate 0 false hOther
        (firstScoreCommitReg l 383 (by decide))
      exact ⟨elected.pos k,elected.before k,v,elected.positive k hk,elected.bounded k hk,
        elected.released k hk,elected.recorded k hk,elected.continuation k hk,
        (elected.localSteps k hk).trans (run_rtg hv),hV.mono hV.2.2.2.2.2,
        elected.ordinals.shfl k hk,elected.ordinals.vote k hk⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! pos before state hPos' hBound hRelease hPast hRest hNext hFrame hS hV using hEvery
  refine ⟨⟨⟨⟨pos,before,state,⟨hS,hV⟩,hRest,hNext,hFrame⟩,hPos',hBound,hRelease,hPast⟩⟩,?_⟩
  have hSite : u.pc = 2208 := hU.1
  have hIndex : elected.pos lane = index+1+9 := by rw [hPos,hReadyPos]
  rw [hSite,hIndex] at hCommit
  refine ⟨issuer,index+1,hWarp,fun j => ?_,scoreCommitAtBlock hp hMax.1 0 0 rfl hCommit,
    OpeningScoreCommit.of_decoded hCommit⟩
  exact ⟨Thread.Mma.initialQueryFragmentOfIssue j 0 (hPacket j),_,hPacket j⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
