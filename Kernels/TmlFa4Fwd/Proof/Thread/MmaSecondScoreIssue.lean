-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondQueryProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondQkAssembly
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.TcIssueProgress
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue Prologue
open Thread.Scores (ScoreCommit scoreCommitAtBlock OpeningScoreCommit)

noncomputable section

private def secondBroadcastFrame (l : Launch) : List (Nat × Value) :=
  [(2565,b32 128),(2563,b32 0)] ++ secondQKCommonOperands l

private theorem secondCommonFresh {l : Launch} {r : Nat} (hr : r ≤ 2602 ∨ 9632 < r)
    (hK : r ≠ 2564) (hI : r ≠ 9632) (hS : r ≠ 2535) :
    ∀ pair ∈ secondQKCommonOperands l, pair.1 ≠ r := by
  intro pair hm
  simp only [secondQKCommonOperands,secondQKRootFacts,List.cons_append,List.nil_append,
    List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | hQ
  · exact hK.symm
  · exact hI.symm
  · exact hS.symm
  · unfold qDescriptorFacts at hQ
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hQ
    change 9624+i.val ≠ r
    have := i.isLt
    omega

private theorem secondBroadcastSetup {l : Launch} {g : Nat} {s : TState}
    (hs : At s 2213 (openingSecondQueryWaitFrame l ++ secondQKCommonOperands l)) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧
      At t 2214 (secondBroadcastFrame l) := by
  have hSeg : Seg kernel [] l g 1 2213 [] 2214 [(2565,b32 128)] := by
    intro u hu
    seg_fp hu using rfl
  obtain ⟨t,hRun,hAt⟩ := hSeg s (hs.mono trivial)
  have hStep : Tau kernel [] l g s t := by
    apply tauStep_iff.mp
    unfold run at hRun
    cases h : tauStep kernel [] l g s <;> simp_all [run]
  have hCode := Flow.code_2213
  rw [← hs.1] at hCode
  have hKeep (r : Nat) (hr : r ≠ 2565) : t.regs r = s.regs r :=
    tau_core_regs hCode hStep (by simpa [writesRegs] using hr)
  have hF := hs.2.2.2.2
  have hCommon : Holds t.regs (secondQKCommonOperands l) := by
    apply holdsSchedulerFrame (regs := (secondQKCommonOperands l).map Prod.fst) hF.2.2
    · intro r hr
      obtain ⟨pair,hm,rfl⟩ := List.mem_map.mp hr
      exact hKeep _ (secondCommonFresh (.inl (by decide)) (by decide) (by decide) (by decide)
        pair hm)
    · exact fun _ h => List.mem_map_of_mem h
  exact ⟨t,run_rtg (localRun (by decide) (by decide) hs.1 rfl hRun),
    hAt.mono ⟨hAt.2.2.2.2.1,(hKeep 2563 (by decide)).trans hF.1,hCommon⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
include hp hMax hg

private theorem secondScoreBroadcastOfMaximal {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2213
      (fun _ => openingSecondQueryWaitFrame l ++ secondQKCommonOperands l)
      shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2215 (fun _ => secondQKInputFacts l)
      (shuffles+1) votes ends) := by
  obtain ⟨start⟩ := cur.advanceLocal (G := fun _ => secondBroadcastFrame l)
    (fun lane hl => secondBroadcastSetup (g := warpLane l g lane) (cur.checkpoint lane hl))
  have hFresh : ∀ lane < 32, ∀ pair ∈ secondBroadcastFrame l, pair.1 ≠ 2602 := by
    intro _ _ pair hm
    simp only [secondBroadcastFrame,List.cons_append,List.nil_append,List.mem_cons] at hm
    rcases hm with rfl | rfl | hOther
    · decide
    · decide
    · exact secondCommonFresh (.inl (by decide)) (by decide) (by decide) (by decide) pair hOther
  obtain ⟨done⟩ := start.consumeShuffle (dst := 2602) hp hMax hg .idx
    (fun _ => b32 128) (fun _ => 0) (fun _ => 31) hFresh
    (fun lane hl => laneZeroBroadcast hp (by decide) ((start.checkpoint lane hl).mono
      ⟨(start.checkpoint lane hl).2.2.2.2.1,trivial⟩) Flow.code_2214)
  exact done.advanceLocal (G := fun _ => secondQKInputFacts l)
    (fun lane hl => by
      have hAt := done.checkpoint lane hl
      exact ⟨_,.refl,hAt.mono ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.2⟩⟩)

private theorem secondQKElectedOfMaximal {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2215 (fun _ => secondQKInputFacts l) shuffles votes ends) :
    ∃ leader : Fin 32, ∃ done : SchedulerWarpReached l X g 2216
      (fun lane => (9653,.pred (laneOf l (warpLane l g lane) == leader.val)) ::
        secondQKInputFacts l) shuffles votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+1 ∧
        ∃ inst, X.Elect (warpLane l g lane,cur.pos lane) 2215 4294967295 inst leader := by
  have hPred : ∀ pair ∈ secondQKInputFacts l, pair.1 ≠ (electSite 2).pred := by
    intro pair hm
    simp only [secondQKInputFacts,List.cons_append,List.nil_append,List.mem_cons] at hm
    rcases hm with rfl | rfl | hOther
    · decide
    · decide
    · exact secondCommonFresh (.inr (by decide)) (by decide) (by decide) (by decide) pair hOther
  exact cur.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (cur.state lane) 2)
    (fun lane leader => (9653,.pred (laneOf l (warpLane l g lane) == leader)) ::
      secondQKInputFacts l)
    (fun lane hl _ hj _ _ _ he => noEarlierMmaElection 2 Flow.code_2215
      (by decide +kernel) (by decide +kernel) (cur.checkpoint lane hl)
      (cur.recorded lane hl) (cur.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 2 (cur.checkpoint lane hl))
    (fun lane hl leader => electStateFrame 2 (cur.checkpoint lane hl) leader hPred
      (by simp [electSite]))

private theorem secondQKAtScoreElection {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2215 (fun _ => secondQKInputFacts l) shuffles votes ends) :
    ∃ leader : Fin 32, ∃ index inst, ∃ next : SchedulerWarpReached l X g 2267
      (fun _ => [(2535,b32 l.sharedBase)]) shuffles votes ends,
      X.Elect (warpLane l g leader,index) 2215 4294967295 inst leader.val ∧
      next.pos leader.val = index+1+8 ∧
      ∀ j : Fin 8, X.get (warpLane l g leader,index+1+j.val) =
        some (qkIssueEvent l (warpLane l g leader) 1 j 0) := by
  obtain ⟨leader,elected,hElect⟩ := secondQKElectedOfMaximal hp hMax hg cur
  let selected := leader.val
  let thread := warpLane l g
  let pos := fun lane => elected.pos lane + (if lane = selected then 8 else 0)
  let frame := [(2535,b32 l.sharedBase)]
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hResult (lane : Nat) (hl : lane < 32) : ∃ before state,
      At state 2267 frame ∧
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
        some (qkIssueEvent l (thread lane) 1 j 0)) := by
    obtain ⟨hWarp,hLane⟩ := Step.sameWarp_lane hBlock hg hl
    obtain ⟨u,hu,hU,hOps⟩ := secondQKAssemblyAtIssue hp (g := thread lane)
      (elected.checkpoint lane hl)
    have hToIssue := (elected.localSteps lane hl).trans hu
    by_cases hLead : lane = selected
    · have hPred : (laneOf l (thread lane) == leader.val) = true := by
        apply beq_iff_eq.mpr
        exact hLane.trans hLead
      rw [hPred] at hOps
      have hAt : At u (qkPc 1) frame := hU.mono hU.2.2.2.2.2
      obtain ⟨before,ready,hReady,hPast,hRun,hSteps,hCounts,hEvents⟩ :=
        qkPacketOfMaximal hp hMax hWarp.1.2.1 1 0 hAt (hOps rfl)
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
      rw [hPred] at hU
      obtain ⟨ready,hReady,ht⟩ := skipQK (l := l) (g := thread lane) 1 hU
      simpa only [pos,ite_eq_right hLead,Nat.add_zero] using
        ⟨elected.before lane,ready,hReady,elected.continuation lane hl,hToIssue.trans ht,
          elected.recorded lane hl,elected.bounded lane hl,elected.released lane hl,
          elected.ordinals.shfl lane hl,elected.ordinals.vote lane hl,
          fun h => (hLead h).elim⟩
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! before state hAt hRun hSteps hPast hBound hRelease hShuffle hVote hEvents using hResult
  let next : SchedulerWarpReached l X g 2267 (fun _ => frame) shuffles votes ends :=
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

omit hp hMax hg in
/-- Both opening QK packs have issued and the warp has reached the first K release. -/
abbrev OpeningInitialKeyReturnReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 2271 (fun _ => [(2535,b32 l.sharedBase)])
    shuffles votes ends)

/-- After its second query acquire, the warp issues all eight stage-one QK fragments
followed by their opening score commit. -/
theorem openingSecondScoreAndKeyReturnFromWarp {ends : Nat → Option TState}
    (hAcquired : OpeningSecondQueryMmaAcquiredWithFrame l X g shuffles votes ends
      (secondQKCommonOperands l)) :
    OpeningInitialKeyReturnReached l X g (shuffles+1) votes ends ∧
    ∃ issuer first,
      SameWarp l g issuer ∧
      (∀ j : Fin 8, Thread.Mma.InitialQueryFragment X 1 (issuer,first+j.val) ∧
        X.MmaIssue (issuer,first+j.val) (scoreColumn 1) (qkOperands l issuer 1 j 0)
          (decide (j.val ≠ 0)) (List.replicate 4 0)) ∧
        ScoreCommit l X (issuer,first+9) (issuer/l.block) 1
          (commitSpec l issuer (l.sharedBase+88)) 0 ∧
        OpeningScoreCommit X (issuer,first+9) 1 (commitSpec l issuer (l.sharedBase+88)) := by
  obtain ⟨cur,_⟩ := hAcquired
  obtain ⟨broadcast⟩ := secondScoreBroadcastOfMaximal hp hMax hg cur
  obtain ⟨leader,index,inst,ready,hInitial,hReadyPos,hPacket⟩ :=
    secondQKAtScoreElection hp hMax hg broadcast
  let frame := [(2535,b32 l.sharedBase)]
  let afterFrame := fun lane nextLeader =>
    ((electSite 3).pred,.pred (laneOf l (warpLane l g lane) == nextLeader)) :: frame
  have hPred : ∀ pair ∈ frame, pair.1 ≠ (electSite 3).pred := by simp [frame,electSite]
  have hResult : ∀ pair ∈ frame, pair.1 ∉ (electSite 3).result.toList := by simp [frame,electSite]
  obtain ⟨nextLeader,elected,hNextElect⟩ := ready.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (ready.state lane) 3) afterFrame
    (fun lane hl _ hj _ _ _ he => noEarlierMmaElection 3 Flow.code_2267
      (by decide +kernel) (by decide +kernel) (ready.checkpoint lane hl)
      (ready.recorded lane hl) (ready.localSteps lane hl) hj he)
    (fun lane hl => electTemplate 3 (ready.checkpoint lane hl))
    (fun lane hl k => electStateFrame 3 (ready.checkpoint lane hl) k hPred hResult)
  let lane := leader.val
  let issuer := warpLane l g lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨hWarp,hLane⟩ := Step.sameWarp_lane hBlock hg leader.isLt
  obtain ⟨hPos,inst',he⟩ := hNextElect lane leader.isLt
  have hSelf : SameWarp l issuer issuer := ⟨⟨hWarp.1.2.1,hWarp.1.2.1,rfl⟩,rfl⟩
  have hSame := sameLeader hMax.1 hSelf hInitial he
  have hLead : (laneOf l issuer == nextLeader.val) = true := beq_iff_eq.mpr (hLane.trans hSame)
  have hAt := elected.checkpoint lane leader.isLt
  change At (elected.state lane) 2268
    (((electSite 3).pred,.pred (laneOf l issuer == nextLeader.val)) :: frame) at hAt
  rw [hLead] at hAt
  obtain ⟨u,hu,hU⟩ := commitGate 1 true hAt (by simp [frame,electSite,commitElection])
  have hs := hp.shared.2.1
  have ha := hp.shared.1
  let spec := commitSpec l issuer (l.sharedBase+88)
  have hn : Next kernel Assumptions.all l issuer (elected.before lane) u
      (.tc (.commit spec) (next u)) :=
    ⟨(elected.localSteps lane leader.isLt).trans (run_rtg hu),
      commitTemplate hp hWarp.1.2.1 1 (a := l.sharedBase) hU List.mem_cons_self
        (by change l.sharedBase+88 < 2^32; omega)
        (by change (l.sharedBase+88)%8=0; omega)⟩
  obtain ⟨hCommit,hPrefix,hTail⟩ := Step.tc_issue_of_maximal hMax hWarp.1.2.1 hn rfl
    (elected.recorded lane leader.isLt) (elected.continuation lane leader.isLt)
    (elected.positive lane leader.isLt) (elected.bounded lane leader.isLt)
    (elected.released lane leader.isLt) (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
      (Execution.noNewRead_snoc rfl))
  have hReady : At (next u) 2271 frame := hU.next
  have hEvery (k : Nat) (hk : k < 32) :
      ∃ pos before state,
        let th := warpLane l g k
        0 < pos ∧ pos ≤ (X.tr th).length ∧ (pos = (X.tr th).length → Step.Released l X th) ∧
        Run kernel Assumptions.all l th {} ((X.tr th).take pos) (some before) ∧
        Run kernel Assumptions.all l th before ((X.tr th).drop pos) (ends k) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l th) before state ∧
        At state 2271 frame ∧
        ((X.tr th).take pos).countP Execution.isShfl = shuffles+1 ∧
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
      change At (elected.state k) 2268
        (((electSite 3).pred,.pred (laneOf l (warpLane l g k) == nextLeader.val)) :: frame)
        at hOther
      rw [hNot] at hOther
      obtain ⟨v,hv,hV⟩ := commitGate 1 false hOther (by simp [frame,electSite,commitElection])
      exact ⟨elected.pos k,elected.before k,v,elected.positive k hk,elected.bounded k hk,
        elected.released k hk,elected.recorded k hk,elected.continuation k hk,
        (elected.localSteps k hk).trans (run_rtg hv),hV,
        elected.ordinals.shfl k hk,elected.ordinals.vote k hk⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! pos before state hPos' hBound hRelease hPast hRest hNext hFrame hS hV using hEvery
  refine ⟨⟨⟨⟨pos,before,state,⟨hS,hV⟩,hRest,hNext,hFrame⟩,hPos',hBound,hRelease,hPast⟩⟩,?_⟩
  have hSite : u.pc = 2270 := hU.1
  have hIndex : elected.pos lane = index+1+9 := by rw [hPos,hReadyPos]
  rw [hSite,hIndex] at hCommit
  refine ⟨issuer,index+1,hWarp,fun j => ?_,scoreCommitAtBlock hp hMax.1 1 1 rfl hCommit,
    OpeningScoreCommit.of_decoded hCommit⟩
  exact ⟨Thread.Mma.initialQueryFragmentOfIssue j 0 (hPacket j),_,hPacket j⟩

/-- Once the second query is ready, every MMA lane acquires it and the elected lane
issues the stage-one QK packet and its score commit. -/
theorem openingSecondScoreAndKeyReturnFromReadyWarp {ends : Nat → Option TState}
    (hReached : OpeningSecondQueryMmaReachedWithOperands l X g shuffles votes ends)
    (hReady : let log := X.objects (Thread.Output.queryObject l (g/l.block) 1)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    OpeningInitialKeyReturnReached l X g (shuffles+1) votes ends ∧
    ∃ issuer first,
      SameWarp l g issuer ∧
      (∀ j : Fin 8, Thread.Mma.InitialQueryFragment X 1 (issuer,first+j.val) ∧
        X.MmaIssue (issuer,first+j.val) (scoreColumn 1) (qkOperands l issuer 1 j 0)
          (decide (j.val ≠ 0)) (List.replicate 4 0)) ∧
        ScoreCommit l X (issuer,first+9) (issuer/l.block) 1
          (commitSpec l issuer (l.sharedBase+88)) 0 ∧
        OpeningScoreCommit X (issuer,first+9) 1 (commitSpec l issuer (l.sharedBase+88)) :=
  openingSecondScoreAndKeyReturnFromWarp hp hMax hg
    (openingSecondQueryAcquireFromWarpWithFrame hp hMax hg
      (secondCommonFresh (.inl (by decide)) (by decide) (by decide) (by decide))
      (secondCommonFresh (.inr (by decide)) (by decide) (by decide) (by decide)) hReached hReady)

end
end PTX.Kernels.TmlFa4Fwd.Mma
