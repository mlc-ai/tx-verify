-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSecondScoreIssue
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerElectProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.TcIssueProgress
import Lemmas.Flow.CountTake
import Lemmas.Flow.ReturningPrefix
import Kernels.TmlFa4Fwd.Flow.Code.Part035

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue Prologue

noncomputable section

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes base : Nat} (hg : g < l.threads)
    (site : Fin 12) (leader : Fin 32) {F : List (Nat × Value)} {ends : Nat → Option TState}
    (elected : SchedulerWarpReached l X g ((electSite (commitElection site)).pc+1)
      (fun lane =>
        ((electSite (commitElection site)).pred,.pred (laneOf l (warpLane l g lane) == leader))::F)
      shuffles votes ends) (hAux : ∀ pair ∈ F, pair.1 ≠ (electSite (commitElection site)).pred+1)
    (hBase : ((commitSite site).base,b32 base) ∈ F) (hWidth : base+(commitSite site).off < 2^32)
include hp hMax hg site leader elected hAux hBase hWidth

/-- Execute the decoded commit from an actual elected cursor. The pre-election
matching proof can use either a fresh site or a recurring election ordinal. -/
theorem commitWarpFromElectedWithPollCounts (hAlign : (base+(commitSite site).off)%8 = 0) :
    ∃ next : SchedulerWarpReached l X g ((commitSite site).pc+1) (fun _ => F)
      shuffles votes ends,
    (∀ lane < 32, elected.pos lane ≤ next.pos lane ∧
      elections X (warpLane l g lane) (next.pos lane) =
        elections X (warpLane l g lane) (elected.pos lane) ∧
      ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
        okPolls other ((X.tr (warpLane l g lane)).take (elected.pos lane))) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.get (issuer,index) =
      some ⟨(commitSite site).pc,.tc (.commit
        (commitSpec l issuer (base+(commitSite site).off)))⟩ ∧
      index+1 = next.pos (laneOf l issuer) := by
  let lane := leader.val
  let issuer := warpLane l g lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨hWarp,hLane⟩ := Step.sameWarp_lane hBlock hg leader.isLt
  have hLead : (laneOf l issuer == leader.val) = true := beq_iff_eq.mpr hLane
  have hAt := elected.checkpoint lane leader.isLt
  change At (elected.state lane) ((electSite (commitElection site)).pc+1)
    (((electSite (commitElection site)).pred,.pred (laneOf l issuer == leader.val)) :: F) at hAt
  rw [hLead] at hAt
  obtain ⟨u,hu,hU⟩ := commitGate site true hAt hAux
  let spec := commitSpec l issuer (base+(commitSite site).off)
  have hn : Next kernel Assumptions.all l issuer (elected.before lane) u
      (.tc (.commit spec) (next u)) :=
    ⟨(elected.localSteps lane leader.isLt).trans (run_rtg hu),
      commitTemplate hp hWarp.1.2.1 site hU hBase hWidth hAlign⟩
  obtain ⟨hCommit,hPrefix,hTail⟩ := Step.tc_issue_of_maximal hMax hWarp.1.2.1 hn rfl
    (elected.recorded lane leader.isLt) (elected.continuation lane leader.isLt)
    (elected.positive lane leader.isLt) (elected.bounded lane leader.isLt)
    (elected.released lane leader.isLt) (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
      (Execution.noNewRead_snoc rfl))
  have hReady : At (next u) ((commitSite site).pc+1) F := hU.next
  have hEvery (k : Nat) (hk : k < 32) :
      ∃ pos before state,
        let th := warpLane l g k
        0 < pos ∧ pos ≤ (X.tr th).length ∧ (pos = (X.tr th).length → Step.Released l X th) ∧
        Run kernel Assumptions.all l th {} ((X.tr th).take pos) (some before) ∧
        Run kernel Assumptions.all l th before ((X.tr th).drop pos) (ends k) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l th) before state ∧
        At state ((commitSite site).pc+1) F ∧
        ((X.tr th).take pos).countP Execution.isShfl = shuffles ∧
        ((X.tr th).take pos).countP isFullWarpVote = votes ∧
        elections X th pos = elections X th (elected.pos k) ∧
        pos = elected.pos k + (if k = lane then 1 else 0) ∧
        ∀ other, okPolls other ((X.tr th).take pos) =
          okPolls other ((X.tr th).take (elected.pos k)) := by
    by_cases hCurrent : k = lane
    · subst k
      have hS := (countP_take_succ_false hCommit rfl).trans
        (elected.ordinals.shfl lane leader.isLt)
      have hV := (countP_take_succ_false hCommit rfl).trans
        (elected.ordinals.vote lane leader.isLt)
      exact ⟨_,next u,next u,Nat.succ_pos _,len_of_get hCommit,
        releasedIfLast hCommit (by intro h; cases h),hPrefix,hTail,.refl,hReady,hS,hV,
        countP_take_succ_false hCommit rfl,by simp,fun _ => countP_take_succ_false hCommit rfl⟩
    · have hOther := elected.checkpoint k hk
      have hw : laneOf l (warpLane l g k) = k := (Step.sameWarp_lane hBlock hg hk).2
      have hNot : (laneOf l (warpLane l g k) == leader.val) = false := by
        rw [hw]
        exact beq_eq_false_iff_ne.mpr hCurrent
      change At (elected.state k) ((electSite (commitElection site)).pc+1)
        (((electSite (commitElection site)).pred,
          .pred (laneOf l (warpLane l g k) == leader.val)) :: F)
        at hOther
      rw [hNot] at hOther
      obtain ⟨v,hv,hV⟩ := commitGate site false hOther hAux
      exact ⟨elected.pos k,elected.before k,v,elected.positive k hk,elected.bounded k hk,
        elected.released k hk,elected.recorded k hk,elected.continuation k hk,
        (elected.localSteps k hk).trans (run_rtg hv),hV,
        elected.ordinals.shfl k hk,elected.ordinals.vote k hk,rfl,by simp [hCurrent],fun _ => rfl⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! pos before state hPos hBound hRelease hPast hRest hNext hFrame hS hV hE hCut hPoll
    using hEvery
  refine ⟨⟨⟨pos,before,state,⟨hS,hV⟩,hRest,hNext,hFrame⟩,hPos,hBound,hRelease,hPast⟩,
    ?_,
    issuer,elected.pos lane,hWarp,?_,?_⟩
  · intro k hk
    refine ⟨?_,hE k hk,hPoll k hk⟩
    change elected.pos k ≤ pos k
    rw [hCut k hk]
    exact Nat.le_add_right ..
  · have hPc : u.pc = (commitSite site).pc := hU.1
    change X.get (issuer,elected.pos lane) = some ⟨u.pc,.tc (.commit spec)⟩ at hCommit
    rwa [hPc] at hCommit
  · change laneOf l issuer = lane at hLane
    change elected.pos lane+1 = pos (laneOf l issuer)
    rw [hLane,hCut lane leader.isLt,ite_eq_left rfl]

theorem commitWarpFromElectedWithOrdinals (hAlign : (base+(commitSite site).off)%8 = 0) :
    ∃ next : SchedulerWarpReached l X g ((commitSite site).pc+1) (fun _ => F)
      shuffles votes ends,
    (∀ lane < 32, elections X (warpLane l g lane) (next.pos lane) =
      elections X (warpLane l g lane) (elected.pos lane)) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.get (issuer,index) =
      some ⟨(commitSite site).pc,.tc (.commit
        (commitSpec l issuer (base+(commitSite site).off)))⟩ := by
  obtain ⟨next,hCount,issuer,index,hSame,hCommit,_⟩ :=
    commitWarpFromElectedWithPollCounts hp hMax hg site leader elected hAux hBase hWidth hAlign
  exact ⟨next,fun lane hl => (hCount lane hl).2.1,issuer,index,hSame,hCommit⟩

/-- Execute the decoded commit from an actual elected cursor. The pre-election
matching proof can use either a fresh site or a recurring election ordinal. -/
theorem commitWarpFromElected (hAlign : (base+(commitSite site).off)%8 = 0) :
    Nonempty (SchedulerWarpReached l X g ((commitSite site).pc+1) (fun _ => F)
      shuffles votes ends) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.get (issuer,index) =
      some ⟨(commitSite site).pc,.tc (.commit
        (commitSpec l issuer (base+(commitSite site).off)))⟩ := by
  obtain ⟨after,_,hEvent⟩ := commitWarpFromElectedWithOrdinals hp hMax hg site leader elected
    hAux hBase hWidth hAlign
  exact ⟨⟨after⟩,hEvent⟩
end

/-- A fresh full-warp election issues its decoded commit in the elected lane and
advances every lane to the same continuation while preserving the common frame. -/
theorem commitWarpFromFreshElection {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes base : Nat} (hg : g < l.threads) (site : Fin 12)
    {F : List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (electSite (commitElection site)).pc (fun _ => F)
      shuffles votes ends)
    (hFresh : ∀ lane < 32, ∀ j < cur.pos lane, ∀ mask inst leader,
      ¬ X.Elect (warpLane l g lane,j) (electSite (commitElection site)).pc mask inst leader)
    (hPred : ∀ pair ∈ F, pair.1 ≠ (electSite (commitElection site)).pred)
    (hAux : ∀ pair ∈ F, pair.1 ≠ (electSite (commitElection site)).pred+1)
    (hResult : ∀ pair ∈ F, pair.1 ∉ (electSite (commitElection site)).result.toList)
    (hBase : ((commitSite site).base,b32 base) ∈ F)
    (hWidth : base+(commitSite site).off < 2^32)
    (hAlign : (base+(commitSite site).off)%8 = 0) :
    Nonempty (SchedulerWarpReached l X g ((commitSite site).pc+1) (fun _ => F)
      shuffles votes ends) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.get (issuer,index) =
      some ⟨(commitSite site).pc,.tc (.commit
        (commitSpec l issuer (base+(commitSite site).off)))⟩ := by
  let afterFrame := fun lane leader =>
    ((electSite (commitElection site)).pred,.pred (laneOf l (warpLane l g lane) == leader)) :: F
  obtain ⟨leader,elected,_⟩ := cur.consumeElection hp hMax hg
    (fun lane => electState l (warpLane l g lane) (cur.state lane) (commitElection site)) afterFrame
    hFresh (fun lane hl => electTemplate _ (cur.checkpoint lane hl))
    (fun lane hl k => electStateFrame _ (cur.checkpoint lane hl) k hPred hResult)
  exact commitWarpFromElected hp hMax hg site leader elected hAux hBase hWidth hAlign

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes base : Nat} (hg : g < l.threads)
    (site : Fin 12) {F : List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (electSite (commitElection site)).pc (fun _ => F)
      shuffles votes ends) (hOrdinal : ElectOrdinal l X) (n : Nat)
    (hCut : ∀ lane < 32, elections X (warpLane l g lane) (cur.pos lane) = n)
    (hPred : ∀ pair ∈ F, pair.1 ≠ (electSite (commitElection site)).pred)
    (hAux : ∀ pair ∈ F, pair.1 ≠ (electSite (commitElection site)).pred+1)
    (hResult : ∀ pair ∈ F, pair.1 ∉ (electSite (commitElection site)).result.toList)
    (hBase : ((commitSite site).base,b32 base) ∈ F) (hWidth : base+(commitSite site).off < 2^32)
include hp hMax hg site cur hOrdinal n hCut hPred hAux hResult hBase hWidth

/-- A recurring election on the aligned ordinal sends exactly one decoded commit. -/
theorem commitWarpFromOrdinalElectionWithPollCounts (hAlign : (base+(commitSite site).off)%8 = 0) :
    ∃ next : SchedulerWarpReached l X g ((commitSite site).pc+1) (fun _ => F)
      shuffles votes ends,
    (∀ lane < 32, cur.pos lane < next.pos lane ∧
      elections X (warpLane l g lane) (next.pos lane) = n+1 ∧
      ∀ other, okPolls other ((X.tr (warpLane l g lane)).take (next.pos lane)) =
        okPolls other ((X.tr (warpLane l g lane)).take (cur.pos lane))) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.get (issuer,index) =
      some ⟨(commitSite site).pc,.tc (.commit
        (commitSpec l issuer (base+(commitSite site).off)))⟩ ∧
      index+1 = next.pos (laneOf l issuer) := by
  let afterFrame := fun lane leader =>
    ((electSite (commitElection site)).pred,.pred (laneOf l (warpLane l g lane) == leader)) :: F
  obtain ⟨leader,elected,hElect⟩ := cur.consumeElectionAtOrdinal hp hMax hg
    (fun lane => electState l (warpLane l g lane) (cur.state lane) (commitElection site)) afterFrame
    hOrdinal n hCut (fun lane hl => electTemplate _ (cur.checkpoint lane hl))
    (fun lane hl k => electStateFrame _ (cur.checkpoint lane hl) k hPred hResult)
  obtain ⟨next,hCount,hEvent⟩ := commitWarpFromElectedWithPollCounts hp hMax hg site leader elected
    hAux hBase hWidth hAlign
  refine ⟨next,fun lane hl => ?_,hEvent⟩
  obtain ⟨hi,inst,he⟩ := hElect lane hl
  obtain ⟨hPos,hElec,hPoll⟩ := hCount lane hl
  refine ⟨by rw [hi] at hPos; omega,?_,?_⟩
  · rw [hElec,hi]
    unfold elections
    rw [List.take_add_one,show (X.tr (warpLane l g lane))[cur.pos lane]? = _ from he]
    simp only [Option.toList_some,List.countP_append,List.countP_cons,isElectEv,↓reduceIte,
      List.countP_nil,Nat.zero_add]
    exact congrArg (·+1) (hCut lane hl)
  · intro other
    rw [hPoll other,hi]
    exact countP_take_succ_false he rfl

end
end PTX.Kernels.TmlFa4Fwd.Mma
