-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryExpectationProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryBoxProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Step.Object

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.AsyncCopy
open Prologue Epilogue

/-- The elected lane records its transaction expectation at its own cursor, and every
other lane keeps its cursor. -/
theorem expectationAtElectedWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g entry site shuffles votes : Nat} (hg : g < l.threads) (obj : Nat → Loc)
    {F G : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (done : SchedulerWarpReached l X g entry G shuffles votes ends) (leader : Fin 32)
    (hLead : ∃ s u, s.pc = site ∧ At u (site+1) (F leader) ∧
      Next kernel Assumptions.all l (warpLane l g leader) (done.state leader) s
        (.arrive (obj ((warpLane l g leader)/l.block)) 32768 u 1 true .cta))
    (hSkip : ∀ lane < 32, lane ≠ leader.val → ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (done.state lane) u ∧
      At u (site+1) (F lane)) :
    ∃ next : SchedulerWarpReached l X g (site+1) F shuffles votes ends,
      (∀ lane < 32, next.pos lane =
        if lane = leader.val then done.pos lane+1 else done.pos lane) ∧
      X.get (warpLane l g leader,done.pos leader) =
        some ⟨site,.arrive (obj (g/l.block)) 32768 1 true .cta⟩ := by
  let thread := warpLane l g leader
  let j := done.pos leader
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨s,u,hPc,hU,hn⟩ := hLead
  let loc := obj (thread/l.block)
  let event := Event.mk s.pc (.arrive loc 32768 1 true .cta)
  have hl := (done.localSteps leader leader.isLt).trans hn.steps
  have he : EStep kernel Assumptions.all l thread s event (some u) := ⟨_,hn.stop,rfl,rfl⟩
  have hSame := (Step.sameWarp_lane hBlock hg leader.isLt).1
  have hPast := done.recorded leader leader.isLt
  have hMore : j < (X.tr thread).length := by
    by_contra! hLe
    have hEq := Nat.le_antisymm (done.bounded leader leader.isLt) hLe
    have hStarted : X.tr thread ≠ [] := fun h => by
      have hPos := done.positive leader leader.isLt
      rw [h,List.length_nil] at hEq
      omega
    rw [List.take_of_length_le hLe] at hPast
    apply hMax.not_grows
    refine Step.object_counted_extension_silent hMax.1 (by trivial) hSame.1.2.1 (.inl hStarted)
      (done.released leader leader.isLt hEq) hPast hl he
      ⟨trivial,fun _ h => by cases h⟩ (by trivial)
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rfl (mb := loc) (act := .arrive 1 32768)
      (fun _ _ h => by cases h) ?_ ?_
    · intro target
      by_cases h : target = loc
      · subst target
        simp [objectAction,snoc_get_new,event]
      · simp [objectAction,snoc_get_new,event,h,Ne.symm h]
    · intro rec
      exact Assumptions.wfStep.quiet hMax.1
        (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  have hn' : Next kernel Assumptions.all l thread (done.before leader) s
      (.arrive loc 32768 u 1 true .cta) := ⟨hl,hn.stop⟩
  obtain ⟨_,_,hGet,⟨rfl,hReturn⟩,hRest⟩ := hn'.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) (done.continuation leader leader.isLt)
    (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
  have hTail' : Run kernel Assumptions.all l thread u ((X.tr thread).drop (j+1))
      (ends leader) := by
    rw [← Option.some.inj hReturn]
    exact hRest
  have hPast' : Run kernel Assumptions.all l thread {} ((X.tr thread).take (j+1)) (some u) := by
    rw [List.take_succ_eq_append_getElem hMore,(List.getElem?_eq_some_iff.mp hGet).2]
    exact hPast.snoc hl he
  have hCta : g/l.block = thread/l.block := hSame.1.2.2
  have hIssue : X.get (thread,j) =
      some ⟨site,.arrive (obj (g/l.block)) 32768 1 true .cta⟩ := by
    rw [hCta,← hPc]
    exact hGet
  have hEvery (lane : Nat) (hl : lane < 32) :
      ∃ pos before state,
        let th := warpLane l g lane
        0 < pos ∧ pos ≤ (X.tr th).length ∧ (pos = (X.tr th).length → Step.Released l X th) ∧
        Run kernel Assumptions.all l th {} ((X.tr th).take pos) (some before) ∧
        Run kernel Assumptions.all l th before ((X.tr th).drop pos) (ends lane) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l th) before state ∧
        At state (site+1) (F lane) ∧
        ((X.tr th).take pos).countP Execution.isShfl = shuffles ∧
        ((X.tr th).take pos).countP isFullWarpVote = votes ∧
        pos = if lane = leader.val then done.pos lane+1 else done.pos lane := by
    by_cases hLeader : lane = leader.val
    · subst lane
      have hs : ((X.tr thread).take (j+1)).countP Execution.isShfl = shuffles :=
        (countP_take_succ_false hGet rfl).trans (done.ordinals.shfl leader leader.isLt)
      have hv : ((X.tr thread).take (j+1)).countP isFullWarpVote = votes :=
        (countP_take_succ_false hGet rfl).trans (done.ordinals.vote leader leader.isLt)
      exact ⟨j+1,u,u,Nat.succ_pos j,len_of_get hGet,
        releasedIfLast hGet (by intro h; cases h),hPast',hTail',.refl,hU,hs,hv,
        by simp [j]⟩
    · obtain ⟨w,hw,hW⟩ := hSkip lane hl hLeader
      exact ⟨done.pos lane,done.before lane,w,done.positive lane hl,done.bounded lane hl,
        done.released lane hl,done.recorded lane hl,done.continuation lane hl,
        (done.localSteps lane hl).trans hw,hW,done.ordinals.shfl lane hl,
        done.ordinals.vote lane hl,by simp [hLeader]⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! pos before state hPos hBound hRelease hPrefix hTail hStep hFrame hSh hV hEq
    using hEvery
  exact ⟨⟨⟨pos,before,state,⟨hSh,hV⟩,hTail,hStep,hFrame⟩,hPos,hBound,hRelease,hPrefix⟩,
    hEq,hIssue⟩

/-- The elected input issuer records its tensor command at its own cursor, and every other
lane keeps its cursor. -/
theorem inputBoxIssueAtElection {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes col row head barrier policy election endPc : Nat} (hg : g < l.threads)
    (site : Fin 14)
    (hCol : col < 2^31) (hRow : row < 2^31) (hHead : head < 2^31)
    (hBar : barrier+(inputSite site).barrierOffset < 2^32) (hAlign : barrier%8 = 0)
    (hPolicy : policy < 2^64)
    (hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite site))
      (inputCoordinate col row head))
    (hEndPc : (inputSite site).pc+1 = endPc) {F : Nat → List (Nat × Value)}
    {G : Nat → List (Nat × Value)} {ends : Nat → Option TState} (leader : Fin 32)
    (done : SchedulerWarpReached l X g election G shuffles votes ends)
    (hIssueFrame : ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g leader))
        (done.state leader) u ∧
      At u (inputSite site).pc
        (inputSiteFacts l (inputSite site) col row head barrier policy ++ F leader))
    (hSkip : ∀ lane < 32, lane ≠ leader.val → ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (done.state lane) u ∧
      At u endPc (F lane)) :
    ∃ next : SchedulerWarpReached l X g endPc F shuffles votes ends,
      (∀ lane < 32, next.pos lane =
        if lane = leader.val then done.pos lane+1 else done.pos lane) ∧
      X.get (warpLane l g leader,done.pos leader) =
        some ⟨(inputSite site).pc,.tensorIssue (inputMapAddress p (inputSite site))
          (inputSiteSpec p l (warpLane l g leader) (inputSite site) col row head barrier)⟩ := by
  let thread := warpLane l g leader
  let j := done.pos leader
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨u,hLocal,hU⟩ := hIssueFrame
  have hSame := (Step.sameWarp_lane hBlock hg leader.isLt).1
  obtain ⟨hIssue,hPast,hRest⟩ := loaderInputOfMaximal hp hMax site hSame.1.2.1 hCol hRow hHead
    hBar hAlign hPolicy hBox (hU.mono ((holds_append ..).mp hU.2.2.2.2).1)
    (done.recorded leader leader.isLt) (done.continuation leader leader.isLt)
    ((done.localSteps leader leader.isLt).trans hLocal)
    (done.positive leader leader.isLt) (done.bounded leader leader.isLt)
    (done.released leader leader.isLt)
  have hEnd := ((hU.mono ((holds_append ..).mp hU.2.2.2.2).2).next)
  rw [hEndPc] at hEnd
  have hEvery (lane : Nat) (hl : lane < 32) :
      ∃ pos before state,
        let th := warpLane l g lane
        0 < pos ∧ pos ≤ (X.tr th).length ∧ (pos = (X.tr th).length → Step.Released l X th) ∧
        Run kernel Assumptions.all l th {} ((X.tr th).take pos) (some before) ∧
        Run kernel Assumptions.all l th before ((X.tr th).drop pos) (ends lane) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l th) before state ∧
        At state endPc (F lane) ∧
        ((X.tr th).take pos).countP Execution.isShfl = shuffles ∧
        ((X.tr th).take pos).countP isFullWarpVote = votes ∧
        pos = if lane = leader.val then done.pos lane+1 else done.pos lane := by
    by_cases hLeader : lane = leader.val
    · subst lane
      have hs : ((X.tr thread).take (j+1)).countP Execution.isShfl = shuffles :=
        (countP_take_succ_false hIssue rfl).trans (done.ordinals.shfl leader leader.isLt)
      have hv : ((X.tr thread).take (j+1)).countP isFullWarpVote = votes :=
        (countP_take_succ_false hIssue rfl).trans (done.ordinals.vote leader leader.isLt)
      exact ⟨j+1,next u,next u,Nat.succ_pos j,len_of_get hIssue,
        releasedIfLast hIssue (by intro h; cases h),hPast,hRest,.refl,hEnd,hs,hv,
        by simp [j]⟩
    · obtain ⟨w,hw,hW⟩ := hSkip lane hl hLeader
      exact ⟨done.pos lane,done.before lane,w,done.positive lane hl,done.bounded lane hl,
        done.released lane hl,done.recorded lane hl,done.continuation lane hl,
        (done.localSteps lane hl).trans hw,hW,done.ordinals.shfl lane hl,
        done.ordinals.vote lane hl,by simp [hLeader]⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! pos before state hPos hBound hRelease hPrefix hTail hStep hFrame hSh hV hEq
    using hEvery
  exact ⟨⟨⟨pos,before,state,⟨hSh,hV⟩,hTail,hStep,hFrame⟩,hPos,hBound,hRelease,hPrefix⟩,
    hEq,hIssue⟩

end PTX.Kernels.TmlFa4Fwd.Loader
