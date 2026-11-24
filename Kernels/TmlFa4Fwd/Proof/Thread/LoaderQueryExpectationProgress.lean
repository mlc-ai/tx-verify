-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryStartProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerElectProgress
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Lemmas.Kernel.ProgressDescent
import Lemmas.Protocol.ElectCount
import Lemmas.Step.DrainInOrder
import Lemmas.Step.Object

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.AsyncCopy
open Prologue Epilogue Thread.Output

private def queryElectReturn (l : Launch) (g : Nat) (t : TState) (leader : Nat) : TState :=
  next (setReg (setReg t 1891 (b32 leader)) 140 (.pred (laneOf l g == leader)))

private theorem queryElectOut {l : Launch} {g : Nat} {s : TState}
    (hPc : s.pc = 682) (hFault : s.fault = none) :
    out kernel Assumptions.all l g s = .ev (.elect 4294967295 (queryElectReturn l g s)) := by
  rw [loaderOutCore (by rw [hPc]; decide) (by rw [hPc]; decide)]
  rw [out_event hFault (by rw [hPc]; exact Flow.code_682) rfl rfl]
  have hMask : readBits l g s 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hMember : electMember 4294967295 (laneOf l g) := PTX.electMember_full l g
  change Out.ev (electTmpl l g s (some 1891) 140 (.imm (-1))) = _
  simp only [electTmpl,hMask,show (4294967295#64).toNat = 4294967295 from rfl,hMember,↓reduceIte]
  rfl

set_option maxRecDepth 100000 in
private theorem afterQueryElectionCode :
    (kernel.code.drop 683).all (fun i => Thread.staysPastEvent 683 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterQueryElectionSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (683 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 3000 in
private theorem afterQueryElection {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : 683 ≤ s.pc) : 683 ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit afterQueryElectionCode
      afterQueryElectionSegments hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit afterQueryElectionCode
      afterQueryElectionSegments hs (.inr ⟨_,rfl,he⟩))

private theorem noEarlierQueryElection {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events t) (ht : t.pc = 682) :
    ∀ mask inst leader, (⟨682,.elect mask inst leader⟩ : Event) ∉ events := by
  induction h with
  | refl => simp
  | tau _ _ ih => exact ih ht
  | @event s v t es e he hs ih =>
    intro mask inst leader hm
    rcases List.mem_cons.mp hm with hEq | hTail
    · have hPc : s.pc = 682 := (estep_source_pc he).symm.trans (congrArg Event.pc hEq).symm
      cases hFault : s.fault with
      | none =>
        obtain ⟨tm,hOut,hFire⟩ := he
        rw [queryElectOut hPc hFault,Out.ev.injEq] at hOut
        subst tm
        obtain ⟨_,lead,_,hRet⟩ := hFire
        have hV := congrArg TState.pc (Option.some.inj hRet)
        change v.pc = s.pc+1 at hV
        have hAfter := afterQueryElection hs (by omega)
        omega
      | some f =>
        obtain ⟨tm,hOut,hFire⟩ := he
        simp only [out,hFault,Out.ev.injEq] at hOut
        subst tm
        cases hFire.2
    · exact ih ht _ _ _ hTail

private def electedQueryFacts (l : Launch) (lane leader : Nat) : List (Nat × Value) :=
  [(140,.pred (lane == leader)),(2535,b32 l.sharedBase)]

private theorem electedQueryFrame {l : Launch} {g leader : Nat} {s : TState}
    (hs : At s 682 (primingQueryWaitFacts l)) :
    At (queryElectReturn l g s leader) 683 (electedQueryFacts l (laneOf l g) leader) := by
  refine ⟨by simp [queryElectReturn,next,setReg,hs.1],hs.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
  have hBase := hs.2.2.2.2.2.2.1
  simp [Holds,electedQueryFacts,queryElectReturn,next,setReg,hBase]

private theorem queryExpectNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} (hs : At s 683 [(140,.pred true),(2535,b32 l.sharedBase)]) :
    ∃ t u, t.pc = 686 ∧ At u 687 [(2535,b32 l.sharedBase)] ∧
      Next kernel Assumptions.all l g s t
        (.arrive (queryObject l (g/l.block) 0) 32768 u 1 true .cta) := by
  let F := [(2535,b32 l.sharedBase)]
  have hNot : Seg kernel [] l g 1 683 ((140,.pred true) :: F) 684 ((141,.pred false) :: F) := by
    intro s hs
    dsimp [F] at *
    seg_fp hs using rfl
  obtain ⟨v,hv,hV⟩ := hNot s hs
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) Flow.code_684 false hV
    hV.2.2.2.2.1 (by simp)
  have hLoad : Seg kernel [] l g 1 685 F 686 ((1892,b32 32768) :: F) := by
    intro z hz
    dsimp [F] at *
    seg_fp hz using rfl
  obtain ⟨t,ht,hT⟩ := hLoad w (hW.mono hW.2.2.2.2.2)
  have hv' := (loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by decide) hv).1
  have hw' := (loaderLinear (regs := []) (by decide) (by decide) hV.1
    (by simp) (by decide) hw).1
  have ht' := (loaderLinear (regs := []) (by decide) (by decide) hW.1
    (by simp) (by decide) ht).1
  let loc := queryObject l (g/l.block) 0
  let u := next (mbarStateDest t (some 7579))
  have hOut : out kernel Assumptions.all l g t = .ev (.arrive loc 32768 u 1 true .cta) := by
    rw [loaderOutCore (by rw [hT.1]; decide) (by rw [hT.1]; decide)]
    rw [out_event hT.2.2.2.1 (by rw [hT.1]; exact Flow.code_686) rfl rfl]
    have hBase : l.sharedBase+0 < 2^32 := by have := hp.shared.2.1; omega
    have hAlign : l.sharedBase%8 = 0 := by have := hp.shared.1; omega
    have hEff : effAddr l g t .shared 2535 0 = .ok loc :=
      effAddr_b32_off hT.2.2.2.2.2.1 hBase
    have hLoc : mbarLoc l g t 2535 0 = .ok loc := by
      simp [mbarLoc,hEff,loc,queryObject,hAlign,bind,Except.bind,pure,Except.pure]
    have hOne : readBits l g t 32 (.imm 1) = .ok 1#64 := rfl
    simp [eventTmpl,widenMbarScope,tmaTmpl,hLoc,readBits_b32 hT.2.2.2.2.1 (by decide),
      hOne,u,bind,Except.bind,pure,Except.pure,ofExec]
  have hU : At u 687 F := by
    refine ⟨by change t.pc+1 = 687; rw [hT.1],hT.2.1,hT.2.2.1,hT.2.2.2.1,?_⟩
    simp [Holds,F,u,mbarStateDest,next,hT.2.2.2.2.2.1]
  exact ⟨t,u,hT.1,hU,run_rtg (run_comp (run_comp hv' hw') ht'),hOut⟩

private theorem querySkipExpectation {l : Launch} {g : Nat} {s : TState}
    (hs : At s 683 [(140,.pred false),(2535,b32 l.sharedBase)]) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 687 [(2535,b32 l.sharedBase)] := by
  let F := [(2535,b32 l.sharedBase)]
  have hNot : Seg kernel [] l g 1 683 ((140,.pred false) :: F) 684 ((141,.pred true) :: F) := by
    intro t ht
    dsimp [F] at *
    seg_fp ht using rfl
  obtain ⟨v,hv,hV⟩ := hNot s hs
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) Flow.code_684 true hV
    hV.2.2.2.2.1 (by simp)
  have hv' := (loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by decide) hv).1
  have hw' := (loaderLinear (regs := []) (by decide) (by decide) hV.1
    (by simp) (by decide) hw).1
  exact ⟨w,run_rtg (run_comp hv' hw'),hW.mono hW.2.2.2.2.2⟩

/-- A reached first query cursor at the first box election, after the expectation issue. -/
abbrev PrimingQueryBoxesReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 687 (fun _ => [(2535,b32 l.sharedBase)])
    shuffles votes ends)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

/-- Record an elected input expectation and rejoin the warp after the guarded issue. -/
theorem expectationOfElectedWarp {g entry site shuffles votes : Nat} (hg : g < l.threads)
    (obj : Nat → Loc) {F G : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (done : SchedulerWarpReached l X g entry G shuffles votes ends) (leader : Fin 32)
    (hLead : ∃ s u, s.pc = site ∧ At u (site+1) (F leader) ∧
      Next kernel Assumptions.all l (warpLane l g leader) (done.state leader) s
        (.arrive (obj ((warpLane l g leader)/l.block)) 32768 u 1 true .cta))
    (hSkip : ∀ lane < 32, lane ≠ leader.val → ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (done.state lane) u ∧
      At u (site+1) (F lane)) :
    Nonempty (SchedulerWarpReached l X g (site+1) F shuffles votes ends) ∧
      ∃ issue, X.get issue =
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
        ((X.tr th).take pos).countP isFullWarpVote = votes := by
    by_cases hLeader : lane = leader.val
    · subst lane
      have hs : ((X.tr thread).take (j+1)).countP Execution.isShfl = shuffles :=
        (countP_take_succ_false hGet rfl).trans (done.ordinals.shfl leader leader.isLt)
      have hv : ((X.tr thread).take (j+1)).countP isFullWarpVote = votes :=
        (countP_take_succ_false hGet rfl).trans (done.ordinals.vote leader leader.isLt)
      exact ⟨j+1,u,u,Nat.succ_pos j,len_of_get hGet,
        releasedIfLast hGet (by intro h; cases h),hPast',hTail',.refl,hU,hs,hv⟩
    · obtain ⟨w,hw,hW⟩ := hSkip lane hl hLeader
      exact ⟨done.pos lane,done.before lane,w,done.positive lane hl,done.bounded lane hl,
        done.released lane hl,done.recorded lane hl,done.continuation lane hl,
        (done.localSteps lane hl).trans hw,hW,done.ordinals.shfl lane hl,done.ordinals.vote lane hl⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! pos before state hPos hBound hRelease hPrefix hTail hStep hFrame hSh hV using hEvery
  exact ⟨⟨⟨⟨pos,before,state,⟨hSh,hV⟩,hTail,hStep,hFrame⟩,
    hPos,hBound,hRelease,hPrefix⟩⟩,(thread,j),hIssue⟩

/-- Record an elected query expectation and rejoin the warp after the guarded issue. -/
theorem queryExpectationOfElectedWarp {g entry site shuffles votes : Nat} (hg : g < l.threads)
    (stage : Fin 2) {F G : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (done : SchedulerWarpReached l X g entry G shuffles votes ends) (leader : Fin 32)
    (hLead : ∃ s u, s.pc = site ∧ At u (site+1) (F leader) ∧
      Next kernel Assumptions.all l (warpLane l g leader) (done.state leader) s
        (.arrive (queryObject l ((warpLane l g leader)/l.block) stage) 32768 u 1 true .cta))
    (hSkip : ∀ lane < 32, lane ≠ leader.val → ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (done.state lane) u ∧
      At u (site+1) (F lane)) :
    Nonempty (SchedulerWarpReached l X g (site+1) F shuffles votes ends) ∧
      ∃ issue, X.get issue =
        some ⟨site,.arrive (queryObject l (g/l.block) stage) 32768 1 true .cta⟩ :=
  expectationOfElectedWarp hp hMax hg (fun cta => queryObject l cta stage) done leader hLead hSkip

/-- Once Q0's empty acquire succeeds, the elected loader lane records the actual expectation. -/
theorem primingQueryBoxEntryOfMaximal {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState} (hConsumed : PrimingQueryEmptyConsumed l X g shuffles votes ends) :
    PrimingQueryBoxesReached l X g shuffles votes ends ∧
      ∃ issue, X.Arrive issue (queryObject l (g/l.block) 0) 32768 1 true .cta := by
  obtain ⟨cur⟩ := hConsumed
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hFirst (lane : Nat) (hl : lane < 32) (j : Nat) (hj : j < cur.pos lane)
      (mask inst leader : Nat) : ¬ X.Elect (warpLane l g lane,j) 682 mask inst leader := by
    intro he
    have hTrace := (cur.recorded lane hl).returning_reach.append
      (TraceReach.of_local (cur.localSteps lane hl))
    have hGet : ((X.tr (warpLane l g lane)).take (cur.pos lane))[j]? =
        some ⟨682,.elect mask inst leader⟩ := by rwa [List.getElem?_take_of_lt hj]
    exact noEarlierQueryElection hTrace (cur.checkpoint lane hl).1 mask inst leader
      (List.mem_append_left [] (List.mem_of_getElem? hGet))
  let post (lane : Nat) := queryElectReturn l (warpLane l g lane) (cur.state lane)
  obtain ⟨leader,done,_⟩ := cur.consumeElection hp hMax hg post (electedQueryFacts l)
    hFirst (fun lane hl =>
      queryElectOut (cur.checkpoint lane hl).1 (cur.checkpoint lane hl).2.2.2.1)
    (fun lane hl leader => by
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      have hFrame := electedQueryFrame (g := warpLane l g lane)
        (leader := leader) (cur.checkpoint lane hl)
      rw [hLane] at hFrame
      exact hFrame)
  obtain ⟨hRun,issue,he⟩ := queryExpectationOfElectedWarp hp hMax hg 0
    (site := 686) (F := fun _ => [(2535,b32 l.sharedBase)]) done leader
    (by
      apply queryExpectNext hp (g := warpLane l g leader)
      simpa [electedQueryFacts] using done.checkpoint leader leader.isLt)
    (fun lane hl hLeader => by
      apply querySkipExpectation (g := warpLane l g lane)
      simpa only [electedQueryFacts,beq_eq_false_iff_ne.mpr hLeader] using done.checkpoint lane hl)
  exact ⟨hRun,issue,686,he⟩

end PTX.Kernels.TmlFa4Fwd.Loader
