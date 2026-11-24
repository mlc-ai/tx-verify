-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryExpectationProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
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
import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.Thread.QueryDrainRelease
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.MBarrier PTX.AsyncCopy
open Prologue Epilogue Thread.Output

noncomputable section

/-- Registers retained at the opening second-query boundary. -/
def secondQueryBaseFrame (l : Launch) : List (Nat × Value) :=
  [(2535,b32 l.sharedBase)]

private def secondQueryWaitSite : DrainWaitSite := ⟨730,9609,1907,1908⟩

private def secondQueryWaitFrame (l : Launch) : List (Nat × Value) :=
  [(1907,b32 (l.sharedBase+24)),(1908,b32 1)] ++ secondQueryBaseFrame l

private theorem secondQueryWaitCode : LoaderWaitCode secondQueryWaitSite :=
  ⟨Flow.code_730,Flow.code_731,Flow.code_732⟩

private theorem secondQueryWaitLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 728 (secondQueryBaseFrame l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 730 (secondQueryWaitFrame l) := by
  have hf : l.sharedBase+24 < 2^32 := by have := hp.shared.2.1; omega
  have hSeg : Seg kernel [] l g 2 728 (secondQueryBaseFrame l) 730 (secondQueryWaitFrame l) := by
    intro s hs
    dsimp [secondQueryWaitFrame,secondQueryBaseFrame] at *
    seg_fp hs using first | rfl | norm_bits [Nat.mod_eq_of_lt hf]
  obtain ⟨u,hu,hU⟩ := hSeg t ht
  have hLocal := (loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu).1
  exact ⟨u,run_rtg hLocal,hU⟩

private def secondQueryElectReturn (l : Launch) (g : Nat) (t : TState) (leader : Nat) : TState :=
  next (setReg (setReg t 1909 (b32 leader)) 152 (.pred (laneOf l g == leader)))

private theorem secondQueryElectOut {l : Launch} {g : Nat} {s : TState}
    (hPc : s.pc = 733) (hFault : s.fault = none) :
    out kernel Assumptions.all l g s = .ev (.elect 4294967295 (secondQueryElectReturn l g s)) := by
  rw [loaderOutCore (by rw [hPc]; decide) (by rw [hPc]; decide)]
  rw [out_event hFault (by rw [hPc]; exact Flow.code_733) rfl rfl]
  have hMask : readBits l g s 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hMember : electMember 4294967295 (laneOf l g) := PTX.electMember_full l g
  change Out.ev (electTmpl l g s (some 1909) 152 (.imm (-1))) = _
  simp only [electTmpl,hMask,show (4294967295#64).toNat = 4294967295 from rfl,hMember,↓reduceIte]
  rfl

private theorem secondQueryElectFresh {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events t) (ht : t.pc = 733) :
    ∀ mask inst leader, (⟨733,.elect mask inst leader⟩ : Event) ∉ events := by
  have hFloor {v w : TState} {es : List Event}
      (hRun : TraceReach kernel Assumptions.all l g v es w) (hv : 734 ≤ v.pc) :
      734 ≤ w.pc := by
    induction hRun with
    | refl => exact hv
    | tau hs _ ih =>
      exact ih (Thread.eventTailStepOfAudit (by decide +kernel) (by decide +kernel) hv
        (.inl ⟨rfl,hs⟩))
    | event he _ ih =>
      exact ih (Thread.eventTailStepOfAudit (by decide +kernel) (by decide +kernel) hv
        (.inr ⟨_,rfl,he⟩))
  induction h with
  | refl => simp
  | tau _ _ ih => exact ih ht
  | @event s v t es e he hs ih =>
    intro mask inst leader hm
    rcases List.mem_cons.mp hm with hEq | hTail
    · have hPc : s.pc = 733 := (estep_source_pc he).symm.trans (congrArg Event.pc hEq).symm
      cases hFault : s.fault with
      | none =>
        obtain ⟨tm,hOut,hFire⟩ := he
        rw [secondQueryElectOut hPc hFault,Out.ev.injEq] at hOut
        subst tm
        obtain ⟨_,lead,_,hRet⟩ := hFire
        have hV := congrArg TState.pc (Option.some.inj hRet)
        change v.pc = s.pc+1 at hV
        have hAfter := hFloor hs (by omega)
        omega
      | some f =>
        obtain ⟨tm,hOut,hFire⟩ := he
        simp only [out,hFault,Out.ev.injEq] at hOut
        subst tm
        cases hFire.2
    · exact ih ht _ _ _ hTail

private theorem secondQueryBranch {l : Launch} {g : Nat} {s : TState} (lead : Bool)
    (hs : At s 734 ((152,.pred lead) :: secondQueryBaseFrame l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if lead then 736 else 738) (secondQueryBaseFrame l) := by
  let F := secondQueryBaseFrame l
  have hNot : Seg kernel [] l g 1 734 ((152,.pred lead) :: F) 735 ((153,.pred (!lead)) :: F) := by
    intro s hs
    let v := next (setReg s 153 (.pred (!lead)))
    have hFresh : ∀ pair ∈ (152,.pred lead) :: F, pair.1 ≠ 153 := by
      simp [F,secondQueryBaseFrame]
    have hAt := hs.set (v := .pred (!lead)) hFresh
    refine ⟨v,?_,hAt.mono ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.2⟩⟩
    apply run_local Flow.code_734 rfl hs
    rw [execLocalA_nil]
    change execInt l g s ⟨.not,.pred,false,[some 153],[.reg 152]⟩ = _
    simp [execInt,DType.width,readPred,readReg,hs.2.2.2.2.1,v,
      bind,Except.bind,pure,Except.pure]
  obtain ⟨v,hv,hV⟩ := hNot s hs
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) Flow.code_735 (!lead) hV
    hV.2.2.2.2.1 (by simp)
  have hv' := (loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by decide) hv).1
  have hw' := (loaderLinear (regs := []) (by decide) (by decide) hV.1
    (by simp) (by decide) hw).1
  exact ⟨w,run_rtg (run_comp hv' hw'),by
    cases lead <;> exact hW.mono hW.2.2.2.2.2⟩

private theorem secondQueryExpectNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} (hs : At s 734 ((152,.pred true) :: secondQueryBaseFrame l)) :
    ∃ t u, t.pc = 737 ∧ At u 738 (secondQueryBaseFrame l) ∧
      Next kernel Assumptions.all l g s t
        (.arrive (queryObject l (g/l.block) 1) 32768 u 1 true .cta) := by
  let F := secondQueryBaseFrame l
  obtain ⟨w,hw,hW⟩ := secondQueryBranch (g := g) true hs
  have hLoad : Seg kernel [] l g 1 736 F 737 ((1910,b32 32768) :: F) := by
    intro z hz
    dsimp [F,secondQueryBaseFrame] at *
    seg_fp hz using rfl
  obtain ⟨t,ht,hT⟩ := hLoad w hW
  have ht' := (loaderLinear (regs := []) (by decide) (by decide) hW.1
    (by simp) (by decide) ht).1
  let loc := queryObject l (g/l.block) 1
  let u := next (mbarStateDest t (some 7589))
  have hOut : out kernel Assumptions.all l g t = .ev (.arrive loc 32768 u 1 true .cta) := by
    rw [loaderOutCore (by rw [hT.1]; decide) (by rw [hT.1]; decide)]
    rw [out_event hT.2.2.2.1 (by rw [hT.1]; exact Flow.code_737) rfl rfl]
    have hBase : l.sharedBase+8 < 2^32 := by have := hp.shared.2.1; omega
    have hAlign : (l.sharedBase+8)%8 = 0 := by have := hp.shared.1; omega
    have hEff : effAddr l g t .shared 2535 8 = .ok loc :=
      effAddr_b32_off hT.2.2.2.2.2.1 hBase
    have hLoc : mbarLoc l g t 2535 8 = .ok loc := by
      simp [mbarLoc,hEff,loc,queryObject,hAlign,bind,Except.bind,pure,Except.pure]
    have hOne : readBits l g t 32 (.imm 1) = .ok 1#64 := rfl
    simp [eventTmpl,widenMbarScope,tmaTmpl,hLoc,readBits_b32 hT.2.2.2.2.1 (by decide),
      hOne,u,bind,Except.bind,pure,Except.pure,ofExec]
  have hU : At u 738 F := by
    refine ⟨by change t.pc+1 = 738; rw [hT.1],hT.2.1,hT.2.2.1,hT.2.2.2.1,?_⟩
    simp [Holds,F,secondQueryBaseFrame,u,mbarStateDest,next,hT.2.2.2.2.2.1]
  exact ⟨t,u,hT.1,hU,hw.trans (run_rtg ht'),hOut⟩

/-- A reached post-Bias cursor for the opening second query. -/
abbrev OpeningSecondQueryReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 728 (fun _ => secondQueryBaseFrame l) shuffles votes ends)

/-- The second query's elected loader is ready to issue its two boxes. -/
abbrev OpeningSecondQueryBoxesReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 738 (fun _ => secondQueryBaseFrame l) shuffles votes ends)

/-- After Bias0's initial subboxes the loader crosses the second query empty wait and
records its actual transaction expectation. -/
theorem openingSecondQueryExpectedFromCursorOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (hStart : OpeningSecondQueryReached l X g shuffles votes ends)
    (hReady : ∀ lane < 32, Thread.Loader.OpeningSecondQueryBlocked l X (warpLane l g lane) →
      let log := X.objects (Thread.Loader.secondQueryEmpty l (g / l.block))
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    OpeningSecondQueryBoxesReached l X g shuffles votes ends ∧
      ∃ issue, Thread.Loader.StageOneExpectation l X (g / l.block) issue false := by
  obtain ⟨start⟩ := hStart
  obtain ⟨cur⟩ := start.advanceLocal (pc' := 730) (G := fun _ => secondQueryWaitFrame l)
    (fun lane hl => secondQueryWaitLocal hp (g := warpLane l g lane) (start.checkpoint lane hl))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hAddr : l.sharedBase+24 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+24)%8 = 0 := by have := hp.shared.1; omega
  obtain ⟨atElection⟩ := loaderWarpWaitOfReadyLast hMax hg hBlock secondQueryWaitCode
    (by decide) hAddr hAlign cur (fun _ _ => by simp [secondQueryWaitFrame,secondQueryWaitSite,
      secondQueryBaseFrame]) (fun _ _ => by simp [secondQueryWaitFrame,secondQueryWaitSite])
    (fun _ _ => by simp [secondQueryWaitFrame,secondQueryWaitSite])
    (fun lane hl {_ _} hRun hLocal hAt => hReady lane hl ⟨_,_,hRun,hLocal,hAt.1⟩)
  let post := fun lane => secondQueryElectReturn l (warpLane l g lane) (atElection.state lane)
  let frame := fun (lane leader : Nat) => (152,.pred (lane == leader)) :: secondQueryBaseFrame l
  have hFresh (lane : Nat) (hl : lane < 32) (j : Nat) (hj : j < atElection.pos lane)
      (mask inst leader : Nat) : ¬ X.Elect (warpLane l g lane,j) 733 mask inst leader := by
    intro he
    have hTrace := (atElection.recorded lane hl).returning_reach.append
      (TraceReach.of_local (atElection.localSteps lane hl))
    have hGet : ((X.tr (warpLane l g lane)).take (atElection.pos lane))[j]? =
        some ⟨733,.elect mask inst leader⟩ := by rwa [List.getElem?_take_of_lt hj]
    exact secondQueryElectFresh hTrace (atElection.checkpoint lane hl).1 mask inst leader
      (List.mem_append_left [] (List.mem_of_getElem? hGet))
  obtain ⟨leader,elected,_⟩ := atElection.consumeElection hp hMax hg post frame
    hFresh (fun lane hl => secondQueryElectOut (atElection.checkpoint lane hl).1
      (atElection.checkpoint lane hl).2.2.2.1) (fun lane hl leader => by
      have hAt := atElection.checkpoint lane hl
      have hLane : laneOf l (warpLane l g lane) = lane :=
        (Step.sameWarp_lane hBlock hg hl).2
      have hBase := hAt.2.2.2.2.2.2.1
      exact ⟨by simp [post,secondQueryElectReturn,next,setReg,hAt.1,secondQueryWaitSite],
        hAt.2.1,hAt.2.2.1,hAt.2.2.2.1,by
          simp [Holds,frame,post,secondQueryElectReturn,next,setReg,
            secondQueryBaseFrame,hBase,hLane]⟩)
  obtain ⟨hWarp,issue,he⟩ := queryExpectationOfElectedWarp hp hMax hg 1
    (site := 737) (F := fun _ => secondQueryBaseFrame l) elected leader
    (by
      apply secondQueryExpectNext hp (g := warpLane l g leader)
      simpa [frame,secondQueryWaitSite] using elected.checkpoint leader leader.isLt)
    (fun lane hl hLeader => by
      have hAt : At (elected.state lane) 734 ((152,.pred false) :: secondQueryBaseFrame l) := by
        simpa only [frame,secondQueryWaitSite,beq_eq_false_iff_ne.mpr hLeader] using
          elected.checkpoint lane hl
      exact secondQueryBranch (g := warpLane l g lane) false hAt)
  exact ⟨hWarp,issue,he⟩

/-- After Bias0's initial subboxes the loader crosses the second query empty wait and
records its actual transaction expectation. -/
theorem openingSecondQueryExpectedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (hStart : OpeningSecondQueryReached l X g shuffles votes ends)
    (hReady : let log := X.objects (Thread.Loader.secondQueryEmpty l (g / l.block))
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    OpeningSecondQueryBoxesReached l X g shuffles votes ends ∧
      ∃ issue, Thread.Loader.StageOneExpectation l X (g / l.block) issue false :=
  openingSecondQueryExpectedFromCursorOfMaximal hp hMax hg hStart (fun _ _ _ => hReady)

/-- A counter update that returns the second query observes an earlier actual query acquisition. -/
theorem secondQueryReturnRequiresAcquisition {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} {r : Record Ref} (hr : r ∈ X.objects (Thread.Loader.secondQueryEmpty l cta))
    (hUpdate : CounterUpdate r.action) :
    ∃ read ∈ X.objects (queryObject l cta 1), read.reply.waited = some true := by
  obtain ⟨_,_,_,_,_,hReturn,hCta,_,_⟩ := Thread.Loader.queryEmptyUpdateAt hp hX 1 hr hUpdate
  obtain ⟨_,_,_,_,he,_⟩ := Mma.secondQueryWaitBeforeDrain hp hX hReturn
  obtain ⟨rfl,rfl⟩ := Mma.secondQueryPollOperands hp hX he
  obtain ⟨_,record,hRecord,_,_,_,hSuccess⟩ := Thread.Loader.queryPollRecord hp hX
    (stage := 1) he rfl
  rw [hCta] at hRecord
  exact ⟨record,List.mem_of_getElem? hRecord,hSuccess⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
