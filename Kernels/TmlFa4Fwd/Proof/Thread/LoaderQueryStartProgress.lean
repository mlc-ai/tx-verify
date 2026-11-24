-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyPublicationProgress
import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
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
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryDrainRelease
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Barrier
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Kernels.TmlFa4Fwd.Proof.Thread.FirstQueryReadyOperands
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.MBarrier PTX.AsyncCopy
open Prologue Epilogue Thread.Output Thread.Loader

private def preRoleFacts (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(1062,b32 (14+warp.val)),(2535,b32 l.sharedBase),
   (7295,b64 (l.localBase+96)),(7294,b64 (l.localBase+64))]

/-- Register facts selecting the query loader or the direct route to priming V. -/
def loaderRoleFacts (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(123,.pred (warp == 1)),(2535,b32 l.sharedBase),
   (7295,b64 (l.localBase+96)),(7294,b64 (l.localBase+64))]

set_option maxRecDepth 100000 in
private theorem beforeRoleCode (l : Launch) (warp : Fin 2) :
    ((kernel.code.drop 174).take (538-174)).all
      (fun ins => loaderPipelineCutOp 174 538 673 ((preRoleFacts l warp).map Prod.fst) ins.op) =
        true := by fin_cases warp <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterRoleCode (l : Launch) (warp : Fin 2) :
    ((kernel.code.drop 539).take (674-539)).all
      (fun ins => loaderPipelineCutOp 539 674 673 ((loaderRoleFacts l warp).map Prod.fst) ins.op) =
        true := by fin_cases warp <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem beyondCommitCode :
    (kernel.code.drop 674).all (fun ins => Thread.staysPastEvent 674 ins.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem beyondCommitSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some segment => decide (674 ≤ segment.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 3000 in
private theorem beyondCommit {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : 674 ≤ s.pc) :
    674 ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit beyondCommitCode beyondCommitSegments
      hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit beyondCommitCode beyondCommitSegments
      hs (.inr ⟨_,rfl,he⟩))

private theorem queryRoleTest {l : Launch} {g : Nat} {s : TState} (warp : Fin 2)
    (hs : At s 538 (preRoleFacts l warp)) :
    ∃ u, Tau kernel Assumptions.all l g s u ∧ At u 539 (loaderRoleFacts l warp) := by
  have hSeg : Seg kernel [] l g 1 538 (preRoleFacts l warp) 539 (loaderRoleFacts l warp) := by
    fin_cases warp <;> intro t ht <;>
      dsimp [preRoleFacts,loaderRoleFacts] at ht ⊢ <;> seg_fp ht using rfl
  obtain ⟨u,hu,hU⟩ := hSeg s hs
  have hLocal := (loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by decide) hu).1
  exact ⟨u,tauStep_iff.mp (by simpa [run] using hLocal),hU⟩

private theorem queryRoleStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (warp : Fin 2) (hw : WStep kernel Assumptions.all l g s ev u)
    (hs : At s 538 (preRoleFacts l warp)) : At u 539 (loaderRoleFacts l warp) := by
  obtain ⟨v,hTau,hV⟩ := queryRoleTest (g := g) warp hs
  unfold Tau at hTau
  rcases hw with ⟨_,ht⟩ | ⟨_,_,he⟩
  · rw [Tau,hTau,Out.tau.injEq] at ht
    exact ht ▸ hV
  · obtain ⟨tmpl,hOut,_⟩ := he
    rw [hTau] at hOut
    cases hOut

private theorem cleanReturning {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hw : WStep kernel Assumptions.all l g s ev u) : s.fault = none := by
  cases hf : s.fault with
  | none => rfl
  | some fault =>
    rcases hw with ⟨_,ht⟩ | ⟨_,_,he⟩
    · simp [Tau,out,hf] at ht
    · obtain ⟨tmpl,hOut,hFire⟩ := he
      simp only [out,hf,Out.ev.injEq] at hOut
      subst tmpl
      obtain ⟨_,hBad⟩ := hFire
      cases hBad

set_option maxRecDepth 3000 in
private theorem queryRoleToCommit {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    (warp : Fin 2) (hReach : TraceReach kernel Assumptions.all l g s events t)
    (hFinal : t.pc = 673) (hs : 174 ≤ s.pc) (hShape : RingShape s)
    (hFrame : if s.pc ≤ 538 then Holds s.regs (preRoleFacts l warp)
      else Holds s.regs (loaderRoleFacts l warp)) : Holds t.regs (loaderRoleFacts l warp) := by
  have advance {u v : TState} {es : List Event} {ev : Option Event}
      (hRest : TraceReach kernel Assumptions.all l g v es t)
      (hw : WStep kernel Assumptions.all l g u ev v) (hLo : 174 ≤ u.pc) (hShape : RingShape u)
      (hFrame : if u.pc ≤ 538 then Holds u.regs (preRoleFacts l warp)
        else Holds u.regs (loaderRoleFacts l warp)) :
      174 ≤ v.pc ∧ RingShape v ∧
        (if v.pc ≤ 538 then Holds v.regs (preRoleFacts l warp)
          else Holds v.regs (loaderRoleFacts l warp)) := by
    have hLimit : v.pc ≤ 673 := by
      by_contra! hh
      have := beyondCommit hRest (by omega)
      omega
    have hStart : u.pc ≤ 673 := by
      by_contra! hh
      have hv := Thread.eventTailStepOfAudit beyondCommitCode beyondCommitSegments
        (by omega : 674 ≤ u.pc) hw
      omega
    rcases lt_trichotomy u.pc 538 with hEarly | hTest | hLate
    · obtain ⟨hP,hV,hS,hF⟩ := pipelineCutStep (cut := 538) (branch := 673) (by decide)
        (by decide) ⟨hLo,hEarly⟩ (beforeRoleCode l warp) hw hShape
        (by rwa [ite_eq_left hEarly.le] at hFrame)
      have hBound : v.pc ≤ 538 := hV.resolve_right (by omega)
      exact ⟨hP,hS,by simpa only [ite_eq_left hBound]⟩
    · have hAt := pipelineAtCut hTest hShape
        (by rwa [ite_eq_left hTest.le] at hFrame) (cleanReturning hw) ⟨_,Flow.code_538,rfl⟩
      have hV := queryRoleStep warp hw hAt
      rw [hV.1]
      exact ⟨by decide,ringShapeOfAt hV,by simpa using hV.2.2.2.2⟩
    · obtain ⟨hP,_,hS,hF⟩ := pipelineCutStep (lower := 539) (cut := 674) (branch := 673)
        (by decide) (by decide) ⟨by omega,by omega⟩ (afterRoleCode l warp) hw hShape
        (by rwa [ite_eq_right (Nat.not_le_of_lt hLate)] at hFrame)
      exact ⟨by omega,hS,by simpa only [ite_eq_right (by omega : ¬v.pc ≤ 538)]⟩
  induction hReach with
  | @refl t =>
    have hLate : ¬t.pc ≤ 538 := by omega
    simpa only [ite_eq_right hLate] using hFrame
  | tau hStep hRest ih =>
    obtain ⟨hLo,hS,hF⟩ := advance hRest (.inl ⟨rfl,hStep⟩) hs hShape hFrame
    exact ih hFinal hLo hS hF advance
  | event he hRest ih =>
    obtain ⟨hLo,hS,hF⟩ := advance hRest (.inr ⟨_,rfl,he⟩) hs hShape hFrame
    exact ih hFinal hLo hS hF advance


variable {p : Params} {l : Launch}

/-- The first K cursor retains the decoded loader branch choice and shared base. -/
theorem loaderRoleFrameAtKeyCommit {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} (hg : g < l.threads) (warp : Fin 2)
    (hw : warpIndex l g = 14 + warp.val) (hPos : 5 ≤ pos) (hLength : pos ≤ (X.tr g).length)
    {t u : TState} (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) (hu : u.pc = 673)
    : Holds u.regs (loaderRoleFacts l warp) := by
  obtain ⟨start,_,hStart,_,hPast,_⟩ := nonzeroCommonPrefix hp hX hg (by omega) (hPos.trans hLength)
  have hTake : (X.tr g).take 5 ++ ((X.tr g).take pos).drop 5 = (X.tr g).take pos := by
    simpa only [List.take_take,Nat.min_eq_left hPos] using
      List.take_append_drop 5 ((X.tr g).take pos)
  have hReach := (hPast.after_returned_prefix (hTake.symm ▸ hPrefix)).returning_reach.append
    (TraceReach.of_local hSteps)
  have hFrame : Holds start.regs (preRoleFacts l warp) := by
    have hM := hStart.2.2.2.2
    have hReg : start.regs 1062 = some (b32 (warpIndex l g)) := hM.1
    rw [hw] at hReg
    exact ⟨hReg,hM.2.1,holds_mem hM (by simp [nonzeroBarrierFacts,abiFacts]),
      holds_mem hM (by simp [nonzeroBarrierFacts,abiFacts]),trivial⟩
  exact queryRoleToCommit warp hReach hu (by rw [hStart.1]) (ringShapeOfAt hStart) (by
    rw [hStart.1,ite_eq_left (by decide)]
    exact hFrame)

private abbrev queryRoleFacts (l : Launch) := loaderRoleFacts l 0

private theorem queryRoleFrameAtCommit {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hPos : 5 ≤ pos) (hLength : pos ≤ (X.tr g).length) {t u : TState}
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) (hu : u.pc = 673)
    : Holds u.regs (queryRoleFacts l) :=
  loaderRoleFrameAtKeyCommit hp hX hg 0 hw hPos hLength hPrefix hSteps hu

/-- The first query wait retains the shared base needed by its following expectation. -/
def primingQueryWaitFacts (l : Launch) : List (Nat × Value) :=
  [(1889,b32 (l.sharedBase+16)),(1890,b32 1),(2535,b32 l.sharedBase)]

private theorem queryWaitSetup {m : Mem0} (hp : Pre p l m) {g : Nat} {s : TState}
    (hs : At s 675 (queryRoleFacts l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 679 (primingQueryWaitFacts l) := by
  have hNext : Seg kernel [] l g 1 675 (queryRoleFacts l) 676 (queryRoleFacts l) := by
    intro t ht
    have hFresh : ∀ pair ∈ queryRoleFacts l, pair.1 ≠ 7177 := by
      simp [queryRoleFacts,loaderRoleFacts]
    refine ⟨next (setReg t 7177 (b32 1)), ?_, (ht.set hFresh).mono ?_⟩
    · apply run_local Flow.code_675 rfl ht
      rw [execLocalA_nil]
      rfl
    · exact (ht.set (v := b32 1) hFresh).2.2.2.2.2
  obtain ⟨t,ht,hT⟩ := hNext s hs
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g) Flow.code_676
    false hT hT.2.2.2.2.1 (by simp)
  have hBase : l.sharedBase+16 < 2^32 := by have := hp.shared.2.1; omega
  have hAddr : Seg kernel [] l g 2 677 (queryRoleFacts l) 679 (primingQueryWaitFacts l) := by
    intro w hw
    unfold queryRoleFacts at hw
    unfold primingQueryWaitFacts
    seg_fp hw using first | rfl | norm_bits [Nat.mod_eq_of_lt hBase]
  obtain ⟨u,hu,hU⟩ := hAddr v hV
  have ht' := (loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by decide) ht).1
  have hv' := (loaderLinear (regs := []) (by decide) (by decide) hT.1
    (by simp) (by decide) hv).1
  have hu' := (loaderLinear (regs := []) (by decide) (by decide) hV.1
    (List.all_eq_true.mpr (fun _ _ => rfl))
    (by set_option maxRecDepth 100000 in kernel_rfl) hu).1
  exact ⟨u,run_rtg (run_comp (run_comp ht' hv') hu'),hU⟩

/-- The reached cursor at the commit of the first K packet, before both issue events. -/
abbrev PrimingKeyCommitReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  ∃ F, Nonempty (SchedulerWarpReached l X g 673 F shuffles votes ends)

/-- The reached Q0 empty cursor retains the documented address and parity. -/
abbrev PrimingQueryEmptyReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 679
    (fun _ => primingQueryWaitFacts l) shuffles votes ends)

/-- After the first K publication, warp 14 reaches the Q0 empty acquire with its actual operands. -/
theorem primingQueryEmptyCursorOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hSh : 5 ≤ shuffles) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 673 F shuffles votes ends) :
    PrimingQueryEmptyReached l X g shuffles votes ends := by
  obtain ⟨framed⟩ : Nonempty (SchedulerWarpReached l X g 673
      (fun _ => queryRoleFacts l) shuffles votes ends) := by
    apply cur.advanceLocal
    intro lane hl
    let thread := warpLane l g lane
    have hBlock : l.block%32 = 0 := by rw [hp.block]
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hWarp : warpIndex l thread = 14 := hSame.2.symm.trans hw
    have hPos : 5 ≤ cur.pos lane := by
      have hBound : ((X.tr thread).take (cur.pos lane)).countP Execution.isShfl
          ≤ ((X.tr thread).take (cur.pos lane)).length := List.countP_le_length
      rw [cur.ordinals.shfl lane hl,List.length_take] at hBound
      omega
    have hs := cur.checkpoint lane hl
    have hF := queryRoleFrameAtCommit hp hMax.1 hSame.1.2.1 hWarp hPos (cur.bounded lane hl)
      (cur.recorded lane hl) (cur.localSteps lane hl) hs.1
    exact ⟨cur.state lane,.refl,hs.mono hF⟩
  obtain ⟨done,_⟩ := primingKeyCursorAfterArrivalOfMaximal hp hMax hg (by omega) hSh framed
  exact done.advanceLocal (fun lane hl => queryWaitSetup hp (done.checkpoint lane hl))

private def firstQueryEmptyWaitSite : DrainWaitSite := ⟨679,9607,1889,1890⟩

/-- The Q0 empty acquire has completed and the loader is at its following election. -/
abbrev PrimingQueryEmptyConsumed (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 682
    (fun _ => primingQueryWaitFacts l) shuffles votes ends)

/-- A reached Q0 warp crosses its first poll when any still-blocked lane sees a fresh object. -/
theorem primingQueryEmptyAcquiredOfBlockedPhase {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState} (hReached : PrimingQueryEmptyReached l X g shuffles votes ends)
    (hPhase : ∀ lane < 32, ∀ {t u : TState},
      Run kernel Assumptions.all l (warpLane l g lane) {} (X.tr (warpLane l g lane)) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u →
      u.pc = 679 →
      let log := X.objects (queryEmptyObject l (g/l.block) 0)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    PrimingQueryEmptyConsumed l X g shuffles votes ends := by
  obtain ⟨cur⟩ := hReached
  have hCode : LoaderWaitCode firstQueryEmptyWaitSite := ⟨Flow.code_679,Flow.code_680,Flow.code_681⟩
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSize : l.sharedBase+16 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+16)%8 = 0 := by have := hp.shared.1; omega
  exact loaderWarpWaitOfReadyLast hMax hg hBlock hCode (by decide)
    hSize hAlign cur (by simp [firstQueryEmptyWaitSite,primingQueryWaitFacts])
    (by simp [firstQueryEmptyWaitSite,primingQueryWaitFacts])
    (by simp [firstQueryEmptyWaitSite,primingQueryWaitFacts])
    (fun lane hl {_ _} hRun hLocal hAt => hPhase lane hl hRun hLocal hAt.1)

/-- A reached Q0 empty acquire crosses its first polling loop when the object is fresh. -/
theorem primingQueryEmptyAcquiredOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState} (hReached : PrimingQueryEmptyReached l X g shuffles votes ends)
    (hPhase : let log := X.objects (queryEmptyObject l (g/l.block) 0)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    PrimingQueryEmptyConsumed l X g shuffles votes ends :=
  primingQueryEmptyAcquiredOfBlockedPhase hp hMax hg hReached
    (fun _ _ {_ _} _ _ _ => hPhase)

/-- The common maximal startup gives the first query's empty object its single credit. -/
theorem firstQueryEmptyInitializedOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {cta : Nat} (hc : cta < l.grid) :
    PairTmaRing.InitFirst X (queryEmptyObject l cta 0) 1 ∧
      ∃ r ∈ X.objects (queryEmptyObject l cta 0), r.action = .init 1 := by
  let g := cta*l.block + 0
  have hb : 0 < l.block := by rw [hp.block]; decide
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hb
  obtain ⟨hCta,hLocal⟩ := NamedBar.lane_cta (c := cta) hb hb
  have hw : warpIndex l g = 0 := by unfold warpIndex g; rw [hLocal]
  obtain ⟨a,_,hSame,_,_,hInit⟩ := warp0InitializerRecords hp hMax hg hw
  have ha : a/l.block = cta := hSame.1.2.2.symm.trans hCta
  obtain ⟨j,_,he⟩ := hInit 2
  have hExpected : (initEvent l a 2).kind = .mbInit (queryEmptyObject l cta 0) 1 := by
    change Kind.mbInit (initObject l (a/l.block) 2) 1 = _
    rw [ha]
    rfl
  have hEvent : initEvent l a 2 = ⟨(initEvent l a 2).pc,.mbInit (queryEmptyObject l cta 0) 1⟩ := by
    rw [← hExpected]
  obtain ⟨_,r,hRecord,_,hAction,_,_⟩ := init_record_of_consistent hMax.1
    (show X.MbInit (a,j) (queryEmptyObject l cta 0) 1 from
      ⟨_,he.trans (congrArg some hEvent)⟩)
  have hMem := List.mem_of_getElem? hRecord
  exact ⟨(activeObjectHistory hp hMax.1 (2 : Fin 34) hMem).1,r,hMem,hAction⟩

/-- An actual Q0 return credit implies an earlier successful Q0 acquire in its CTA. -/
theorem firstQueryPollOfEmptyUpdate {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (queryEmptyObject l cta 0)) (hUpdate : CounterUpdate r.action) :
    ∃ (k : Nat) (poll : Record Ref), (X.objects (queryObject l cta 0))[k]? = some poll ∧
      poll.action = .pollParity 0 true ∧ poll.reply.waited = some true := by
  obtain ⟨g,j,_,_,_,he,hCta,_,_⟩ := queryEmptyUpdateAt hp hX 0 hr hUpdate
  obtain ⟨k,_,loc,q,hGet,_⟩ := Mma.firstQueryWaitBeforeGate hp hX he
    (by change 2145 ≤ 2537; decide) (by change 2537 ≤ 2642; decide)
  have hLoc := Mma.mmaFixedWaitAddress hp hX hGet (by decide)
  rw [hCta] at hLoc
  have hObj : loc = queryObject l cta 0 := hLoc
  rw [hObj] at hGet
  have hParity := firstQueryReadyPollParity hp hX hGet (by rfl)
  rw [hParity] at hGet
  obtain ⟨i,poll,hPoll,_,hAction,_,hSuccess⟩ := actualPollRecordClean hp hX hGet
  exact ⟨i,poll,hPoll,hAction,hSuccess⟩

/-- An actual Q0 return credit implies an earlier successful Q0 acquire in its CTA. -/
theorem firstQueryObservedOfEmptyUpdate {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {cta : Nat} {r : Record Ref}
    (hr : r ∈ X.objects (queryEmptyObject l cta 0)) (hUpdate : CounterUpdate r.action) :
    ∃ poll ∈ X.objects (queryObject l cta 0), poll.reply.waited = some true := by
  obtain ⟨_,poll,hPoll,_,hSuccess⟩ := firstQueryPollOfEmptyUpdate hp hX hr hUpdate
  exact ⟨poll,List.mem_of_getElem? hPoll,hSuccess⟩

end PTX.Kernels.TmlFa4Fwd.Loader
