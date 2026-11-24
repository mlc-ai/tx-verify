-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasGuard
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness
public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Barrier
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Flow.ReturningPrefix
import Lemmas.Protocol.ElectCount
import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.MBarrier PTX.EventFrame Prologue
open Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

set_option maxRecDepth 15000 in
private theorem openingBiasTailCode :
    (kernel.code.drop 707).all (fun i => staysPastEvent 707 i.op) = true := by kernel_rfl

private theorem openingBiasTailSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (707 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

/-- A trace whose decoded successors stay above a cut retains that floor. -/
theorem traceRetainsFloor {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    {floor : Nat}
    (hCode : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true)
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : floor ≤ s.pc) : floor ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (eventTailStepOfAudit hCode hSegments hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (eventTailStepOfAudit hCode hSegments hs (.inr ⟨_,rfl,he⟩))

/-- An event above the cut cannot precede a final state below that cut. -/
theorem noEventAboveFinalFloor {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} {e : Event}
    {floor : Nat}
    (hCode : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true)
    (h : TraceReach kernel Assumptions.all l g s events t) (ht : t.pc < floor)
    (he : e ∈ events) : e.pc < floor := by
  induction h with
  | refl => simp at he
  | tau _ _ ih => exact ih ht he
  | @event s v t es event hStep hRest ih =>
    rcases List.mem_cons.mp he with rfl | hTail
    · by_contra! hHigh
      have hSource := (estep_source_pc hStep).symm ▸ hHigh
      have hNext := eventTailStepOfAudit hCode hSegments
        hSource (.inr ⟨_,rfl,hStep⟩)
      have hAfter := traceRetainsFloor hCode hSegments hRest hNext
      omega
    · exact ih ht hTail

/-- A loader lane is still at the wait for its opening Bias buffer. -/
def OpeningBiasBlocked (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ t u, Run kernel Assumptions.all l g {} (X.tr g) (some t) ∧
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧ u.pc = 704

variable {p : Params}

/-- A lane still at the opening Bias wait precludes any actual Bias expectation in its CTA. -/
theorem noBiasExpectationAtOpeningPoll {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hBlocked : OpeningBiasBlocked l X g) (stage : Fin 2) {issue : EvId}
    (hIssue : X.Arrive issue (biasReadyObject l (g/l.block) stage) 32768 1 true .cta) :
    False := by
  obtain ⟨t,u,hRun,hLocal,hPc⟩ := hBlocked
  obtain ⟨a,j⟩ := issue
  obtain ⟨k,site,inst,_,hFloor,hElection⟩ :=
    biasExpectationSelectedIssuerWithFloor hp hX stage hIssue
  have hWarp := biasExpectationIssuerWarp hp hX stage hIssue
  obtain ⟨_,he⟩ := hIssue
  obtain ⟨_,_,hWhere⟩ := actualArriveOffsetIn hp hX he
  have hCta := (congrArg Loc.cta hWhere).symm
  have hSame : SameWarp l a g :=
    ⟨⟨event_thread_lt hX he,hg,hCta⟩,hWarp.trans hw.symm⟩
  obtain ⟨peer,pc,pc',mask,mask',label,lead,lead',ha,hPeer⟩ :=
    ElectOrd.partner hX hSame hElection (PTX.electMember_full l g)
  have hSite := congrArg Event.pc (Option.some.inj (ha.symm.trans hElection))
  change pc = site at hSite
  have hAgree := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ ha hPeer hSame).1
  have hTrace := hRun.returning_reach.append (TraceReach.of_local hLocal)
  simp only [List.append_nil] at hTrace
  have hLow := noEventAboveFinalFloor openingBiasTailCode openingBiasTailSegments hTrace
    (by rw [hPc]; decide) (List.mem_of_getElem? hPeer)
  change pc' < 707 at hLow
  omega

set_option maxRecDepth 15000 in
private theorem openingQueryTailCode :
    (kernel.code.drop 682).all (fun i => staysPastEvent 682 i.op) = true := by kernel_rfl

private theorem openingQueryTailSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (682 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

/-- A loader lane is still at the wait for its opening Q0 buffer. -/
def OpeningFirstQueryBlocked (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ t u, Run kernel Assumptions.all l g {} (X.tr g) (some t) ∧
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧ u.pc = 679

/-- A lane at the opening Q0 wait precludes an actual Q0 tensor subbox from its loader warp. -/
theorem noQuerySubboxAtOpeningPoll {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hBlocked : OpeningFirstQueryBlocked l X g) {issue : EvId}
    {plane : Fin 2} {spec : TensorCopy.Spec} (hCta : issue.1/l.block = g/l.block)
    (hBox : QuerySubbox p l X issue 0 plane spec) : False := by
  obtain ⟨t,u,hRun,hLocal,hPc⟩ := hBlocked
  obtain ⟨hWarp,k,site,inst,hFloor,hElection⟩ := querySubboxElection hp hX hBox
  obtain ⟨_,hGet⟩ := hBox.1
  have hSame : SameWarp l issue.1 g :=
    ⟨⟨event_thread_lt hX hGet,hg,hCta⟩,hWarp.trans hw.symm⟩
  obtain ⟨peer,pc,pc',mask,mask',label,lead,lead',ha,hPeer⟩ :=
    ElectOrd.partner hX hSame hElection (PTX.electMember_full l g)
  have hSite := congrArg Event.pc (Option.some.inj (ha.symm.trans hElection))
  change pc = site at hSite
  have hAgree := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ ha hPeer hSame).1
  have hTrace := hRun.returning_reach.append (TraceReach.of_local hLocal)
  simp only [List.append_nil] at hTrace
  have hLow := noEventAboveFinalFloor openingQueryTailCode openingQueryTailSegments hTrace
    (by rw [hPc]; decide) (List.mem_of_getElem? hPeer)
  change pc' < 682 at hLow
  have hHigh : 682 ≤ site := hFloor
  omega

/-- A loader lane is still at the wait for its opening Q1 buffer. -/
def OpeningSecondQueryBlocked (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ t u, Run kernel Assumptions.all l g {} (X.tr g) (some t) ∧
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧ u.pc = 730

/-- A lane at the opening Q1 wait precludes an actual Q1 tensor subbox from its loader warp. -/
theorem noSecondQuerySubboxAtOpeningPoll {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hBlocked : OpeningSecondQueryBlocked l X g) {issue : EvId}
    {plane : Fin 2} {spec : TensorCopy.Spec} (hCta : issue.1/l.block = g/l.block)
    (hBox : QuerySubbox p l X issue 1 plane spec) : False := by
  obtain ⟨t,u,hRun,hLocal,hPc⟩ := hBlocked
  obtain ⟨hWarp,k,site,inst,hFloor,hElection⟩ := querySubboxElection hp hX hBox
  obtain ⟨_,hGet⟩ := hBox.1
  have hSame : SameWarp l issue.1 g :=
    ⟨⟨event_thread_lt hX hGet,hg,hCta⟩,hWarp.trans hw.symm⟩
  obtain ⟨peer,pc,pc',mask,mask',label,lead,lead',ha,hPeer⟩ :=
    ElectOrd.partner hX hSame hElection (PTX.electMember_full l g)
  have hSite := congrArg Event.pc (Option.some.inj (ha.symm.trans hElection))
  change pc = site at hSite
  have hAgree := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ ha hPeer hSame).1
  have hTrace := hRun.returning_reach.append (TraceReach.of_local hLocal)
  simp only [List.append_nil] at hTrace
  have hLow := noEventAboveFinalFloor (floor := 733)
    (by decide +kernel) (by decide +kernel) hTrace
    (by rw [hPc]; decide) (List.mem_of_getElem? hPeer)
  change pc' < 733 at hLow
  have hHigh : 733 ≤ site := hFloor
  omega

/-- A loader lane is still at the opening stage-one Bias empty wait. -/
def OpeningSecondBiasBlocked (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ t u, Run kernel Assumptions.all l g {} (X.tr g) (some t) ∧
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧ u.pc = 756

/-- A lane waiting at the stage-one opening Bias guard excludes an issued stage-one expectation. -/
theorem noSecondBiasExpectationAtOpeningPoll {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hBlocked : OpeningSecondBiasBlocked l X g) {issue : EvId}
    (hIssue : X.Arrive issue (biasReadyObject l (g/l.block) 1) 32768 1 true .cta) :
    False := by
  obtain ⟨t,u,hRun,hLocal,hPc⟩ := hBlocked
  obtain ⟨a,j⟩ := issue
  obtain ⟨k,site,inst,_,hFloor,hElection⟩ :=
    biasExpectationSelectedIssuerWithStageFloor hp hX 1 hIssue
  have hWarp := biasExpectationIssuerWarp hp hX 1 hIssue
  obtain ⟨_,he⟩ := hIssue
  obtain ⟨_,_,hWhere⟩ := actualArriveOffsetIn hp hX he
  have hCta := (congrArg Loc.cta hWhere).symm
  have hSame : SameWarp l a g :=
    ⟨⟨event_thread_lt hX he,hg,hCta⟩,hWarp.trans hw.symm⟩
  obtain ⟨peer,pc,pc',mask,mask',label,lead,lead',ha,hPeer⟩ :=
    ElectOrd.partner hX hSame hElection (PTX.electMember_full l g)
  have hSite := congrArg Event.pc (Option.some.inj (ha.symm.trans hElection))
  change pc = site at hSite
  have hAgree := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ ha hPeer hSame).1
  have hTrace := hRun.returning_reach.append (TraceReach.of_local hLocal)
  simp only [List.append_nil] at hTrace
  have hLow := noEventAboveFinalFloor (floor := 759)
    (by decide +kernel) (by decide +kernel) hTrace
    (by rw [hPc]; decide) (List.mem_of_getElem? hPeer)
  change pc' < 759 at hLow
  change 759 ≤ site at hFloor
  omega

/-- The prologue initializes both opening Bias-empty objects with four return credits. -/
theorem openingBiasEmptyInitializedAtStage {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {cta : Nat} (hCta : cta < l.grid) (stage : Fin 2)
    :
    PairTmaRing.InitFirst X (biasEmptyObject l cta stage) 4 ∧
      ∃ r ∈ X.objects (biasEmptyObject l cta stage), r.action = .init 4 := by
  let g := cta*l.block + 0
  have hb : 0 < l.block := by rw [hp.block]; decide
  have hg : g < l.threads := NamedBar.cta_thread_lt hCta hb
  obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hb hb
  have hw : warpIndex l g = 0 := by unfold warpIndex g; rw [hLocal]
  obtain ⟨a,_,hSame,_,_,hInit⟩ := warp0InitializerRecords hp hMax hg hw
  have hCta' : a/l.block = cta := hSame.1.2.2.symm.trans hOwner
  let slot : Fin 34 := ⟨32 + stage.val, by have := stage.isLt; omega⟩
  obtain ⟨j,_,he⟩ := hInit slot
  have hKind : (initEvent l a slot).kind = .mbInit (biasEmptyObject l cta stage) 4 := by
    fin_cases stage <;>
      change Kind.mbInit (initObject l (a/l.block) _) 4 = _ <;>
      rw [hCta'] <;> rfl
  have hExpected :
      initEvent l a slot = ⟨(initEvent l a slot).pc,.mbInit (biasEmptyObject l cta stage) 4⟩ := by
    rw [← hKind]
  have hIssue : X.MbInit (a,j) (biasEmptyObject l cta stage) 4 :=
    ⟨_,he.trans (congrArg some hExpected)⟩
  obtain ⟨_,r,hRecord,_,hAction,_,_⟩ := init_record_of_consistent hMax.1 hIssue
  have hr : r ∈ X.objects (biasEmptyObject l cta stage) := List.mem_of_getElem? hRecord
  refine ⟨?_, r, hr, hAction⟩
  fin_cases stage
  · exact (activeObjectHistory hp hMax.1 (32 : Fin 34) hr).1
  · exact (activeObjectHistory hp hMax.1 (33 : Fin 34) hr).1

/-- The prologue initializes the opening Bias buffer with four return credits. -/
theorem openingBiasEmptyInitialized {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {cta : Nat} (hCta : cta < l.grid) :
    PairTmaRing.InitFirst X (biasEmptyObject l cta 0) 4 ∧
      ∃ r ∈ X.objects (biasEmptyObject l cta 0), r.action = .init 4 :=
  openingBiasEmptyInitializedAtStage hp hMax hCta 0

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
