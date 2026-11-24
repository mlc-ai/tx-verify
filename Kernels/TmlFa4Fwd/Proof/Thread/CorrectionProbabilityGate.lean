-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityIssuers
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
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
public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalProbabilityGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.MBarrier PTX.Assumption Prologue
open PTX.Kernels.TmlFa4Fwd.Correction

private theorem jointCreditSites {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i source cta tx n : Nat} {rel : Bool} {scope : MbarScope}
    (stage : Fin 2) (hw : 8 ≤ warpIndex l g)
    (he : X.get (g,i) = some ⟨source, .arrive (Scores.probabilityObject l cta stage 0)
      tx n rel scope⟩) :
    source ∈ (if stage.val = 0 then [7752, 8223, 8759] else [7754, 8442, 9055]) := by
  have hOff : 96 + 8 * stage.val ∈ [96, 104, 112, 120] := by fin_cases stage <;> decide
  rcases actualProbabilityArrivalSite hp hX he hOff rfl with ⟨q, rfl⟩ | hc
  · have hRole := (Softmax.probabilityArriveFacts hp hX q he).2.2.2.2.1
    omega
  · have hAddr := correctionArriveAddressExact hp hX he (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      tauto)
    have hGroup : correctionArriveOffset source = 96 + 8 * stage.val := by
      have h := congrArg Loc.addr hAddr
      change l.sharedBase + (96 + 8 * stage.val) =
        l.sharedBase + correctionArriveOffset source at h
      omega
    have hAll : ∀ stage : Fin 2, ∀ source ∈ [7752, 7754, 8223, 8442, 8759, 9055],
        correctionArriveOffset source = 96 + 8 * stage.val →
        source ∈ (if stage.val = 0 then [7752, 8223, 8759] else [7754, 8442, 9055]) := by
      decide
    exact hAll stage source hc hGroup

private def initialCreditSite (stage : Fin 2) : Nat := if stage.val = 0 then 7752 else 7754

set_option maxRecDepth 100000 in
private theorem initialCreditFloor (stage : Fin 2) :
    ((kernel.code.drop (initialCreditSite stage + 1)).all
      (fun i => staysPastEvent (initialCreditSite stage + 1) i.op)) = true := by
  fin_cases stage <;> kernel_rfl

private theorem initialCreditSegments (stage : Fin 2) (site : Nat)
    (hLow : initialCreditSite stage + 1 ≤ site) (hSite : site ∈ Assumptions.swExp2Sites)
    (seg : SegMatch CuteSlot) (_hSeg : cuteExp2.matchAt kernel site = some seg) :
    initialCreditSite stage + 1 ≤ seg.stop := by
  have hCode : Assumptions.swExp2Sites.all (· < 7752) = true := by decide
  have hHigh := of_decide_eq_true (List.all_eq_true.mp hCode site hSite)
  have hInit : 7752 ≤ initialCreditSite stage := by fin_cases stage <;> decide
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem noPriorJointCredit {g i cta source : Nat} (stage : Fin 2) (hw : 8 ≤ warpIndex l g)
    (he : X.get (g,i) = some
      ⟨source, .arrive (Scores.probabilityObject l cta stage 0) 0 1 true .cta⟩)
    (hSource : source = initialCreditSite stage) :
    Scores.probabilityOrdinal l X cta stage 0 (g,i) = 0 := by
  let obj := Scores.probabilityObject l cta stage 0
  change ((X.tr g).take i).countP (arrivesOn obj) = 0
  apply List.countP_eq_zero.mpr
  intro e hMem hMark
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hMem
  have hLt := (List.getElem?_eq_some_iff.mp hk).1
  simp only [List.length_take] at hLt
  have hKI : k < i := by omega
  rw [List.getElem?_take_of_lt hKI] at hk
  obtain ⟨prev, kind⟩ := e
  cases kind <;> simp only [arrivesOn, sourceArrive, Bool.false_eq_true] at hMark
  case arrive loc tx count rel scope =>
    have hLoc : loc = obj := of_decide_eq_true hMark
    subst loc
    have hJoint := jointCreditSites hp hX stage hw (i := k) (cta := cta) hk
    have hPrior : initialCreditSite stage ≤ prev := by
      fin_cases stage <;> simp [initialCreditSite] at hJoint ⊢ <;> omega
    have hMarked : correctionProbabilityMark stage
        ⟨prev, .arrive obj tx count rel scope⟩ = true :=
      (correctionProbabilityMark_iff stage _).mpr hJoint
    obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
    have hIK : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨_, u, hStep, hTail⟩ := hRun.after_event
      (show X.get (g,k) = some _ from hk) (by omega : k+1 < (X.tr g).length)
    obtain ⟨_, hWalk⟩ := Mma.walkFromRun hTail
    have hNext := correctionProbabilityReturnsForward stage hStep hMarked
    have hBound : initialCreditSite stage + 1 ≤ u.pc := by simpa [hNext] using hPrior
    have hAt : ((X.tr g).drop (k+1))[i-(k+1)]? =
        some ⟨source, .arrive obj 0 1 true .cta⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
      exact he
    have hLate := eventTailEventsOfSegmentFloor (initialCreditFloor stage)
      (initialCreditSegments stage) hWalk hBound _ (List.mem_of_getElem? hAt)
    change initialCreditSite stage + 1 ≤ source at hLate
    omega

/-- The physical joint credits of a correction lane occur only at its audited
stage-marked release instructions. -/
theorem correctionProbabilityOrdinalLeMarks (stage : Fin 2) {g cta j : Nat} (hw : 8 ≤ warpIndex l g)
    :
    Scores.probabilityOrdinal l X cta stage 0 (g,j) ≤
      ((X.tr g).take j).countP (correctionProbabilityMark stage) := by
  let obj := Scores.probabilityObject l cta stage 0
  apply List.countP_mono_left
  intro e he hm
  obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he)
  obtain ⟨site,kind⟩ := e
  cases kind <;> simp only [arrivesOn,sourceArrive,Bool.false_eq_true] at hm
  case arrive loc tx count rel scope =>
    have hArea : loc = obj := of_decide_eq_true hm
    subst loc
    exact (correctionProbabilityMark_iff _ _).mpr
      (jointCreditSites hp hX stage hw (i := k) (cta := cta) hk)

/-- A correction joint credit is its lane's startup contribution or follows the returned
statistics rendezvous of the same local ordinal. -/
theorem correctionProbabilityCreditStatsWait {g i cta : Nat} (stage : Fin 2)
    (hw : 8 ≤ warpIndex l g) (hCredit : Scores.ProbabilityCredit l X (g,i) cta stage 0) :
    (Scores.probabilityOrdinal l X cta stage 0 (g,i) = 0 ∧
      ∃ e, X.get (g,i) = some e ∧
        correctionAction e = some (.accumulatorCredit .initial stage)) ∨
    (∃ j < i, BarrierArrival X (g,j) (statsBarrierId l g stage) (some 64) .sync ∧
      (correctionBefore X (g,j)).barrier (statsBarrierId l g stage) =
        Scores.probabilityOrdinal l X cta stage 0 (g,i)) := by
  obtain ⟨source, he⟩ := hCredit
  have hs := jointCreditSites hp hX stage hw he
  let obj := Scores.probabilityObject l cta stage 0
  let n := Scores.probabilityOrdinal l X cta stage 0 (g,i)
  have hRaw :
      source = (if stage.val = 0 then 7752 else 7754) ∨
      source ∈ (if stage.val = 0 then [8223, 8759] else [8442, 9055]) := by
    fin_cases stage <;> simpa using hs
  rcases hRaw with hFirst | hLater
  · left
    have hCorr : source ∈ [7752, 7754, 8223, 8442, 8759, 9055] := by
      fin_cases stage <;> rw [hFirst] <;> decide
    obtain ⟨_, _, ht, hr, _, _⟩ := correctionProbabilityCredit hp hX he hCorr
    refine ⟨noPriorJointCredit hp hX stage hw he hFirst, _, he, ?_⟩
    rw [ht, hr]
    exact correctionInitialAccumulatorObservation stage _ source hFirst
  · right
    have hBudget := correctionProbabilityWaitBudget hX stage he hLater
    change ((X.tr g).take i).countP (correctionProbabilityMark stage) + 1 ≤
      ((X.tr g).take i).countP (correctionStatsWaitMark stage) at hBudget
    have hCompare := correctionProbabilityOrdinalLeMarks hp hX stage (cta := cta) (j := i) hw
    exact correctionNamedWaitAtOrdinal hp hX stage (List.getElem?_eq_some_iff.mp he).1
      (by omega)

/-- A joint credit after the terminal statistics rendezvous belongs to the terminal round. -/
theorem terminalProbabilityCreditAfterStats {g i j cta : Nat} (stage : Fin 2)
    (hw : 8 ≤ warpIndex l g) (hCredit : Scores.ProbabilityCredit l X (g,i) cta stage 0)
    (hWait : CorrectionWaits X (g,j) .terminal stage) (hJ : j < i) :
    Scores.TerminalProbabilityCredit l X (g,i) cta stage := by
  obtain ⟨source,hGet⟩ := hCredit
  obtain ⟨e,he,hAction⟩ := hWait
  have hSite := correctionTerminalWaitSite hAction
  have hLate : 8447 ≤ e.pc := by rw [hSite]; fin_cases stage <;> decide
  have hFloor : (kernel.code.drop 8447).all (fun i => staysPastEvent 8447 i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSites : ∀ site ∈ Assumptions.swExp2Sites, site < 8447 := by decide
  have hSegment : ∀ site, 8447 ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, PTX.Assumption.cuteExp2.matchAt kernel site = some seg → 8447 ≤ seg.stop := by
    intro site hLow hMem
    exact False.elim ((Nat.not_le_of_lt (hSites site hMem)) hLow)
  have hLen : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hGet).1
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX hGet)
  obtain ⟨t,u,hStep,hTail⟩ := hRun.after_event he (by omega)
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hTail
  have hHere : 8447 ≤ t.pc := (PTX.EventFrame.estep_source_pc hStep).symm ▸ hLate
  have hRel : j+1 ≤ i := by omega
  have hMem : (⟨source,.arrive (Scores.probabilityObject l cta stage 0) 0 1 true .cta⟩ : Event) ∈
      e :: (X.tr g).drop (j+1) := by
    apply List.mem_cons_of_mem
    apply List.mem_of_getElem? (i := i-(j+1))
    rw [List.getElem?_drop,Nat.add_sub_of_le hRel]
    exact hGet
  have hAfter := eventTailEventsOfSegmentFloor (floor := 8447)
    hFloor hSegment (.ev hStep hWalk) hHere _ hMem
  have hOptions := jointCreditSites hp hX stage hw hGet
  have hFinal : source = if stage = 0 then 8759 else 9055 := by
    change 8447 ≤ source at hAfter
    fin_cases stage
    · change source ∈ [7752,8223,8759] at hOptions
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hOptions
      change source = 8759
      omega
    · change source ∈ [7754,8442,9055] at hOptions
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hOptions
      change source = 9055
      omega
  rw [hFinal] at hGet
  exact Scores.terminalProbabilityCreditOfDecoded hGet
