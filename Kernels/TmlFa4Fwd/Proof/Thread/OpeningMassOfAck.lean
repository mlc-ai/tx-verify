-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityAck
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMassReach
import all Kernels.TmlFa4Fwd.Proof.Thread.OpeningMassReach
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

set_option maxRecDepth 100000 in
private theorem afterSumEntryCode :
    (kernel.code.drop 4878).all (fun i => Thread.staysPastEvent 4878 i.op) = true := by
  decide +kernel

private theorem afterSumEntrySegments : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (4878 ≤ seg.stop)
    | none => false) = true := by decide +kernel

private theorem afterSumEntry {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : 4878 ≤ s.pc) :
    4878 ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih =>
    exact ih (Thread.eventTailStepOfAudit afterSumEntryCode afterSumEntrySegments hs
      (.inl ⟨rfl,ht⟩))
  | event he _ ih =>
    exact ih (Thread.eventTailStepOfAudit afterSumEntryCode afterSumEntrySegments hs
      (.inr ⟨_,rfl,he⟩))

private theorem advanceSumEntry {l : Launch} {g : Nat} {s t : TState} {e : Option Event}
    (hs : s.pc = 4877) (ht : WStep kernel Assumptions.all l g s e t) :
    4878 ≤ t.pc := by
  rcases ht with ⟨rfl,h⟩ | ⟨_,rfl,h⟩
  · obtain ⟨i,hCode,_,hExec⟩ := tauScoreSource h
    rw [hs,Flow.code_4877] at hCode
    obtain rfl := Option.some.inj hCode.symm
    rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
    · change 4878 ≤ s.pc+1
      omega
    · rcases scoreExecLocal hLocal with hFrame | ⟨_,hSite,_,_⟩
      · have hNext : t.pc = s.pc+1 := by simpa only [nextPc,BrxTarget,or_false] using hFrame.pc
        omega
      · rw [hs] at hSite
        exact ((by decide : 4877 ∉ Assumptions.swExp2Sites) hSite).elim
  · obtain ⟨_,hCode,hNoLocal,_⟩ := estep_event_source h
    rw [hs,Flow.code_4877] at hCode
    obtain rfl := Option.some.inj hCode.symm
    cases hNoLocal

private theorem beforeSumEntryKeeps {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events t) (ht : t.pc = 4877)
    (hLo : 4826 ≤ s.pc) (hHi : s.pc ≤ 4877) (hSub : s.sub ≤ 3) :
    ∀ r ∈ openingCarryRegisters, t.regs r = s.regs r := by
  induction h with
  | refl => exact fun _ _ => rfl
  | @tau s u t es hs hRest ih =>
    have hStep := (show WStep kernel Assumptions.all l g _ none _ from .inl ⟨rfl,hs⟩)
    have hStrict : s.pc < 4877 := by
      by_contra! h
      have hFloor := afterSumEntry hRest (advanceSumEntry (hHi.antisymm h) hStep)
      omega
    obtain ⟨hLower,hUpper,hKeep⟩ := openingTailKeeps hLo hStrict hSub hStep
    have hFrame := windowStepFrame .firstRoundCounters (by change 3425 ≤ s.pc; omega)
      (by change s.pc < 5006; omega) hSub hStep
    exact fun r hr => (ih ht hLower hUpper hFrame.2.2.1 r hr).trans (hKeep r hr)
  | @event s u t es e he hRest ih =>
    have hStep := (show WStep kernel Assumptions.all l g _ (some _) _ from .inr ⟨_,rfl,he⟩)
    have hStrict : s.pc < 4877 := by
      by_contra! h
      have hFloor := afterSumEntry hRest (advanceSumEntry (hHi.antisymm h) hStep)
      omega
    obtain ⟨hLower,hUpper,hKeep⟩ := openingTailKeeps hLo hStrict hSub hStep
    have hFrame := windowStepFrame .firstRoundCounters (by change 3425 ≤ s.pc; omega)
      (by change s.pc < 5006; omega) hSub hStep
    exact fun r hr => (ih ht hLower hUpper hFrame.2.2.1 r hr).trans (hKeep r hr)

private theorem cannotReachBeforeSumEntry {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (hs : s.pc = 4877) (ht : t.pc < 4877) :
    ¬ TraceReach kernel Assumptions.all l g s events t := by
  intro h
  cases h with
  | refl => omega
  | tau he hRest =>
    have hFloor := afterSumEntry hRest (advanceSumEntry hs (.inl ⟨rfl,he⟩))
    omega
  | event he hRest =>
    have hFloor := afterSumEntry hRest (advanceSumEntry hs (.inr ⟨_,rfl,he⟩))
    omega

/-- The observed opening acknowledgement gives the first row sum even when the lane has
not yet exited. The retained exponent registers come from its earlier probability cursor. -/
theorem OpeningProbabilityAck.firstMass {p : Params} {l : Launch} {X : Execution}
    {g : Nat} {stage : Fin 2} (ack : OpeningProbabilityAck l X g)
    (cursor : OpeningProbabilityWaitCursor p l X g stage)
    (hWait : cursor.statistics.index+2 ≤ (X.tr g).length)
    (hWeights : ∀ i < 128, cursor.state.regs (1231+i) = some (fl (cursor.values i))) :
    ∃ v, At v 5006 [(7257,fl (∑ i ∈ Finset.range 128, cursor.values i))] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) ack.state v ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take (ack.index+1)) v ∧
      (∀ r ∈ firstSumResidentRegs, v.regs r = cursor.state.regs r) := by
  have hStart : cursor.state.pc = 4826 := cursor.site
  have hEnd := ack.ready.1
  have hForward es : ¬ TraceReach kernel Assumptions.all l g ack.state es cursor.state := by
    exact cannotReachBeforeSumEntry hEnd (by omega)
  obtain ⟨_,hPath⟩ := recordedCheckpointsPath hWait ack.bounded cursor.recorded .refl
    ack.recorded ack.localSteps hForward
  have hKeep := beforeSumEntryKeeps hPath hEnd hStart.ge (by omega)
    (by rw [cursor.sub]; decide)
  have hWeight i (hi : i < 128) : ack.state.regs (1231+i) = some (fl (cursor.values i)) :=
    (hKeep _ (List.mem_append_right _ (mem_exponentLive.mpr (by omega)))).trans (hWeights i hi)
  obtain ⟨v,hv,hLocal,hFrame⟩ :=
    firstRowSumWithResidentsLocal cursor.values ack.ready hWeight (l := l) (g := g)
  refine ⟨v,hv,hLocal,?_,fun r hr => (hFrame r hr).trans
    (hKeep r (by
      simp only [firstSumResidentRegs, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      simp only [openingCarryRegisters, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false]
      tauto))⟩
  simpa only [List.append_nil] using ack.recorded.returning_reach.append
    (TraceReach.of_local (ack.localSteps.trans hLocal))

end PTX.Kernels.TmlFa4Fwd.Softmax
