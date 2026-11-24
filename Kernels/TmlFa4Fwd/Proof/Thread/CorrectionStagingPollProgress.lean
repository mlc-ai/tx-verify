-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionOutputAcquire
public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputStagingAvailability
import all Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.ReturningPrefix
import Lemmas.Execution.EventFrameSource
import Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.EventFrame Prologue

private theorem afterStagingGateCode (stage : Fin 2) :
    (kernel.code.drop (finalizePollPc stage true+3)).all
      (fun ins => Thread.staysPastEvent (finalizePollPc stage true+3) ins.op) = true := by
  fin_cases stage <;> set_option maxRecDepth 100000 in decide +kernel

private theorem afterStagingGateNoSegments (stage : Fin 2) :
    Assumptions.swExp2Sites.all (fun site => decide (site < finalizePollPc stage true+3)) =
      true := by fin_cases stage <;> decide +kernel

private theorem afterStagingGateStep (stage : Fin 2) {l : Launch} {g : Nat}
    {s u : TState} {event : Option Event} (hs : finalizePollPc stage true+3 ≤ s.pc)
    (he : WStep kernel Assumptions.all l g s event u) : finalizePollPc stage true+3 ≤ u.pc := by
  apply Thread.eventTailStep (afterStagingGateCode stage) _ hs he
  intro site hLower hSite _ _
  have hUpper := of_decide_eq_true (List.all_eq_true.mp (afterStagingGateNoSegments stage) site
    hSite)
  omega

private theorem stagingGateFloorAlong (stage : Fin 2) {l : Launch} {g : Nat}
    {s u : TState} {events : List Event}
    (hReach : TraceReach kernel Assumptions.all l g s events u) :
    (finalizePollPc stage true+3 ≤ s.pc ∨
      ∃ event ∈ events, finalizePollPc stage true+3 ≤ event.pc) →
    finalizePollPc stage true+3 ≤ u.pc := by
  induction hReach with
  | refl => rintro (h | ⟨_,h,_⟩); exact h; cases h
  | tau he _ ih =>
    intro h
    exact ih (h.imp_left (fun hp => afterStagingGateStep stage hp (.inl ⟨rfl,he⟩)))
  | event he _ ih =>
    intro h
    rcases h with h | ⟨event,hMem,hPc⟩
    · exact ih (.inl (afterStagingGateStep stage h (.inr ⟨_,rfl,he⟩)))
    · rcases List.mem_cons.mp hMem with rfl | hTail
      · exact ih (.inl (afterStagingGateStep stage ((estep_source_pc he) ▸ hPc)
          (.inr ⟨_,rfl,he⟩)))
      · exact ih (.inr ⟨event,hTail,hPc⟩)

private theorem stagingGateExcludesPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g : Nat} {s u : TState}
    (hRun : Run kernel Assumptions.all l g {} (X.tr g) (some s))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u)
    (hPc : u.pc = finalizePollPc stage true) {j : Nat} :
    ¬ Thread.CorrectionReady X (g,j) stage := by
  intro hPub
  have he := hPub.decoded hp hX
  have hEvent : finalizePollPc stage true+3 ≤ outputFencePc stage+2 := by fin_cases stage <;> decide
  have hPath := hRun.returning_reach.append (TraceReach.of_local hLocal)
  rw [List.append_nil] at hPath
  have hFloor := stagingGateFloorAlong stage hPath
    (.inr ⟨_,List.mem_of_getElem? he,hEvent⟩)
  omega

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (stage : Fin 2) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (finalizePollPc stage true) F)
    (hFresh : ∀ q ∈ F, q.1 ≠ finalizePollPred stage true)
    (hBase : (finalizePollBase stage true,b32 (finalizePollLoc l g stage true).addr) ∈ F)
include hp hMax hg hw stage c hFresh hBase

/-- A suspended staging wait still has its original free slot, since reaching
that wait excludes this lane's own prerequisite publication. -/
theorem stagingWaitOfMaximal (hPhase : (6498,b32 1) ∈ F) :
    ∃ j, X.get (g,j) = some ⟨finalizePollPc stage true,
        .wait (finalizePollLoc l g stage true) 1 true true .cta⟩ ∧
      ∃ d : OpeningTripCursor l X g (finalizePollPc stage true+3) F, d.pos = j+1 := by
  apply finalizePollOfMaximal hp hMax hg stage true c hFresh hBase hPhase
  intro t u hRun hLocal hAt
  have hPhaseZero := Protocol.Output.freePhaseZeroBeforeCorrectionPublication hp hMax hg hw
    stage (fun _ => stagingGateExcludesPublication hp hMax.1 stage hRun hLocal hAt.1)
  obtain ⟨state,hs,hZero⟩ := hPhaseZero
  fin_cases stage <;> exact ⟨state,hs,by rw [hZero]; decide⟩

theorem stagingPollOfMaximal (hPhase : (6498,b32 1) ∈ F) :
    Nonempty (OpeningTripCursor l X g (finalizePollPc stage true+3) F) := by
  obtain ⟨_,_,d,_⟩ := stagingWaitOfMaximal hp hMax hg hw stage c hFresh hBase hPhase
  exact ⟨d⟩
end

/-- After the first staging acquire, the real suffix is ready to load the
accumulator, with the normalization word packed in both halves. -/
theorem FirstOutputAcquired.firstLoadOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads)
    (hw : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12)
    (c : FirstOutputAcquired p l X g batch lane) :
    let recip := fl (1 / (if c.sum = 0 then 1 else c.sum))
    Nonempty (OpeningTripCursor l X (warpLane l g lane) (finalizeLoadPc 0 0)
      ((finalizeReciprocalPair 0,.pair recip recip) ::
        (finalPollPrepReg 0,finalPollPrepWord l 0) ::
        firstTerminalReciprocalFrame p l g batch lane c.sum c.maximum)) := by
  let thread := warpLane l g lane
  let F := (finalPollPrepReg 0,finalPollPrepWord l 0) ::
    firstTerminalReciprocalFrame p l g batch lane c.sum c.maximum
  have fresh {r : Nat} (h : r ∉ F.map Prod.fst) : ∀ pair ∈ F, pair.1 ≠ r := by
    intro pair hm he
    exact h (he ▸ List.mem_map_of_mem hm)
  have hBase : (finalizePollBase 0 true,b32 (finalizePollLoc l thread 0 true).addr) ∈ F := by
    simp [F,firstTerminalReciprocalFrame,finalizePollBase,finalizePollLoc,correctionBeforeRescale,
      tileSetupFrame,correctionActiveTileFacts,correctionTileFrame,afterCreditFacts,creditFacts,
      entryFacts,nonzeroBarrierFacts]
  have hPhase : (6498,b32 1) ∈ F := by
    simp [F,firstTerminalReciprocalFrame,finalizeLayoutFacts]
  obtain ⟨after⟩ := stagingPollOfMaximal hp hMax hg hw 0 c.cursor
    (fresh (of_decide_eq_true rfl)) hBase hPhase
  let recip := 1 / (if c.sum = 0 then 1 else c.sum)
  have hr : after.ready.regs (reciprocalReg 0) = some (fl recip) :=
    holds_mem after.checkpoint.2.2.2.2 (.tail _ (.head _))
  obtain ⟨u,hu,hLocal⟩ := packFinalReciprocalLocal (l := l) (g := thread) 0 recip
    after.checkpoint hr (fresh (of_decide_eq_true rfl))
  exact ⟨⟨after.pos,after.before,u,after.ending,after.positive,after.bounded,after.released,
    hu,after.recorded,after.remaining,after.localSteps.trans hLocal⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
