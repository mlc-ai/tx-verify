-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFirstStageStaging
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalCreditProgress
import all Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal
import all Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasRendezvousProgress
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadyHistory
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Epilogue Prologue

private theorem outputFenceOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (stage : Fin 2) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (outputFencePc stage) F) :
    ∃ d : OpeningTripCursor l X g (outputFencePc stage+1) F, d.pos = c.pos+1 := by
  let proxy : ProxyFence := .async (some (.shared .cta))
  let e : Event := ⟨c.ready.pc,.fenceProxy proxy none⟩
  have hOut : out kernel Assumptions.all l g c.ready =
      .ev (.fenceProxy proxy none (next c.ready)) := by
    have hLo : 8758 ≤ outputFencePc stage := by unfold outputFencePc; omega
    rw [signalModel c.checkpoint.1 hLo (fenceCode stage) rfl]
    unfold out
    rw [c.checkpoint.1,c.checkpoint.2.2.2.1,fenceCode]
    rfl
  have hEvent : EStep kernel Assumptions.all l g c.ready e (some (next c.ready)) :=
    ⟨_,hOut,rfl,rfl⟩
  have hLt : c.pos < (X.tr g).length := by
    by_contra! hLong
    have hEnd := Nat.le_antisymm c.bounded hLong
    have hStarted := List.ne_nil_of_length_pos (hEnd ▸ c.positive)
    have hPrefix := c.recorded
    rw [List.take_of_length_le hLong] at hPrefix
    exact hMax.not_grows (Softmax.biasProxyCanIssue hMax.1 hg hStarted
      (c.released hEnd) hPrefix c.localSteps hEvent)
  have hTail := c.remaining
  rw [List.drop_eq_getElem_cons hLt] at hTail
  let hNext : Next kernel Assumptions.all l g c.before c.ready
      (.fenceProxy proxy none (next c.ready)) := ⟨c.localSteps,hOut⟩
  obtain ⟨_,⟨hGet,hReturned⟩,hRest⟩ := hNext.continuing_event
    (by rintro ⟨_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hReturned
  have he : X.get (g,c.pos) = some e := by
    change (X.tr g)[c.pos]? = _
    rw [List.getElem?_eq_getElem hLt,hGet]
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some (next c.ready)) :=
    by rw [List.take_succ_eq_append_getElem hLt,hGet]; exact c.recorded.snoc c.localSteps hEvent
  exact ⟨⟨c.pos+1,next c.ready,next c.ready,c.ending,Nat.succ_pos _,len_of_get he,
    releasedIfLast he (by simp [e,Kind.resume]),c.checkpoint.next,hPast,hRest,.refl⟩,rfl⟩

/-- Staging publication and its returned lane state. -/
structure StagingPublished (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (F : List (Nat × Value)) where
  publication : Nat
  ready : Thread.CorrectionReady X (g,publication) stage
  cursor : OpeningTripCursor l X g (outputFencePc stage+3) F
  position : cursor.pos = publication+1

/-- The final staged vector is fenced and its credits and ready arrival are recorded. -/
theorem publishStagingOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (stage : Fin 2) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (outputFencePc stage) (outputSignalFacts l g stage ++ F))
    (hFrame : ∀ pair ∈ F, pair.1 ≠ outputCreditDst stage ∧ pair.1 ≠ outputCreditDst stage+1) :
    Nonempty (StagingPublished l X g stage F) := by
  obtain ⟨a,_⟩ := outputFenceOfMaximal hMax hg stage c
  have hAt := a.checkpoint
  have hFresh {pair : Nat × Value} (hMem : pair ∈ outputSignalFacts l g stage ++ F) :
      pair.1 ≠ outputCreditDst stage ∧ pair.1 ≠ outputCreditDst stage+1 := by
    rcases List.mem_append.mp hMem with h | h
    · simp only [outputSignalFacts,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl <;> fin_cases stage <;> dsimp only <;> decide
    · exact hFrame pair h
  have hLim := hp.shared.2.1
  have hAlign := hp.shared.1
  have hStage := stage.isLt
  have hCreditBound : (creditLoc l g stage).addr + 0 < 2^32 := by unfold creditLoc; simp only; omega
  have hCreditAlign : ((creditLoc l g stage).addr + 0)%8 = 0 := by
    unfold creditLoc
    simp only
    omega
  have hCredit := correctionReleaseOut (l := l) (g := g) hAt
    (signalModel hAt.1 (by unfold outputFencePc; omega) (creditCode stage) rfl) (creditCode stage)
    hAt.2.2.2.2.1 hAt.2.2.2.2.2.2.1 hCreditBound hCreditAlign
  obtain ⟨_,b,_⟩ := unitArrivalOfMaximal hMax hg a hCredit (fun _ h => (hFresh h).1)
  have hAt := b.checkpoint
  have hOutAddr : outputReadyBase l stage + outputReadyImm stage = (readyLoc l g stage).addr := by
    fin_cases stage <;> simp [outputReadyBase,outputReadyImm,readyLoc]
  have hOutBound : outputReadyBase l stage + outputReadyImm stage < 2^32 := by
    rw [hOutAddr]
    unfold readyLoc
    simp only
    omega
  have hOutAlign : (outputReadyBase l stage + outputReadyImm stage)%8 = 0 := by
    rw [hOutAddr]
    unfold readyLoc
    simp only
    omega
  have hOut := correctionReleaseOut (l := l) (g := g) hAt
    (signalModel hAt.1 (by unfold outputFencePc; omega) (readyCode stage) rfl) (readyCode stage)
    hAt.2.2.2.2.2.1 hAt.2.2.2.2.2.2.1 hOutBound hOutAlign
  obtain ⟨he,d,hPos⟩ := unitArrivalOfMaximal hMax hg b hOut (fun _ h => (hFresh h).2)
  have hReady : Thread.CorrectionReady X (g,b.pos) stage := by
    exact (Thread.CorrectionReady.ofActualArrival hp hMax.1 stage
      (by simpa only [Nat.add_assoc,hOutAddr,readyLoc] using he)).1
  let after : OpeningTripCursor l X g (outputFencePc stage+3) F :=
    ⟨d.pos,d.before,d.ready,d.ending,d.positive,d.bounded,d.released,
      d.checkpoint.mono ((holds_append _ _ _).1 d.checkpoint.2.2.2.2).2,
      d.recorded,d.remaining,d.localSteps⟩
  exact ⟨⟨b.pos,hReady,after,hPos⟩⟩

/-- The actual first staging publication retains the complete correction lane frame. -/
structure FirstOutputPublished (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  staging : FirstStageStagingDone p l X g batch
  published : StagingPublished l X g 0
    (finalizeSurfaceFrame l g 0 16
      (firstChunkFrame p l g batch (laneOf l g) staging.sum staging.maximum))

theorem FirstStageStagingDone.publishOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (c : FirstStageStagingDone p l X g batch) :
    Nonempty (FirstOutputPublished p l X g batch) := by
  let F := finalizeSurfaceFrame l g 0 16
    (firstChunkFrame p l g batch (laneOf l g) c.sum c.maximum)
  have hOld : Holds c.cursor.ready.regs F := c.cursor.checkpoint.2.2.2.2
  have hCredit : (outputCreditReg 0,b32 (creditLoc l g 0).addr) ∈ F := by
    simp [F,finalizeSurfaceFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      correctionBeforeRescale,tileSetupFrame,correctionActiveTileFacts,correctionTileFrame,
      afterCreditFacts,creditFacts,outputCreditReg,creditLoc]
  have hBase : (outputReadyReg 0,b32 (outputReadyBase l 0)) ∈ F := by
    simp [F,finalizeSurfaceFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      correctionBeforeRescale,tileSetupFrame,correctionActiveTileFacts,correctionTileFrame,
      afterCreditFacts,creditFacts,entryFacts,nonzeroBarrierFacts,outputReadyReg,outputReadyBase]
  have hCount : (6498,b32 1) ∈ F := by
    simp [F,finalizeSurfaceFrame,firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts]
  have hSignals : Holds c.cursor.ready.regs (outputSignalFacts l g 0) :=
    ⟨holds_mem hOld hCredit,holds_mem hOld hBase,holds_mem hOld hCount,trivial⟩
  let a : OpeningTripCursor l X g (outputFencePc 0) (outputSignalFacts l g 0 ++ F) :=
    ⟨c.cursor.pos,c.cursor.before,c.cursor.ready,c.cursor.ending,c.cursor.positive,
      c.cursor.bounded,c.cursor.released,
      c.cursor.checkpoint.mono ((holds_append _ _ _).2 ⟨hSignals,hOld⟩),
      c.cursor.recorded,c.cursor.remaining,c.cursor.localSteps⟩
  have hFresh : ∀ r ∈ F.map Prod.fst, r ≠ outputCreditDst 0 ∧ r ≠ outputCreditDst 0+1 :=
    of_decide_eq_true rfl
  obtain ⟨d⟩ := publishStagingOfMaximal hp hMax hg 0 a
    (fun _ h => hFresh _ (List.mem_map_of_mem h))
  exact ⟨⟨c,d⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
