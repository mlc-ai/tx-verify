-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondFinalizationAcquire
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFirstStageStaging

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Prologue Epilogue

private def secondChunkKeys : List Nat :=
  [9391,6499,6795,740,1654,1653] ++ firstChunkKeys

private theorem secondChunkKeeps (chunk : Fin 16) :
    ∀ r ∈ secondChunkKeys,
      r ∉ finalizeDataRegs 1 chunk ∧
      (∀ q ∈ finalizePacks 1 chunk, q.1 ≠ r) ∧
      (∀ q ∈ finalizeMuls 1 chunk, q.1 ≠ r) ∧
      (∀ half, ∀ q ∈ finalizeUnpacks 1 chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) ∧
      (chunk.val < 4 → r ≠ outputStoreAddrReg 1 (finalizeVector chunk 1)) := by
  fin_cases chunk <;> decide +kernel

private theorem secondChunkTmemFresh (chunk : Fin 16) :
    0 < chunk.val → finalizeAddressReg 1 chunk ∉ secondChunkKeys := by
  fin_cases chunk <;> decide +kernel

private theorem secondChunkEvenFresh (chunk : Fin 16) :
    0 < chunk.val → chunk.val < 4 →
      outputStoreAddrReg 1 (finalizeVector chunk 0) ∉ secondChunkKeys := by
  fin_cases chunk <;> decide +kernel

private theorem secondChunkSurfaceRegisters {p : Params} {l : Launch} {X : Execution}
    {g batch : Nat} (hg : g < l.threads) (c : SecondTerminalWordsReady p l X g batch) :
    FinalizeSurfaceRegisters l g 1 c.reciprocal c.chunkFrame := by
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hFirst := firstChunkSurfaceRegisters p l g batch (laneOf l g) c.firstSum c.firstMaximum
  rw [hSelf] at hFirst
  have hKeep {rv : Nat × Value}
      (h : rv ∈ firstChunkFrame p l g batch (laneOf l g) c.firstSum c.firstMaximum) :
      rv ∈ c.chunkFrame := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ h)))))
  have hKeys : c.chunkFrame.map Prod.fst = secondChunkKeys := rfl
  refine ⟨hKeep hFirst.tmemZero,?_,hKeep hFirst.deltaOdd,
    fun chunk hn hc => hKeep (hFirst.deltaEven chunk hn hc),.head _,?_,?_,?_⟩
  · apply hKeep
    simp [firstChunkFrame,firstTerminalReciprocalFrame,correctionBeforeRescale,tileSetupFrame,
      correctionTileGeometryFacts,finalizeAddressReg,hSelf]
  · intro chunk hn rv hr he
    exact secondChunkTmemFresh chunk hn (hKeys ▸ he ▸ List.mem_map_of_mem hr)
  · intro chunk hn hc rv hr he
    exact secondChunkEvenFresh chunk hn hc (hKeys ▸ he ▸ List.mem_map_of_mem hr)
  · intro chunk r hr
    exact secondChunkKeeps chunk r (hKeys ▸ hr)

private theorem SecondOutputLoadReady.surfaceCursor {p : Params} {l : Launch}
    {Y X : Execution} (hTrace : Y.tr = X.tr) {g batch : Nat} (hg : g < l.threads)
    (c : SecondOutputLoadReady p l Y g batch) :
    Nonempty (OpeningTripCursor l X g (finalizeSurfacePc 1 0)
      (finalizeSurfaceFrame l g 1 0 c.words.chunkFrame)) := by
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hVec : finalizeVectorFact l g 1 0 ∈ c.words.chunkFrame := by
    simp [SecondTerminalWordsReady.chunkFrame,SecondTerminalWordsReady.pollFrame,
      SecondTerminalWordsReady.reciprocalFrame,SecondTerminalWordsReady.wordsFrame,
      firstChunkFrame,firstTerminalReciprocalFrame,finalizeLayoutFacts,hSelf]
  have hAt : At c.cursor.ready (finalizeSurfacePc 1 0)
      (finalizeSurfaceFrame l g 1 0 c.words.chunkFrame) := by
    have hFrame := c.cursor.checkpoint.2.2.2.2
    apply c.cursor.checkpoint.mono
    change Holds c.cursor.ready.regs (finalizeVectorFact l g 1 0::c.words.chunkFrame)
    exact ⟨holds_mem hFrame hVec,hFrame⟩
  have he : X.get (g,c.freeIndex) =
      some ⟨finalizePollPc 1 true,.wait (finalizePollLoc l g 1 true) 1 true true .cta⟩ := by
    simpa only [Execution.get,hTrace] using c.freeWait
  exact ⟨⟨c.cursor.pos,c.cursor.before,c.cursor.ready,c.cursor.ending,c.cursor.positive,
    by simpa only [hTrace] using c.cursor.bounded,
    fun hLast => releasedIfLast he (by simp [Kind.resume]) (c.position.symm.trans hLast),
    hAt,by simpa only [hTrace] using c.cursor.recorded,
    by simpa only [hTrace] using c.cursor.remaining,c.cursor.localSteps⟩⟩

/-- Both row statistics are retained after the live second output surface is staged. -/
structure SecondStageStagingDone (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  wordsExecution : Execution
  words : SecondTerminalWordsReady p l wordsExecution g batch
  cursor : OpeningTripCursor l X g (outputFencePc 1)
    (finalizeSurfaceFrame l g 1 16 words.chunkFrame)

/-- The second surface uses the same chunk transition at its own collective ordinals. -/
theorem secondStageStagingAfterRescale {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : OutputFootprint p X) (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {lead batch : Nat} (hRole : 8 ≤ warpIndex l lead ∧ warpIndex l lead < 12)
    (hFirst : ∀ g, SameWarp l lead g → ∃ Y, Y.tr = X.tr ∧
      Nonempty (SecondOutputLoadReady p l Y g batch)) :
    ∀ g, SameWarp l lead g → Nonempty (SecondStageStagingDone p l X g batch) := by
  classical
  let c g hw := Classical.choice (Classical.choose_spec (hFirst g hw)).2
  let R (g : Nat) := if hw : SameWarp l lead g then (c g hw).words.reciprocal else 0
  let F (g : Nat) := if hw : SameWarp l lead g then (c g hw).words.chunkFrame else []
  have hF (g : Nat) (hw : SameWarp l lead g) : FinalizeSurfaceRegisters l g 1 (R g) (F g) := by
    simpa only [R,F,dite_eq_left hw] using secondChunkSurfaceRegisters hw.1.2.1 (c g hw).words
  have hEntry (g : Nat) (hw : SameWarp l lead g) :
      Nonempty (OpeningTripCursor l X g (finalizeSurfacePc 1 0)
        (finalizeSurfaceFrame l g 1 0 (F g))) := by
    have h := SecondOutputLoadReady.surfaceCursor (Classical.choose_spec (hFirst g hw)).1
      hw.1.2.1 (c g hw)
    simpa only [F,dite_eq_left hw] using h
  intro g hw
  obtain ⟨d,_,_⟩ := surfaceWarpThroughAfterRescale hp hMax hOutputs hValues hRole
    1 R hF 0 (fun q hq => Classical.choice (hEntry q hq)) 16 (by decide) g hw
  have hFence : finalizeSurfacePc 1 (0+16) = outputFencePc 1 := rfl
  exact ⟨⟨_,(c g hw).words,by simpa only [F,dite_eq_left hw,hFence,Nat.zero_add] using d⟩⟩

theorem secondStageStagingOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : OutputFootprint p X) (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {lead batch : Nat} (hRole : 8 ≤ warpIndex l lead ∧ warpIndex l lead < 12)
    (_hb : batch < p.batch) (_hLo : tilePrefix p batch*p.heads ≤ lead/l.block)
    (_hHi : lead/l.block < tilePrefix p (batch+1)*p.heads)
    (_hSingle : Mma.trips p batch (assignedCoordinates p batch (lead/l.block)).1 = 1)
    (hFirst : ∀ g, SameWarp l lead g → ∃ Y, Y.tr = X.tr ∧
      Nonempty (SecondOutputLoadReady p l Y g batch)) :
    ∀ g, SameWarp l lead g → Nonempty (SecondStageStagingDone p l X g batch) := by
  exact secondStageStagingAfterRescale hp hMax hOutputs hValues hRole hFirst

/-- The actual second staging publication leaves the lane at its LSE dispatch. -/
structure SecondOutputPublished (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  staging : SecondStageStagingDone p l X g batch
  published : StagingPublished l X g 1 (finalizeSurfaceFrame l g 1 16 staging.words.chunkFrame)

theorem SecondStageStagingDone.publishOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (c : SecondStageStagingDone p l X g batch) :
    Nonempty (SecondOutputPublished p l X g batch) := by
  let F := finalizeSurfaceFrame l g 1 16 c.words.chunkFrame
  have hOld : Holds c.cursor.ready.regs F := c.cursor.checkpoint.2.2.2.2
  have hCredit : (outputCreditReg 1,b32 (creditLoc l g 1).addr) ∈ F := by
    simp [F,finalizeSurfaceFrame,SecondTerminalWordsReady.chunkFrame,
      SecondTerminalWordsReady.pollFrame,SecondTerminalWordsReady.reciprocalFrame,
      SecondTerminalWordsReady.wordsFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      correctionBeforeRescale,tileSetupFrame,correctionActiveTileFacts,correctionTileFrame,
      afterCreditFacts,outputCreditReg,creditLoc]
  have hBase : (outputReadyReg 1,b32 (outputReadyBase l 1)) ∈ F := by
    simp [F,finalizeSurfaceFrame,SecondTerminalWordsReady.chunkFrame,
      SecondTerminalWordsReady.pollFrame,SecondTerminalWordsReady.reciprocalFrame,
      SecondTerminalWordsReady.wordsFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      correctionBeforeRescale,tileSetupFrame,correctionActiveTileFacts,correctionTileFrame,
      afterCreditFacts,creditFacts,entryFacts,nonzeroBarrierFacts,outputReadyReg,outputReadyBase]
  have hCount : (6498,b32 1) ∈ F := by
    simp [F,finalizeSurfaceFrame,SecondTerminalWordsReady.chunkFrame,
      SecondTerminalWordsReady.pollFrame,SecondTerminalWordsReady.reciprocalFrame,
      SecondTerminalWordsReady.wordsFrame,firstChunkFrame,firstTerminalReciprocalFrame,
      finalizeLayoutFacts]
  have hSignals : Holds c.cursor.ready.regs (outputSignalFacts l g 1) :=
    ⟨holds_mem hOld hCredit,holds_mem hOld hBase,holds_mem hOld hCount,trivial⟩
  let a : OpeningTripCursor l X g (outputFencePc 1) (outputSignalFacts l g 1 ++ F) :=
    ⟨c.cursor.pos,c.cursor.before,c.cursor.ready,c.cursor.ending,c.cursor.positive,
      c.cursor.bounded,c.cursor.released,
      c.cursor.checkpoint.mono ((holds_append _ _ _).2 ⟨hSignals,hOld⟩),
      c.cursor.recorded,c.cursor.remaining,c.cursor.localSteps⟩
  have hFresh : ∀ r ∈ F.map Prod.fst, r ≠ outputCreditDst 1 ∧ r ≠ outputCreditDst 1+1 :=
    of_decide_eq_true rfl
  obtain ⟨d⟩ := publishStagingOfMaximal hp hMax hg 1 a
    (fun _ h => hFresh _ (List.mem_map_of_mem h))
  exact ⟨⟨c,d⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
