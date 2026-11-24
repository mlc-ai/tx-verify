-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingPollProgress
public import Lemmas.Step.TcLoadProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.Safety.TmemWordSizes
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTensorSchedule

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Prologue Epilogue

/-- An available staging slot permits the lane to issue the next output load.
The recorded callback supplies eight words and retains the same ending. -/
theorem finalizeLoadOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : LayoutInjective X)
    {g : Nat} (hg : g < l.threads) (stage : Fin 2) (chunk : Fin 16)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (finalizeLoadPc stage chunk) F)
    (hAddress : (finalizeAddressReg stage chunk,
      b32 (outputAddress l g stage (8 * chunk.val))) ∈ F)
    :
    ∃ ds words, ds.length = 8 ∧ words.length = 8 ∧
      kernel.code[finalizeLoadPc stage chunk]? =
        some ⟨none,.tcLd ds (finalizeAddressReg stage chunk) .s32x32b none⟩ ∧
      X.get (g,c.pos) = some ⟨finalizeLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (8 * chunk.val)) words .s32x32b)⟩ ∧
      let u := setRegs (next c.ready) ds words
      Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (c.pos+1)) c.ending := by
  obtain ⟨ds,hDs,hCode,hOut⟩ := finalizeLoadTemplate hp stage chunk
    (c.checkpoint.mono ⟨holds_mem c.checkpoint.2.2.2.2 hAddress,trivial⟩)
  obtain ⟨words,hLen,he,hPast,hTail⟩ := Step.tcLoadOfMaximal hMax hGuard hLayout hg
    c.positive c.bounded c.released c.recorded c.remaining c.localSteps hOut
    (fun _ _ _ ⟨_,hWrite,_⟩ => Safety.tensorWroteWordBytes hp hMax.1 hWrite)
    (Assumptions.wfStep _ _ hMax.1 le_snoc (Execution.notifiedInOrder_of_eq rfl)
        (Execution.noNewRead_snoc rfl))
  rw [c.checkpoint.1] at he
  exact ⟨ds,words,hDs,hLen,hCode,he,hPast,hTail⟩

/-- The first recorded output load retains both the ready frame and the real
continuation with the eight accumulator words in its destination registers. -/
structure FirstOutputLoadIssued (p : Params) (l : Launch) (X : Execution)
    (g batch lane : Nat) where
  acquired : FirstOutputAcquired p l X g batch lane
  loadCursor : OpeningTripCursor l X (warpLane l g lane) (finalizeLoadPc 0 0)
    (let recip := fl (1 / (if acquired.sum = 0 then 1 else acquired.sum))
     (finalizeReciprocalPair 0,.pair recip recip) ::
       (finalPollPrepReg 0,finalPollPrepWord l 0) ::
       firstTerminalReciprocalFrame p l g batch lane acquired.sum acquired.maximum)
  destinations : List Nat
  words : List Value
  destinationCount : destinations.length = 8
  wordCount : words.length = 8
  decoded : kernel.code[finalizeLoadPc 0 0]? =
    some ⟨none,.tcLd destinations (finalizeAddressReg 0 0) .s32x32b none⟩
  issued : X.get (warpLane l g lane,loadCursor.pos) = some
    ⟨finalizeLoadPc 0 0,.tc (.ld (outputAddress l (warpLane l g lane) 0 0) words .s32x32b)⟩
  returned : Run kernel Assumptions.all l (warpLane l g lane) {}
    ((X.tr (warpLane l g lane)).take (loadCursor.pos+1))
    (some (setRegs (next loadCursor.ready) destinations words))
  continuation : Run kernel Assumptions.all l (warpLane l g lane)
    (setRegs (next loadCursor.ready) destinations words)
    ((X.tr (warpLane l g lane)).drop (loadCursor.pos+1)) loadCursor.ending

theorem FirstOutputAcquired.issueLoadOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X) (hLayout : LayoutInjective X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads)
    (hw : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12)
    (c : FirstOutputAcquired p l X g batch lane) :
    Nonempty (FirstOutputLoadIssued p l X g batch lane) := by
  obtain ⟨load⟩ := c.firstLoadOfMaximal hp hMax hg hw
  have hAddress : (1629,b32 (outputAddress l (warpLane l g lane) 0 0)) ∈
      firstTerminalReciprocalFrame p l g batch lane c.sum c.maximum := by
    simp [firstTerminalReciprocalFrame,correctionBeforeRescale,tileSetupFrame,
      correctionTileGeometryFacts]
  obtain ⟨ds,words,hDs,hWords,hCode,he,hPast,hTail⟩ :=
    finalizeLoadOfMaximal hp hMax hGuard hLayout hg 0 0 load (.tail _ (.tail _ hAddress))
  exact ⟨⟨c,load,ds,words,hDs,hWords,hCode,he,hPast,hTail⟩⟩

theorem FirstOutputLoadIssued.ordinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch lane : Nat}
    (hRole : 8 ≤ warpIndex l (warpLane l g lane) ∧ warpIndex l (warpLane l g lane) < 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ warpLane l g lane/l.block)
    (hHi : warpLane l g lane/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (warpLane l g lane/l.block)).1 = 1)
    (c : FirstOutputLoadIssued p l X g batch lane) :
    X.TcK (warpLane l g lane,c.loadCursor.pos) 0 :=
  Thread.correctionFirstOutputLoadOrdinal hp hX hFrame hRole.1 hRole.2 hb hLo hHi hSingle c.issued

/-- All participants at the first load release the recorded operation at a stopped lane. -/
theorem FirstOutputLoadIssued.released {p : Params} {l : Launch} {X : Execution}
    {g batch lane : Nat} (c : FirstOutputLoadIssued p l X g batch lane)
    (hRank : X.TcK (warpLane l g lane,c.loadCursor.pos) 0)
    (hPeers : ∀ peer ∈ warpLanes l (warpLane l g lane), ∃ k, X.TcK (peer,k) 0) :
    c.loadCursor.pos+1 = (X.tr (warpLane l g lane)).length →
      Step.Released l X (warpLane l g lane) :=
  Step.releasedOfTcOrdinal c.issued rfl hRank.2 hPeers

end PTX.Kernels.TmlFa4Fwd.Correction
