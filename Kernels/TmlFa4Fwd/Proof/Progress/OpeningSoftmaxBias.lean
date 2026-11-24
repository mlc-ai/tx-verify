-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BiasFirstVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreLoadWords
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningBiasDelivery
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxStages
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleStatisticsCredit
public import Kernels.TmlFa4Fwd.Proof.Thread.SelectedOpeningBiasAcquire
import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasReturn
import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedBiasValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasGeometry
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasVector
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRendezvous

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof PTX.TcMma Prologue Epilogue

private theorem openingBiasPhaseForSoftmaxStage {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {batch : Nat} (hg : g < l.threads) (stage : Fin 2) (hRole : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hMissing : Flow.okPolls (Thread.Loader.biasReadyObject l (g/l.block) stage) (X.tr g) = 0) :
    let log := X.objects (Thread.Loader.biasReadyObject l (g/l.block) stage)
    ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1 := by
  fin_cases stage
  · exact openingBiasPhaseForPendingLane hp hMax hFrame hg
      (by change warpIndex l g / 4 = 0 at hRole; omega) hb hLo hHi hMissing
  · exact openingSecondBiasPhaseForPendingLane hp hMax hFrame hg hRole hb hLo hHi hMissing

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

private theorem openingSoftmaxBiasLaneOfWords {g : Nat} (hValues : Softmax.OpeningScoreWords l X g)
    {batch : Nat} (hg : g < l.threads) (stage : Fin 2) (hRole : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads) :
    ∃ j, Thread.Scores.FirstBiasAcquire l X g j stage ∧
      Nonempty (Softmax.OpeningBiasLane p l X g batch stage j) := by
  have hCuQ : DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hUsedK := usedKProtected hp hMax.1
  have hGuard := syncGuarded hp hMax.1 hCuQ
  have hLayout := Mma.actualMmaLayoutInjective hMax.1
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  have hStage : Softmax.stageOf (⟨warpIndex l g,hWarp⟩ : Fin 8) = stage := Fin.ext hRole
  obtain ⟨_,ends,⟨selected⟩⟩ :=
    Softmax.activeWarpOfMaximal hp hMax hg hWarp hCuQ hb hLo hHi
  have hAck peer (hs : SameWarp l g peer)
      (hMissing : ¬ ∃ j, Thread.Scores.CreditAcquired X (peer,j)) :
      Softmax.OpeningPollReady X (Softmax.waitLoc l peer
        (Softmax.stageOf (⟨warpIndex l g,hWarp⟩ : Fin 8)) 0) 1 := by
    have hSameWarp : warpIndex l g = warpIndex l peer := hs.2
    have hPeer : warpIndex l peer < 8 := hSameWarp ▸ hWarp
    have hPeerStage : warpIndex l peer / 4 = stage.val := by rwa [←hSameWarp]
    rw [hStage]
    obtain ⟨s,hs,hPhase⟩ := Protocol.Statistics.initialStatisticsPhaseZeroForPendingLane
      hp hMax hCuQ hs.1.2.1 hPeer stage hPeerStage.symm hMissing
    exact ⟨s,hs,by rw [hPhase]; decide⟩
  have hScore peer (hs : SameWarp l g peer)
      (hMissing : ¬ ∃ j, Thread.Scores.FirstScoreAcquire l X (peer,j)
        (Softmax.stageOf (⟨warpIndex l g,hWarp⟩ : Fin 8))) :
      Softmax.OpeningPollReady X (Softmax.waitLoc l peer
        (Softmax.stageOf (⟨warpIndex l g,hWarp⟩ : Fin 8)) 1) 0 := by
    have hSameWarp : warpIndex l g = warpIndex l peer := hs.2
    have hPeerStage : warpIndex l peer / 4 = stage.val := by rwa [←hSameWarp]
    have hCta : g/l.block = peer/l.block := hs.1.2.2
    rw [hStage] at hMissing ⊢
    obtain ⟨s,hs,hPhase⟩ :=
      openingScoreReadyForSoftmaxStage hp hMax hFrame hs.1.2.1 stage hPeerStage hb
        (hCta ▸ hLo) (hCta ▸ hHi) hMissing
    exact ⟨s,hs,by rw [hPhase]; decide⟩
  have hBias : let stage := Softmax.stageOf (⟨warpIndex l g,hWarp⟩ : Fin 8)
      Flow.okPolls (Thread.Loader.biasReadyObject l (g/l.block) stage) (X.tr g) = 0 →
      Softmax.OpeningPollReady X (Softmax.waitLoc l g stage 2) 0 := by
    dsimp only
    rw [hStage]
    intro hMissing
    obtain ⟨s,hs,hPhase⟩ :=
      openingBiasPhaseForSoftmaxStage hp hMax hFrame hg stage hRole hb hLo hHi hMissing
    exact ⟨s,hs,by rw [hPhase]; decide⟩
  obtain ⟨j,hAcquire,returned,hPosition,hCount,⟨scores⟩⟩ :=
    Softmax.openingBiasOfSelectedWarpWithWordsAndCount
    hp hMax hGuard hLayout hg hWarp hb hLo hHi hCuQ hUsedK selected hAck hScore hValues hBias
  exact ⟨j,hStage ▸ hAcquire,⟨⟨_,hStage,_,returned,hPosition,hCount,hStage ▸ scores⟩⟩⟩

/-- Every active softmax lane returns from its first Bias acquire in a maximal execution. -/
theorem openingSoftmaxBiasLaneOfAllStages {g batch : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hRole : warpIndex l g/4 = stage.val) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads) :
    ∃ j, Thread.Scores.FirstBiasAcquire l X g j stage ∧
      Nonempty (Softmax.OpeningBiasLane p l X g batch stage j) := by
  have hCuQ : DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hWords := Softmax.OpeningScoreWords.ofSelectedCta hp hMax.1 hCuQ hFrame hb hLo hHi
  exact openingSoftmaxBiasLaneOfWords hp hMax hFrame hWords hg stage hRole hb hLo hHi

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hRole : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hMax hFrame hg stage hRole hb hLo

/-- The opening Bias rendezvous returns its lane cursor for subsequent role progress. -/
theorem openingSoftmaxBiasCursorOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ j, Thread.Scores.FirstBiasAcquire l X g j stage ∧
      Nonempty (Softmax.OpeningBiasArrivalLane p l X g batch stage j) := by
  obtain ⟨j,hWait,⟨opening⟩⟩ := openingSoftmaxBiasLaneOfAllStages hp hMax hFrame
    hg stage hRole hb hLo hHi
  have hCuQ := (hFrame.metadataProtected hp).1
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  have hGuard := syncGuarded hp hMax.1 hCuQ
  obtain ⟨loaded⟩ := opening.readsOfMaximal hp hMax hGuard hCuQ hWait hg hWarp hb hLo hHi
    (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  exact ⟨j,hWait,loaded.arrivalOfMaximal hp hMax hg⟩

/-- Every lane of the selected softmax stage arrives at its opening Bias rendezvous. -/
theorem openingSoftmaxBiasArrivalOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ j, Softmax.FirstBiasArrival X g j stage := by
  obtain ⟨j,_,⟨arrived⟩⟩ :=
    openingSoftmaxBiasCursorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  exact ⟨j+66,arrived.observed⟩

end PTX.Kernels.TmlFa4Fwd.Progress
