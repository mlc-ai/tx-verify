-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitRound
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitScoreWrites
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitPublication
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasAddresses
import Kernels.TmlFa4Fwd.Proof.SoftmaxGroupCoordinates
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Step.ExitLast
import Kernels.TmlFa4Fwd.Proof.Thread.TmemDelayedLoadCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
import Kernels.TmlFa4Fwd.Proof.Thread.WorkSecondOutputCommit
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocatorExit
import Kernels.TmlFa4Fwd.Proof.Thread.Exit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Thread.Scores Epilogue Prologue

private theorem outputRegions {p : Params} {X : Execution} (h : OutputFootprint p X) :
    ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc := by
  intro w a bytes loc hw hCover hSpace
  rcases h w a bytes loc hw hCover hSpace with ho | ⟨q,hq,h,hh,k,hk,rfl⟩
  · exact .inl ho
  · exact .inr (lseByte_in hq hh hk)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    (hFootprint : OutputFootprint p X) (warp : Fin 8) {g j batch tile head biasCap pastTile : Nat}
    {t : TState} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCoords : assignedCoordinates p batch (g / l.block) = (tile, head))
    (hTrip : Mma.trips p batch tile = 1)
    (hRow : 128 * (2 * tile + (stageOf warp).val) + (g % l.block) % 128 < p.qLength batch)
    (ht : At t 3425 (singleVisitRoundFacts p l g warp batch tile biasCap pastTile))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp hX hComplete hFootprint warp hb hLo hHi hCoords hTrip hRow ht hr

/-- At the first score acquire, actual QK and Bias source events determine the first round
of a single-visit request. The identified tail PV destinations exclude overlap with the scores. -/
theorem singleVisitRoundOfObservedScoreEventsWithPhase :
    ∃ producer commit wait, FirstQkPhase l X (stageOf warp) producer g commit wait ∧
    ∃ qkFails biasFails,
      let fence := j + qkFails + 1 + 4 + biasFails + 1 + 64
      X.get (g, fence) = some ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, fence + 1) = some ⟨3583, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      (laneOf l g = 0 → X.get (g, fence + 2) =
        some ⟨3590, .arrive (signalLoc l g (stageOf warp) 0) 0 1 true .cta⟩) ∧
      FirstRoundProgress p l X warp g (if laneOf l g = 0 then fence + 3 else fence + 2)
        batch head (128 * (2 * tile + (stageOf warp).val) + (g % l.block) % 128)
        1 biasCap pastTile := by
  let stage := stageOf warp
  have hWaitFrame : At t 3425 [(2769,b32 (waitLoc l g stage 1).addr),(2770,b32 0)] := by
    apply ht.mono
    exact ⟨holds_mem ht.2.2.2.2 (by simp [singleVisitRoundFacts,stage]),
      holds_mem ht.2.2.2.2 (by simp [singleVisitRoundFacts]),trivial⟩
  obtain ⟨wait,hWait,hEarlier⟩ := firstObservedScoreWait hp hX stage hWaitFrame hr
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨output,spec,hOutput,hOutputCta⟩ := Thread.secondOutputCommitOfCompletedWork hp hX
    hComplete (g := g) (event_thread_lt hX hWait) hWork
  obtain ⟨last,⟨site,kind⟩,hExit,hKind⟩ :=
    Thread.exitedOfComplete hX hComplete (event_thread_lt hX hOutput.decoded)
  change kind = .exit at hKind
  subst kind
  obtain ⟨release,_,hDealloc⟩ :=
    Thread.mmaDeallocBeforeExit hp hX (hOutput.issuerWarp hp hX) hExit
  have hRelease := Thread.Deallocation.of_decoded hDealloc
  have hOne : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1 := by
    simpa [hCoords] using hTrip
  obtain ⟨producer,commit,hPhase⟩ := singleVisitFirstScorePhase hp hX hComplete hFootprint
    stage hb hLo hHi hOne hWait
  let hCta := hPhase.sameCta.2.2
  have hProdLo : tilePrefix p batch * p.heads ≤ producer/l.block := hCta.symm ▸ hLo
  have hProdHi : producer/l.block < tilePrefix p (batch+1) * p.heads := hCta.symm ▸ hHi
  have hProdTrip : Mma.trips p batch (assignedCoordinates p batch (producer/l.block)).1 = 1 :=
    hCta.symm ▸ hOne
  have hProdOutput : producer/l.block = output.1/l.block := hCta.trans hOutputCta
  refine ⟨producer,commit,wait,hPhase,?_⟩
  apply singleVisitRoundOfScoreLoads hp hX hComplete warp hb hLo hHi hCoords hTrip hRow
    (outputRegions hFootprint) ht ?_ hr
  intro read q vals hRead word
  have hLoad : Thread.DelayedScoreLoad X (g,read) false q :=
    Thread.DelayedScoreLoad.of_decoded hRead
  obtain ⟨done,hReadDone,hDone,_⟩ :=
    Thread.delayedScoreLoadWaitRecordedBeforeRelease hp hX (i := (g,read)) (d := (output.1,release))
      hOutputCta
      hLoad hRelease
  have hWaitRead := hEarlier read q vals _ hRead
  have hValue := singleVisitScoreWord hp hX hComplete hFootprint hb hProdLo hProdHi hProdTrip
    hPhase hOutput hProdOutput q word hRead hWaitRead hDone hReadDone
    (fun start hIssues => singleVisitScoreOutsideWrites hp hX hComplete hFootprint hb
      hProdLo hProdHi hProdTrip hPhase hOutput hProdOutput hIssues hWaitRead hReadDone hDone
      q word)
  have hAssigned : assignedCoordinates p batch (producer/l.block) = (tile,head) :=
    hCta.symm ▸ hCoords
  simpa [hAssigned,stage,show 256*tile + 128*(stageOf warp).val =
    128 * (2*tile + (stageOf warp).val) by omega, Nat.add_assoc] using hValue

end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    (hFootprint : OutputFootprint p X) {g batch : Nat} (hWarp : warpIndex l g < 8)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRow : 128 * (2 * (assignedCoordinates p batch (g/l.block)).1 +
      (stageOf ⟨warpIndex l g,hWarp⟩).val) + (g % l.block) % 128 < p.qLength batch)
include hp hX hComplete hFootprint hWarp hb hLo hHi hTrip hRow

/-- A complete one-visit lane has its numerical first-round cursor on the selected work item. -/
theorem singleVisitObservedFirstRoundWithPhase (hg : g < l.threads) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    let coords := assignedCoordinates p batch (g/l.block)
    let row := 128 * (2 * coords.1 + (stageOf warp).val) + (g % l.block) % 128
    ∃ pos producer commit wait, FirstQkPhase l X (stageOf warp) producer g commit wait ∧
      FirstRoundProgress p l X warp g pos batch coords.2 row 1
      (1 - stageGeometryBlocks p batch coords.1 (stageOf warp) + 10)
      (p.kLength batch - p.qLength batch + 256 * coords.1) := by
  dsimp only
  have hExited := Thread.exitedOfComplete hX hComplete hg
  obtain ⟨last,⟨exitPc,kind⟩,hExit,hKind⟩ := hExited
  change kind = .exit at hKind
  subst kind
  have hExitPc := actualExitPc hX hExit
  let src := laneOf l g
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  have hSame : warpLane l g src = g := by
    apply Nat.sub_add_cancel
    exact (Nat.mod_le _ _).trans (Nat.mod_le _ _)
  have hExitAt : X.get (warpLane l g src,last) = some ⟨exitPc,.exit⟩ := hSame.symm ▸ hExit
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨chosen,_,hc,hChosenLo,hChosenHi,ends,cur,hFollow⟩ :=
    activeTileOfEvent hp hX hg hWarp hSrc hWork (hFootprint.metadataProtected hp).1 hExitAt
      (by change 3231 < exitPc; omega)
  have hBatch : chosen = batch := by
    obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
    exact (hUnique chosen ⟨hc,hChosenLo,hChosenHi⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst chosen
  have hLast : ((X.tr (warpLane l g src)).drop (cur.pos src))[last-cur.pos src]? =
      some ⟨exitPc,.exit⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hFollow.before]
    exact hExitAt
  have hRun := cur.continuation src hSrc
  have hEnds : ends src = none := by
    cases hEnd : ends src with
    | none => rfl
    | some _ =>
      rw [hEnd] at hRun
      exact (hRun.no_exit hLast).elim
  rw [hEnds] at hRun
  have hRun := hRun.after_local_nonempty (cur.localSteps src hSrc) hFollow.nonempty
  have ht := cur.checkpoint src hSrc
  rw [hSame] at hRun
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  obtain ⟨_,_,_,hReady,hR⟩ :=
    firstActiveSingleVisitGeometry hp hX warp hb hLo hHi hTrip ht (outputRegions hFootprint) hRun
  obtain ⟨producer,commit,wait,hPhase,_,_,_,_,_,hRound⟩ :=
    singleVisitRoundOfObservedScoreEventsWithPhase hp hX hComplete hFootprint warp hb hLo hHi
      (Prod.eta _).symm hTrip hRow hReady hR
  exact ⟨_,producer,commit,wait,hPhase,hRound⟩

/-- A complete one-visit lane has its numerical first-round cursor on the selected work item. -/
theorem singleVisitObservedFirstRound (hg : g < l.threads) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    let coords := assignedCoordinates p batch (g/l.block)
    let row := 128 * (2 * coords.1 + (stageOf warp).val) + (g % l.block) % 128
    ∃ pos, FirstRoundProgress p l X warp g pos batch coords.2 row 1
      (1 - stageGeometryBlocks p batch coords.1 (stageOf warp) + 10)
      (p.kLength batch - p.qLength batch + 256 * coords.1) := by
  obtain ⟨pos,_,_,_,_,hRound⟩ :=
    singleVisitObservedFirstRoundWithPhase hp hX hComplete hFootprint hWarp hb hLo hHi hTrip hRow hg
  exact ⟨pos,hRound⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    (hFootprint : OutputFootprint p X) {g batch publication : Nat} (hWarp : warpIndex l g < 8)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRow : 128 * (2 * (assignedCoordinates p batch (g/l.block)).1 +
      (stageOf ⟨warpIndex l g,hWarp⟩).val) + (g % l.block) % 128 < p.qLength batch)
include hp hX hComplete hFootprint hWarp hb hLo hHi hTrip hRow

/-- The observed terminal publication of a single-visit lane carries the numerical
sum and maximum recovered from the actual scheduler, QK, and Bias traces. -/
theorem singleVisitObservedFinalPublicationWithReference
    (hFinal : Publishes X (g,publication) .final) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    let coords := assignedCoordinates p batch (g/l.block)
    let row := 128 * (2 * coords.1 + (stageOf warp).val) + (g % l.block) % 128
    ∃ (maximum sum : ℝ),
      SoftmaxSumRun p batch coords.2 row 1 (fun _ => some (abiFloat p.scaleLog2Bits * maximum))
        (fun _ => sum) ∧
      firstReference p batch coords.2 row 1 = abiFloat p.scaleLog2Bits * maximum ∧
      X.get (g, publication-2) = some ⟨7614,.wr (statsAcc l g warp 2) (fl sum).toBytes⟩ ∧
      X.get (g, publication-2+1) = some ⟨7615,.wr (statsAcc l g warp 3) (fl maximum).toBytes⟩ ∧
      X.get (g, publication) = some ⟨7616,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      2 ≤ publication := by
  dsimp only
  have hFinalRecord := hFinal
  obtain ⟨event,hEvent,_⟩ := hFinalRecord
  have hg : g < l.threads := event_thread_lt hX hEvent
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  obtain ⟨_,hRound⟩ :=
    singleVisitObservedFirstRound hp hX hComplete hFootprint hWarp hb hLo hHi hTrip hRow hg
  have hExited := Thread.exitedOfComplete hX hComplete hg
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hLen := (hp.lengths batch hb).2
  exact singleVisitAtFinalPublicationWithReference hp hX warp rfl hb hRow
    (by omega) (by omega) (by omega) hRound hExited hFinal

/-- The observed terminal publication of a single-visit lane carries the numerical
sum and maximum recovered from the actual scheduler, QK, and Bias traces. -/
theorem singleVisitObservedFinalPublication (hFinal : Publishes X (g,publication) .final) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    let coords := assignedCoordinates p batch (g/l.block)
    let row := 128 * (2 * coords.1 + (stageOf warp).val) + (g % l.block) % 128
    ∃ (maximum sum : ℝ),
      SoftmaxSumRun p batch coords.2 row 1 (fun _ => some (abiFloat p.scaleLog2Bits * maximum))
        (fun _ => sum) ∧
      X.get (g, publication-2) = some ⟨7614,.wr (statsAcc l g warp 2) (fl sum).toBytes⟩ ∧
      X.get (g, publication-2+1) = some ⟨7615,.wr (statsAcc l g warp 3) (fl maximum).toBytes⟩ ∧
      X.get (g, publication) = some ⟨7616,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      2 ≤ publication := by
  obtain ⟨maximum,sum,hVisits,_,hSum,hMax,hPub,hLen⟩ :=
    singleVisitObservedFinalPublicationWithReference hp hX hComplete hFootprint hWarp hb
      hLo hHi hTrip hRow hFinal
  exact ⟨maximum,sum,hVisits,hSum,hMax,hPub,hLen⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
