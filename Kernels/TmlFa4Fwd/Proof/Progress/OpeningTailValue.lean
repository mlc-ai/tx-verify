-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningValueReady
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSecondScoreReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailValueProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningKeyContinue
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstQueryProgress
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstGroupShuffles
import Kernels.TmlFa4Fwd.Proof.Progress.FirstQueryAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hMax hFrame hg hw hb hLo

/-- The post-opening MMA warp retains the exact trip count from the selected metadata. -/
theorem openingKeyReturnedWithTripsOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ shuffles votes ends, Nonempty (Mma.OpeningKeyReturnedWithTrip l X g
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) shuffles votes ends) := by
  obtain ⟨shuffles,votes,ends,hReached,_⟩ :=
    openingSecondScoreAndKeyReturnOfMaximal hp hMax hFrame hg hw hb hLo hHi
  obtain ⟨⟨cur⟩,_⟩ := Mma.openingKeyReleaseAndContinueFromWarp hp hMax hg hReached
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hProtect : DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hCuQ off (ho : off ≤ 1) k (hk : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + off))).at k) :=
    hp.inputByte_unwritten (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
      (region := ⟨p.cuQBase, 4 * (p.batch + 1)⟩) (by simp [Params.inputRegions])
      (by simp only [Region.Contains, globalLoc, Loc.at, true_and]; omega) hw
  have hUsedK k (hk : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k) :=
    hp.inputByte_unwritten (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
      (region := ⟨p.usedKBase, 4 * p.batch⟩) (by simp [Params.inputRegions])
      (by simp only [Region.Contains, globalLoc, Loc.at, true_and]; omega) hw
  refine ⟨shuffles,votes,ends,cur.advanceLocal ?_⟩
  intro lane hl
  have hs := (Step.sameWarp_lane hBlock hg hl).1
  have hLo' := hs.1.2.2 ▸ hLo
  have hHi' := hs.1.2.2 ▸ hHi
  have hTile := (assignedCoordinates_valid hp hLo' hHi').1
  obtain ⟨_,_,_,_,hPos,hBound,_,_,hReleased,hAt,hPast,hLocal,hRest⟩ :=
    Thread.Allocation.mmaMetadataOfMaximal hp hMax hs.1.2.1 (hs.2.symm.trans hw)
      hProtect hb hLo' hHi'
  have hReady := openingQueryReadyPhaseOfMaximal hp hMax hFrame
    (NamedBar.cta_lt hs.1.2.1) hb hLo' hHi'
  obtain ⟨_,_,_,he,hPrefix,_,hNext,hTrip⟩ :=
    Mma.selectedFirstQueryWaitOfMaximal hp hMax hs.1.2.1 hb hTile hAt hCuQ hUsedK hReady
      hPast hLocal hRest hPos hBound hReleased
  have hh := cur.checkpoint lane hl
  have hReg := Mma.openingTripAtKeyReturn (hTrip.mono ⟨hTrip.2.2.2.2.2.2.1,trivial⟩)
    hh.1 (len_of_get he) (cur.bounded lane hl) hPrefix (cur.recorded lane hl) hNext
    (cur.localSteps lane hl)
  rw [← hs.1.2.2] at hReg
  exact ⟨_,.refl,hh.mono ⟨hReg,hh.2.2.2.2⟩⟩

/-- For one selected KV visit, both query buffers return and the opening value acquire is recorded
in every MMA lane. The result is independent of termination of the final PV body. -/
theorem singleVisitOpeningTailValueOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    (∀ stage : Fin 2, ∃ issuer index, SameWarp l g issuer ∧
      X.Commit (issuer,index) (Mma.commitSpec l issuer (l.sharedBase+16+8*stage.val))) ∧
    ∀ lane < 32, ∃ j, Thread.Mma.ReadyPoll l X (warpLane l g lane) j 1 0 true .cta := by
  obtain ⟨_,_,_,⟨cur⟩⟩ := openingKeyReturnedWithTripsOfMaximal hp hMax hFrame hg hw hb hLo hHi
  obtain ⟨⟨ready⟩,hQuery⟩ := Mma.openingTailValueReachedOfMaximal hp hMax hg (hSingle ▸ cur)
  refine ⟨hQuery,fun lane hl => ?_⟩
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hs := (Step.sameWarp_lane hBlock hg hl).1
  rcases openingValueReadyPhaseOrAcquireOfMaximal hp hMax hFrame hs.1.2.1
    (hs.2.symm.trans hw) hb (hs.1.2.2 ▸ hLo) (hs.1.2.2 ▸ hHi) with hPhase | ⟨j,hPoll,_⟩
  · simp only [Thread.Loader.readyObject,← hs.1.2.2] at hPhase
    exact Mma.openingTailValueWaitOfMaximal hp hMax hg ready hPhase lane hl
  · exact ⟨j,hPoll⟩

end PTX.Kernels.TmlFa4Fwd.Progress
