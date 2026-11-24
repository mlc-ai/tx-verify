-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionTerminal
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningStatistics
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
import Kernels.TmlFa4Fwd.Proof.Protocol.Statistics
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuseClosure
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningStatisticsCredit
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue Thread

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hMax hFrame hg hRole hb hLo hHi

private theorem openingCorrectionFirstCursorOfMaximal :
    Nonempty (Correction.OpeningCorrectionStatistics p l X g batch (laneOf l g) 0) := by
  have hCuQ : DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hUsedK k (_ : k < 4) w a bytes (hw : X.MemWrites w a bytes) :
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k) :=
    hp.inputByte_unwritten (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
      (region := ⟨p.usedKBase,4*p.batch⟩)
      (by simp [Params.inputRegions])
      (by simp only [Region.Contains,globalLoc,Loc.at,true_and]; omega) hw
  have hl : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  exact Correction.openingCorrectionFirstStatisticsOfMaximal hp hMax hg
    hRole.1 hRole.2 hCuQ hb hLo hHi hUsedK (laneOf l g) hl

/-- Each active correction lane records its initial stage-zero statistics rendezvous. -/
theorem openingCorrectionFirstStatisticsOfMaximal :
    ∃ j, CorrectionWaits X (g,j) .initial 0 := by
  obtain ⟨c⟩ := openingCorrectionFirstCursorOfMaximal hp hMax hFrame hg hRole hb hLo hHi
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  exact ⟨c.index,by simpa only [hSelf] using c.waited⟩

omit hp hMax hFrame hg hRole hb hLo hHi in
/-- If a correction lane ends at its initial statistics wait, the matched producer
and consumer arrivals release it in a maximal execution with the same trace. -/
theorem openingCorrectionStatisticsReleasedHistory {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hWait : CorrectionWaits X (g,(X.tr g).length-1) .initial stage)
    (hPeers : ∀ h, h < l.threads → h/l.block = g/l.block →
      8 ≤ warpIndex l h → warpIndex l h < 12 → ∃ j, CorrectionWaits X (h,j) .initial stage) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  let idx := warpIndex l g % 4+4*stage.val
  have hs := stage.isLt
  have hmod := Nat.mod_lt (warpIndex l g) (show 0 < 4 by decide)
  let w : Fin 8 := ⟨idx,by dsimp [idx]; omega⟩
  let id := 3+w.val
  have hId : Correction.statsBarrierId l g stage = id := by
    dsimp [Correction.statsBarrierId,id,w,idx]
    omega
  have hWarp : 8+w.val%4 = warpIndex l g := by
    dsimp [w,idx]
    omega
  have hStage : w.val/4 = stage.val := by dsimp [w,idx]; omega
  have hSources := statsBarrierSources hp hMax.1 w
  have hBar : BarrierArrival X (g,(X.tr g).length-1) id (some 64) .sync :=
    hId ▸ initialCorrectionStatisticsBarrier hp hMax.1 hWait
  have hOrdinal : observedBarrierOrdinal X (g,(X.tr g).length-1) id = 0 := by
    have hSrc : NamedBar.Sources l X (some 64) (statsParticipants w)
        (Correction.statsBarrierId l g stage) := by rw [hId]; exact hSources
    rw [← hId]
    exact (correctionBarrierOrdinal ..).symm.trans
      (correctionInitialWaitOrdinal hp hMax.1 hWait hSrc)
  refine releaseSynchronization hMax (fun Y hY _ hWrites => ?_) hg
    (statsBarrierShape hp w) hSources hBar ?_
  · apply Protocol.noActualNamedBarrierFault hp hY
    have hCuQ : DrainCuQProtected p X :=
      hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
    intro i hi k hk w a bytes he
    exact hCuQ i hi k hk w a bytes (hWrites ▸ he)
  · intro lane hl hMember
    let peer := g/l.block*l.block+lane
    have hpT : peer < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hl
    have hbL : 0 < l.block := by rw [hp.block]; decide
    obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := g/l.block) hbL hl
    change peer/l.block = g/l.block at hOwner
    change peer%l.block = lane at hLocal
    simp only [statsParticipants,Finset.mem_insert,Finset.mem_singleton] at hMember
    have hPeerWarp : warpIndex l peer = lane/32 := by rw [warpIndex,hLocal]
    rw [hOrdinal]
    rcases hMember with hW | hW
    · have hSoft : warpIndex l peer = w.val := hPeerWarp.trans hW
      obtain ⟨j,hPub⟩ := openingStatisticsOfMaximal hp hMax hFrame hpT stage
        (by rw [hSoft]; exact hStage) hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi)
      have hSrc : NamedBar.Sources l X (some 64) (statsParticipants w) (3+warpIndex l peer) := by
        rw [hSoft]
        exact hSources
      have hZero := Scores.firstOrdinal hp hMax.1 hPub hSrc
      have hArrive := openingSoftmaxStatisticsBarrier hp hMax.1 hPub
      rw [hSoft] at hArrive hZero
      have hExt := barrierArrivalExtent hArrive
      rw [Scores.barrierOrdinal] at hZero
      change observedBarrierOrdinal X (peer,j) id = 0 at hZero
      exact hZero ▸ hExt
    · have hCorrection : warpIndex l peer = warpIndex l g := hPeerWarp.trans (hW.trans hWarp)
      obtain ⟨j,hw⟩ := hPeers peer hpT hOwner (hCorrection.symm ▸ hRole.1)
        (hCorrection.symm ▸ hRole.2)
      have hPeerId : Correction.statsBarrierId l peer stage = id := by
        simpa only [Correction.statsBarrierId,hCorrection] using hId
      have hSrc : NamedBar.Sources l X (some 64) (statsParticipants w)
          (Correction.statsBarrierId l peer stage) := by rw [hPeerId]; exact hSources
      have hZero := correctionInitialWaitOrdinal hp hMax.1 hw hSrc
      have hArrive := initialCorrectionStatisticsBarrier hp hMax.1 hw
      rw [hPeerId] at hArrive hZero
      have hExt := barrierArrivalExtent hArrive
      rw [correctionBarrierOrdinal] at hZero
      change observedBarrierOrdinal X (peer,j) id = 0 at hZero
      exact hZero ▸ hExt

private theorem openingCorrectionSecondCursorAndCreditOfMaximal :
    (∃ j, X.Arrive (g,j) (Correction.statsCreditLoc l (g/l.block) 0) 0 1 true .cta) ∧
      Nonempty (Correction.OpeningCorrectionStatistics p l X g batch (laneOf l g) 1) := by
  obtain ⟨c⟩ := openingCorrectionFirstCursorOfMaximal hp hMax hFrame hg hRole hb hLo hHi
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨he,next⟩ := c.secondAndCreditOfMaximal hp hMax (hSelf.symm ▸ hg) (by
    intro hLast
    rw [hSelf] at hLast ⊢
    have hIndex : (X.tr g).length-1 = c.index := by omega
    have hWait : CorrectionWaits X (g,(X.tr g).length-1) .initial 0 := by
      simpa only [hSelf,hIndex] using c.waited
    obtain ⟨Y,hY,hTrace,_,hReady⟩ := openingCorrectionStatisticsReleasedHistory hp hMax hFrame
      hg hRole 0 hb hLo hHi hWait (fun h hh hCta hwLo hwHi =>
        openingCorrectionFirstStatisticsOfMaximal hp hMax hFrame hh ⟨hwLo,hwHi⟩ hb
          (hCta.symm ▸ hLo) (hCta.symm ▸ hHi))
    exact ⟨Y,hY,hTrace,hReady⟩)

  exact ⟨⟨c.index+1,by
    simpa only [hSelf,Correction.statsCreditLoc,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using he⟩,
    next⟩

private theorem openingCorrectionSecondCursorOfMaximal :
    Nonempty (Correction.OpeningCorrectionStatistics p l X g batch (laneOf l g) 1) :=
  (openingCorrectionSecondCursorAndCreditOfMaximal hp hMax hFrame hg hRole hb hLo hHi).2

/-- The returned first correction statistics rendezvous enables the second stage's arrival. -/
theorem openingCorrectionSecondStatisticsOfMaximal :
    ∃ j, CorrectionWaits X (g,j) .initial 1 := by
  obtain ⟨next⟩ := openingCorrectionSecondCursorOfMaximal hp hMax hFrame hg hRole hb hLo hHi
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  exact ⟨next.index,by simpa only [hSelf] using next.waited⟩

/-- A scheduled correction lane has both opening statistics arrivals in a maximal trace. -/
theorem openingCorrectionStatisticsOfMaximal (stage : Fin 2) :
    ∃ j, CorrectionWaits X (g,j) .initial stage := by
  fin_cases stage
  · exact openingCorrectionFirstStatisticsOfMaximal hp hMax hFrame hg hRole hb hLo hHi
  · exact openingCorrectionSecondStatisticsOfMaximal hp hMax hFrame hg hRole hb hLo hHi

omit hp hMax hFrame hg hRole hb hLo hHi in
/-- Each opening correction statistics wait can return when it is the lane's last event. -/
theorem openingCorrectionStatisticsReadyOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hWait : CorrectionWaits X (g,(X.tr g).length-1) .initial stage) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g :=
  openingCorrectionStatisticsReleasedHistory hp hMax hFrame hg hRole stage hb hLo hHi hWait
    (fun _ hh hCta hwLo hwHi => openingCorrectionStatisticsOfMaximal hp hMax hFrame hh
      ⟨hwLo,hwHi⟩ hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) stage)

private theorem secondStatisticsCursorWithRelease
    : ∃ c : Correction.OpeningCorrectionStatistics p l X g batch (laneOf l g) 1,
      c.index+1 = (X.tr (warpLane l g (laneOf l g))).length →
        ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
          Step.Released l Y (warpLane l g (laneOf l g)) := by
  obtain ⟨c⟩ := openingCorrectionSecondCursorOfMaximal hp hMax hFrame hg hRole hb hLo hHi
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  refine ⟨c,?_⟩
  intro hLast
  rw [hSelf] at hLast ⊢
  have hIndex : (X.tr g).length-1 = c.index := by omega
  have hWait : CorrectionWaits X (g,(X.tr g).length-1) .initial 1 := by
    simpa only [hSelf,hIndex] using c.waited
  obtain ⟨Y,hY,hTrace,_,hRel⟩ :=
    openingCorrectionStatisticsReadyOfMaximal hp hMax hFrame hg hRole 1 hb hLo hHi hWait
  exact ⟨Y,hY,hTrace,hRel⟩

/-- Every correction lane assigned one visit joins its first terminal statistics rendezvous. -/
theorem openingCorrectionFirstTerminalOfMaximal
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2) :
    ∃ j, CorrectionWaits X (g,j) .terminal 0 := by
  obtain ⟨c,hRelease⟩ := secondStatisticsCursorWithRelease hp hMax hFrame hg hRole hb hLo hHi
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  rw [← hSelf]
  exact c.firstTerminalOfMaximal hp hMax (hSelf.symm ▸ hg) hb hLo hHi hSingle hRelease

/-- Every active correction lane returns the stage-zero credit. A single visit also
returns the stage-one credit in the finalizer preheader. -/
theorem openingCorrectionCreditOfMaximal (stage : Fin 2)
    (hSingle : stage.val = 1 → Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2) :
    ∃ j, X.Arrive (g,j) (Correction.statsCreditLoc l (g/l.block) stage) 0 1 true .cta := by
  fin_cases stage
  · exact (openingCorrectionSecondCursorAndCreditOfMaximal hp hMax hFrame hg hRole hb hLo hHi).1
  · obtain ⟨c,hRelease⟩ := secondStatisticsCursorWithRelease hp hMax hFrame hg hRole hb hLo hHi
    have hSelf : warpLane l g (laneOf l g) = g :=
      Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
    obtain ⟨he,_⟩ :=
      c.firstTerminalAndCreditOfMaximal hp hMax (hSelf.symm ▸ hg) hb hLo hHi (hSingle rfl) hRelease
    exact ⟨c.index+1,by simpa only [hSelf,Correction.statsCreditLoc] using he⟩
end

/-- The first statistics reuse object advances in every active CTA. The second one
also advances when the selected tile has a single KV visit. -/
theorem openingStatsSlotAdvancedOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (stage : Fin 2)
    (hSingle : stage.val = 1 → Mma.trips p batch (assignedCoordinates p batch cta).1 < 2) :
    let log := X.objects (Correction.statsCreditLoc l cta stage)
    ∃ s, MBarrier.stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  have hCuQ := hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hUsedK : UsedKProtected p X := by
    intro i hi k hk w a bytes he
    exact hp.inputByte_unwritten (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
      (region := ⟨p.usedKBase,4*p.batch⟩) (by simp [Params.inputRegions])
      (by simp only [Region.Contains,globalLoc,Loc.at,true_and]; omega) he
  have hBound := Protocol.Statistics.countedExitCreditBound hp hMax.1 hCuQ hUsedK
  have hDeps := Protocol.Statistics.creditDependenciesOfCountedExitBound hp hMax.1 hBound
  apply Protocol.Statistics.openingSlotAdvancedOfCredits hp hMax.1 hDeps stage
  intro lane
  let thread := Correction.statsCreditLane l cta lane
  have hl : 256+lane.val < l.block := by rw [hp.block]; have := lane.isLt; omega
  have hg : thread < l.threads := by
    unfold thread Correction.statsCreditLane
    have h := NamedBar.cta_thread_lt hc hl
    simpa only [Nat.add_assoc] using h
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta) hBlock hl
  have hCta : thread/l.block = cta := by
    simpa only [thread,Correction.statsCreditLane,Nat.add_assoc] using hOwner
  have hLane : thread%l.block = 256+lane.val := by
    simpa only [thread,Correction.statsCreditLane,Nat.add_assoc] using hLocal
  have hRole : 8 ≤ warpIndex l thread ∧ warpIndex l thread < 12 := by
    rw [warpIndex,hLane]
    have := lane.isLt
    omega
  obtain ⟨j,he⟩ := openingCorrectionCreditOfMaximal hp hMax hFrame hg hRole hb
    (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) stage (hCta.symm ▸ hSingle)
  rw [hCta] at he
  exact ⟨j,he⟩

end PTX.Kernels.TmlFa4Fwd.Progress
