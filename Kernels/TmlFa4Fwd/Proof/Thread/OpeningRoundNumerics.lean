-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstRound
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMaskCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningAffineLaunchScores
import Kernels.TmlFa4Fwd.Proof.SoftmaxNamedBarrierIds
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxAffine
import Kernels.TmlFa4Fwd.Proof.Termination
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The opening affine replay initializes the actual denominator for an arbitrary
number of blocks of a completed selected tile. -/
theorem OpeningAffineLane.firstRoundOfExit (hFrame : OutputFootprint p X) {g batch wait : Nat}
    {stage : Fin 2} (lane : OpeningAffineLane p l X g batch stage wait) {last pc : Nat}
    (hExit : X.get (g,last) = some ⟨pc,.exit⟩) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : 128*(2*(assignedCoordinates p batch (g/l.block)).1+stage.val)+(g%l.block)%128 <
      p.qLength batch) :
    let entry := lane.entry
    let warp := entry.arrival.loaded.opening.warp
    let coords := assignedCoordinates p batch (g/l.block)
    let blocks := Mma.trips p batch coords.1
    let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
    let past := p.kLength batch-p.qLength batch+256*coords.1
    FirstRoundProgress p l X warp g entry.pos batch coords.2
      (128*(2*coords.1+stage.val)+(g%l.block)%128) blocks cap past := by
  let entry := lane.entry
  let loaded := entry.arrival.loaded
  let warp := loaded.opening.warp
  let coords := assignedCoordinates p batch (g/l.block)
  let blocks := Mma.trips p batch coords.1
  let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
  let past := p.kLength batch-p.qLength batch+256*coords.1
  let base := 2*coords.1+stage.val
  let row := 128*base+(g%l.block)%128
  let raw := firstBiasLogit (abiFloat p.invScaleBits)
    (firstBiasRegisterValue (openingBiasColumns p l g batch stage)) (firstQkRegisterValue lane.dot)
  have hStage : stageOf warp = stage := loaded.opening.selectedStage
  have hIndex : entry.pos ≤ last := by
    by_contra! hEarly
    have hGet : ((X.tr g).take entry.pos)[last]? = some ⟨pc,.exit⟩ := by
      rwa [List.getElem?_take_of_lt hEarly]
    exact (entry.recorded.no_exit hGet).elim
  have hLast : ((X.tr g).drop entry.pos)[last-entry.pos]? = some ⟨pc,.exit⟩ := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  have hSuffix : Run kernel Assumptions.all l g entry.before ((X.tr g).drop entry.pos) none := by
    have hRun := entry.continuation
    cases hEnd : loaded.opening.ending with
    | none => exact hEnd ▸ hRun
    | some value => exact ((hEnd ▸ hRun).no_exit hLast).elim
  obtain ⟨s,hs,hAddresses,hRaw,hScale,hBar,hPath,hKeep⟩ := lane.maskCursorWithFrame hp
  have hMore : (X.tr g).drop entry.pos ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hLast
    simp at hLast
  have hRun := hSuffix.after_local_nonempty hPath hMore
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hBlock := (Mma.trips_bounds hp hb hTile).2.1
  have hBlocks : 128*(blocks-1) ≤ p.kLength batch := by
    change blocks ≤ (p.kLength batch+127)/128 at hBlock
    omega
  have hTid : g%l.block < 2^32 := by
    rw [hp.block]
    have := Nat.mod_lt g (by decide : 0 < 512)
    omega
  have hBound : row < p.qLength batch+256 := by change row < p.qLength batch at hRow; omega
  have hLive (col : Nat) (hc : col < 128) (hKey : visitKey blocks 0 col < p.keyCount batch row) :
      raw col = some (score p batch coords.2 row (visitKey blocks 0 col) /
        abiFloat p.scaleLog2Bits) := by
    have h := lane.maskedLogitOfLaunch hp hX hFrame hb hLo hHi ⟨col,hc⟩ hRow
    change firstMaskedValue p batch row blocks raw col =
      maskedLogit p batch coords.2 row (visitKey blocks 0 col) at h
    simpa only [firstMaskedValue,maskedLogit,ite_eq_left hKey] using h
  have hFields {x : Nat × Value} (hm : x ∈ openingScoreReturnedFacts p l g batch coords.1 warp) :
      loaded.cursor.ready.regs x.1 = some x.2 := holds_mem loaded.cursor.checkpoint.2.2.2.2 hm
  have hPast : past+256 = p.kLength batch-p.qLength batch+256*(coords.1+1) := by
    dsimp [past]
    omega
  have hLoop : Holds s.regs (firstLoopGeometry blocks cap past) := by
    refine ⟨?_,?_,?_,hs.2.2.2.2.1,trivial⟩
    · exact (hKeep _ (by decide) (by decide +kernel) (by decide)).trans
        (hFields (x := (1225,b32 (past+256))) (by
          simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts,hPast]))
    · exact (hKeep _ (by decide) (by decide +kernel) (by decide)).trans
        (hFields (x := (1226,b32 blocks)) (by
          simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts,blocks]))
    · exact (hKeep _ (by decide) (by decide +kernel) (by decide)).trans
        (hFields (x := (1228,b32 cap)) (by
          simp [openingScoreReturnedFacts,firstGeometryAckFacts,firstGeometryFacts,cap,blocks,
            hStage]))
  have hTail : Holds s.regs (tailFrame l warp) := by
    refine ⟨?_,?_,trivial⟩
    · exact (hKeep _ (by decide) (by decide +kernel) (by decide)).trans
        (hFields (x := (1062,b32 warp.val)) (by
          simp [openingScoreReturnedFacts,singleVisitGeometryCarry,biasFenceFacts,biasKeep]))
    · exact (hKeep _ (by decide) (by decide +kernel) (by decide)).trans
        (hFields (x := (2535,b32 l.sharedBase)) (by
          simp [openingScoreReturnedFacts,singleVisitGeometryCarry,biasFenceFacts,biasKeep]))
  have hProb (q : Fin 4) : s.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)) := by
    rw [hStage]
    exact holds_mem hAddresses (by fin_cases q <;> simp [firstAddressFacts,probabilityReg])
  have hPBase : s.regs 3217 = some (b32 (l.sharedBase+8*(stageOf warp).val)) := by
    rw [hStage]
    exact holds_mem hAddresses (by simp [firstAddressFacts])
  exact firstRoundFromScores hp warp raw hb hTid hBound hBlocks hs hRaw hLive hLoop hTail
    hScale hBar hProb hPBase hRun

/-- A completed lane has its actual initial denominator on the original trace.
A maximal extension can discharge the opening rendezvous without changing that lane's records. -/
theorem openingRoundOfCompletedLane (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (hWarp : Prologue.warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRow : 128*(2*(assignedCoordinates p batch (g/l.block)).1+Prologue.warpIndex l g/4)+
      (g%l.block)%128 < p.qLength batch) :
    let warp : Fin 8 := ⟨Prologue.warpIndex l g,hWarp⟩
    let stage := stageOf warp
    let coords := assignedCoordinates p batch (g/l.block)
    let blocks := Mma.trips p batch coords.1
    let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
    let past := p.kLength batch-p.qLength batch+256*coords.1
    ∃ pos, FirstRoundProgress p l X warp g pos batch coords.2
      (128*(2*coords.1+stage.val)+(g%l.block)%128) blocks cap past := by
  let warp : Fin 8 := ⟨Prologue.warpIndex l g,hWarp⟩
  let stage := stageOf warp
  obtain ⟨Y,hPrefix,hMax⟩ := maximalExtension hp hX
  obtain ⟨last,⟨pc,kind⟩,hx,hK⟩ := Thread.exitedOfComplete hX hDone hg
  change kind = .exit at hK
  subst kind
  have hy := Execution.le_get hPrefix hx
  have hLength := (X.exit_last hX hg hx).symm.trans (Y.exit_last hMax.1 hg hy)
  obtain ⟨suffix,hAppend⟩ := hPrefix.1 g
  have hSuffix : suffix = [] := by
    have hEq := congrArg List.length hAppend
    simp only [List.length_append] at hEq
    exact List.length_eq_zero_iff.mp (by omega)
  have hTrace : X.tr g = Y.tr g := by simpa only [hSuffix,List.append_nil] using hAppend
  obtain ⟨wait,⟨lane⟩⟩ := Progress.openingSoftmaxAffineOfAllStages hp hMax
    (hFootprint Y hMax.1) hg stage rfl hb hLo hHi
  have hRound := lane.firstRoundOfExit hp hMax.1 (hFootprint Y hMax.1) hy hb hLo hHi hRow
  let entry := lane.entry
  let w := entry.arrival.loaded.opening.warp
  have hNotify : Y.get (g,entry.pos) = some ⟨4397,.bar (3+w.val) (some 64) .arrive⟩ := by
    obtain ⟨_,_,_,_,_,he,_⟩ := hRound
    exact he
  have hWarpEq : w = warp := by
    apply Fin.ext
    have hID := actualSoftmaxStatsBarrierId hp hMax.1 (by decide : 4397 ∈ softmaxStatsSites)
      hNotify
    change w.val = Prologue.warpIndex l g
    omega
  refine ⟨entry.pos,?_⟩
  change FirstRoundProgress p l Y w g entry.pos batch _ _ _ _ _ at hRound
  rw [hWarpEq] at hRound
  unfold FirstRoundProgress at hRound ⊢
  simpa only [Execution.get,hTrace] using hRound

end
end PTX.Kernels.TmlFa4Fwd.Softmax
