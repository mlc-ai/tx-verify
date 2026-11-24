-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxSingleVisitRetire
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityAck

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Protocol.Statistics

/-- The lane's actual final statistics arrival has completed its named generation. -/
def SingleVisitSoftmaxRelease (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ j, Scores.Publishes X (g,j) .final → j+1 = (X.tr g).length →
    CtaBarrier.Released l.block (X.barriers (g/l.block)) (3+warpIndex l g)
      (((X.tr g).take j).countP (Execution.isBarId (3+warpIndex l g)))

private theorem singleVisitTerminalInputsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hOne : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRelease : SingleVisitSoftmaxRelease l X g) :
    Nonempty (Softmax.SingleVisitTerminalInput p l X g) := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  let stage := Softmax.stageOf warp
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  let cap := blocks-Softmax.stageGeometryBlocks p batch tile stage+10
  let past := p.kLength batch-p.qLength batch+256*tile
  have hCount : blocks = 1 := hOne
  have hCap : 0 < cap ∧ cap < 2^31 := by dsimp only [cap]; omega
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨_,_,hLimit⟩ := Mma.trips_bounds hp hb hTile
  have hPast : past+256 < 2^31 := by
    change p.kLength batch-p.qLength batch+256*(tile+1) < 2^31 at hLimit
    change (p.kLength batch-p.qLength batch+256*tile)+256 < 2^31
    simpa only [Nat.mul_succ,Nat.add_assoc] using hLimit
  obtain ⟨ack⟩ := openingProbabilityAckOfMaximal hp hMax hFrame hg stage rfl hb hLo hHi
    (fun _ => hOne.symm ▸ Nat.one_lt_two)
  obtain ⟨denom⟩ := ack.denominatorOfMaximal hp hMax hFrame hg stage rfl hb hLo hHi
  let c : Softmax.OpeningDenominatorCursor p l X g 1 cap past := hCount ▸ denom
  refine ⟨⟨cap,past,c,hCap.1,hCap.2,hPast,?_⟩⟩
  intro hLast
  have hPub := (c.publishSingleVisitAtCursor hp hMax (hFrame.metadataProtected hp).1
    hg hw hCap.1 hCap.2 hPast).1
  exact hRelease _ hPub (by omega)

/-- After both roles have handed off the terminal statistics, every lane of a single-visit
softmax warp records its actual final allocation arrival. -/
theorem singleVisitSoftmaxAllocationArrivalsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hDeps : CreditAcquireDependencies l X)
    {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hOne : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hCredits : TerminalCorrectionCredits l X (g/l.block) (Softmax.stageOf ⟨warpIndex l g,hw⟩) 1)
    (hRelease : ∀ lane < 32, SingleVisitSoftmaxRelease l X (warpLane l g lane)) :
    ∀ lane < 32, ∃ j, FinalAllocationArrival X (warpLane l g lane,j) .arrive := by
  apply Softmax.allocationArrivalsOfSingleVisitWarp hp hMax (hFrame.metadataProtected hp).1 hDeps
    hg hw hb hLo hHi hOne hCredits
  intro lane hl
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hCTA : warpLane l g lane/l.block = g/l.block := hSame.1.2.2.symm
  have hWarp : warpIndex l g = warpIndex l (warpLane l g lane) := hSame.2
  apply singleVisitTerminalInputsOfMaximal (g := warpLane l g lane)
    hp hMax hFrame hSame.1.2.1 (hWarp ▸ hw) hb
    (hCTA.symm ▸ hLo) (hCTA.symm ▸ hHi) _ (hRelease lane hl)
  rwa [hCTA]

end PTX.Kernels.TmlFa4Fwd.Progress
