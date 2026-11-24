-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PvProbabilityTile
public import Kernels.TmlFa4Fwd.Proof.MmaPvNumerics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.TcMma PTX.Kernels.TmlFa4Fwd.Mma PTX.Kernels.TmlFa4Fwd.Softmax
open PTX.Kernels.TmlFa4Fwd.Epilogue (assignedCoordinates stageRow)
open PTX.Kernels.TmlFa4Fwd.Protocol.Scores (probabilityProducer)
open PTX.Kernels.TmlFa4Fwd.Thread.Scores

noncomputable section

/-- The selected probability words and the actual carry give a complete weighted
block in the PV output cell, using the launch's paged value operands. -/
theorem PvVisit.resultOfShiftedTile {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {g index batch use : Nat} {block : Fin 4} {row col : Fin 128}
    (visit : PvVisit l X g block use row col index)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (reference carry : ℝ) (hDone : X.async.mmaDone (g,index) = true) :
    let coords := assignedCoordinates p batch (g/l.block)
    let stage := (pvSite block).stage
    let qrow := stageRow coords.1 stage + row.val
    let blocks := trips p batch coords.1
    let weights := fun k =>
      shiftedWeight p batch coords.2 qrow (visitKey blocks (use/2) k) reference
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    ObservedProbabilityTile l X (probabilityProducer l (g/l.block) stage row.val) stage
      (use/2) weights →
    (visit.keep = false → carry = 0) →
    (visit.keep = true → ∃ source, ReadSource l X .acc source (g,visit.issues 0) cell ∧
      (TcMma.Result l Assumptions.all X source cell (.float .f32 carry) ∨
        StoreValue l X source cell (.float .f32 carry))) →
    TcMma.Result l Assumptions.all X (g,index) cell (.float .f32 (carry +
      (2 : ℝ)^(-reference) * maskedBlockSum (p.keyCount batch qrow) blocks (use/2)
        (weightedValue p batch coords.2 qrow col.val))) := by
  dsimp only
  intro hTile hZero hCarry
  let coords := assignedCoordinates p batch (g/l.block)
  let stage := (pvSite block).stage
  let qrow := stageRow coords.1 stage + row.val
  let blocks := trips p batch coords.1
  let weights := fun k => shiftedWeight p batch coords.2 qrow (visitKey blocks (use/2) k) reference
  have result := visit.resultOfProbabilities hp hX hFrame hCuQ hb hLo hHi weights carry hDone
    (fun step _ hOps _ hk => visit.probabilityElementOfTile hp hX hCuQ step weights hTile hOps hk)
    hZero hCarry
  change TcMma.Result l Assumptions.all X (g,index)
    ⟨g/l.block,row.val,outputColumn stage+col.val⟩ (.float .f32 (carry +
      ∑ k ∈ Finset.range 128, shiftedWeight p batch coords.2 qrow
        (visitKey blocks (use/2) k) reference * pvValue p batch coords.2
          (visitKey blocks (use/2) k) col.val)) at result
  rwa [pvMaskedWeightedBlock] at result

end
end PTX.Kernels.TmlFa4Fwd.Protocol
