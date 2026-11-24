-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitBiasWordOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstBiasReadReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.FirstBiasReadReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.FirstBiasObservation
import Kernels.TmlFa4Fwd.Proof.LoaderBiasIssueOrigin

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.AsyncCopy Thread.Scores Thread.Loader Prologue Epilogue
open Protocol.Bias (AcquiredBiasBox)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The first Bias word keeps its observed generation-zero source even when later
transfers overwrite the same Bias buffer. -/
theorem firstBiasWordOrderOfOpeningBoxInPrefix {g wait read : Nat} {stage : Fin 2} (i : Fin 16)
    (word : Fin 4) (hWarp : warpIndex l g < 8) {tensor : EvId} {o : TensorCopy.Observation}
    (hWait : FirstBiasAcquire l X g wait stage)
    (hBox : AcquiredBiasBox p l X stage g wait tensor (biasVectorHalf i) o)
    (hOpening : biasTensorOrdinal l X stage (biasVectorHalf i) tensor = 0)
    (hRead : FirstBiasWordRead X (g,read)) :
    BiasWordOrder p l X stage false i word g read tensor := by
  apply Thread.Scores.biasWordOrderOfOverlappingWrites hp hX i word hBox
  intro writer spec x y k loc hOther hOwner _ hLocal hCovers
  rcases Nat.eq_zero_or_pos (biasTensorOrdinal l X stage (biasVectorHalf i) writer)
    with hSame | hLater
  · exact .inl (biasTensorOrdinalInjective hp hX hOther hBox.subbox
      (hOwner.trans hBox.owner.symm) (hSame.trans hOpening.symm))
  · exact .inr (Protocol.Bias.firstBiasReadBeforeReusedBoxInPrefix hp hX hRead hWait
      hWarp hOther hOwner hLater hLocal.1 hLocal.2.1 hCovers)

/-- Each actual first Bias word contains the two specified logical Bias values,
independently of the number of visits to the selected query tile. -/
theorem firstBiasValuesInPrefix (hCuQ : DrainCuQProtected p X) {batch g wait : Nat} {stage : Fin 2}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) (hWarp : warpIndex l g < 8)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) (hWait : FirstBiasAcquire l X g wait stage)
    :
    let coords := assignedCoordinates p batch (g / l.block)
    let row := 128 * (2 * coords.1 + stage.val) + (g % l.block) % 128
    let bias := firstVisitBiasValue p batch row coords.2
    ∀ i k, k < 4 → ∀ bs, X.get (g, wait + 1 + 4 * i.val + k) = some
      ⟨biasReadPc false i, .rd (biasReadAcc l g (biasVectorBase l g stage false i) false i k) bs⟩ →
      rebuild 3 bs = .ok (biasLoadWord (bias (8 * i.val + 2 * k))
        (bias (8 * i.val + 2 * k + 1))) := by
  intro coords row bias i k hk bs hRead
  have hWork : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  let word : Fin 4 := ⟨k,hk⟩
  let half := biasVectorHalf i
  obtain ⟨tensor,o,hBox,hOrdinal⟩ := Protocol.Bias.firstBiasAcquiredHalfInPrefix hp hX
    hCuQ hWait hWork hWarp half
  have hOrder := firstBiasWordOrderOfOpeningBoxInPrefix hp hX i word hWarp
    hWait hBox hOrdinal (FirstBiasWordRead.ofDecoded hRead)
  have hOrigin := Loader.firstBiasBoxOfOpeningAcquireInPrefix hp hX hb hLo hHi writes hBox hOrdinal
  obtain ⟨observation,barrier,cluster,hObserve,hSpec⟩ := hOrigin.spec
  have hResult := biasReadWordOfBox hp hX writes stage false i word
    (firstVisitBiasBoxColumnBounds half) (assignedCoordinates_valid hp hLo hHi).2
    hObserve hSpec hRead (by omega) hOrigin.cta hOrigin.observed hOrder
  exact (firstVisitBiasSourceWord (p := p) (l := l) (g := g) (batch := batch)
    (base := 2 * coords.1 + stage.val) (head := coords.2) i hk) ▸ hResult

end
end PTX.Kernels.TmlFa4Fwd.Softmax
