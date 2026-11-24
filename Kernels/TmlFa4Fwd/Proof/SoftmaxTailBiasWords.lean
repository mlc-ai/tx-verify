-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRecurringBiasWords
public import Kernels.TmlFa4Fwd.Proof.LoaderTailBiasSource
public import Kernels.TmlFa4Fwd.Proof.LoaderTailBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Loader Thread Thread.Scores Thread.Loader
open Protocol.Bias

/-- On the low stage's optional Bias packet, the observed word uses logical visit ten. -/
theorem tailBiasWordOfSelectedHalf {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    {g read wait : Nat} {repeated : Bool} {i : Fin 16} {word : Fin 4}
    {tensor : EvId} {o : TensorCopy.Observation} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X (g,read) repeated i
      (biasReadAcc l g (biasVectorBase l g 0 repeated i) repeated i word.val) bytes)
    (hEarlier : wait < read) (hBox : AcquiredBiasBox p l X 0 g wait tensor (biasVectorHalf i) o)
    (hOrder : BiasWordOrder p l X 0 repeated i word g read tensor)
    (hIssue : X.get tensor = some ⟨(inputSite (tailBiasInputSite (biasVectorHalf i))).pc,
      .tensorIssue p.biasMapAddress o.spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+(g%l.block)%128
      let col := 8*i.val+2*word.val
      10 < Mma.trips p batch co.1 ∧
      biasTensorOrdinal l X 0 (biasVectorHalf i) tensor = 10 ∧
      rebuild 3 bytes = .ok (biasLoadWord
        (visitBiasElement p batch co.1 row co.2 10 col)
        (visitBiasElement p batch co.1 row co.2 10 (col+1))) := by
  let half := biasVectorHalf i
  obtain ⟨batch,hb,hLo,hHi,hTrips,hGap,hOrigin⟩ :=
    tailBiasFinalOrigin hp hX hFrame hCuQ half hBox.subbox hIssue
  have hOrdinal := tailBiasOrdinalExact hp hX hFrame hCuQ half hBox.subbox hIssue
  rw [hBox.owner] at hLo hHi hTrips hGap hOrigin
  let co := assignedCoordinates p batch (g/l.block)
  let lane := (g%l.block)%128
  let row := 256*co.1+lane
  let column := residualBiasColumn half 9
  let low := 8*i.val+2*word.val
  have hSource := hBox.firstBiasBox
    (row := p.qOffset batch+256*co.1) (head := co.2) (col := column) hOrigin
  obtain ⟨seen,barrier,cluster,hSeen,hSpec⟩ := hSource.spec
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hRead' : X.get (g,read) = some ⟨biasReadPc repeated i,
      .rd (biasReadAcc l g (biasVectorBase l g 0 repeated i) repeated i word.val) bytes⟩ := hRead
  have hFit : column+64 ≤ 1280 := by have := half.isLt; dsimp [column,residualBiasColumn]; omega
  have hWords := biasReadWordOfBox hp hX
    (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
    0 repeated i word hFit hHead hSeen hSpec hRead' hEarlier hSource.cta hSource.observed hOrder
  have hElement (k : Nat) (hk : k < 2) :
      visitBiasElement p batch co.1 row co.2 10 (low+k) =
      biasBoxValue p (p.qOffset batch+256*co.1+lane) co.2
        (column+(8*(i.val%8)+2*word.val)+k) := by
    have hi := i.isLt
    have hw := word.isLt
    have hCol : low+k < 128 := by dsimp [low]; omega
    have hLane : lane < 128 := Nat.mod_lt _ (by decide)
    have hHalf : (⟨(low+k)/64,by omega⟩ : Fin 2) = half := by
      apply Fin.ext
      change (low+k)/64 = i.val/8
      dsimp [low]
      omega
    have hWithin : (low+k)%64 = 8*(i.val%8)+2*word.val+k := by dsimp [low]; omega
    have hColumn := residualBiasColumnMatchesVisit p batch co.1 hTrips hGap hLane hCol
    dsimp only at hColumn
    rw [hHalf,hWithin] at hColumn
    change p.biasColumn batch row (visitKey (Mma.trips p batch co.1) 10 (low+k)) =
      (column+(8*(i.val%8)+2*word.val+k) : Nat) at hColumn
    unfold visitBiasElement
    rw [hColumn,Int.toNat_natCast]
    simp [row,Nat.add_assoc]
  refine ⟨batch,hb,hLo,hHi,hTrips,hOrdinal,?_⟩
  change rebuild 3 bytes = .ok (biasLoadWord
    (visitBiasElement p batch co.1 row co.2 10 low)
    (visitBiasElement p batch co.1 row co.2 10 (low+1)))
  have hLow : visitBiasElement p batch co.1 row co.2 10 low =
      biasBoxValue p (p.qOffset batch+256*co.1+lane) co.2
        (column+(8*(i.val%8)+2*word.val)) := hElement 0 (by decide)
  rw [hLow,hElement 1 (by decide)]
  exact hWords

end PTX.Kernels.TmlFa4Fwd.Softmax
