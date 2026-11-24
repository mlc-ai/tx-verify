-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedRecurringBias
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRecurringBiasGeometry
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasSource
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Loader Thread Thread.Scores Protocol.Bias
open Thread.Loader

/-- Locate consecutive BF16 values in the logical Bias row for one block visit.
A padded packed row retains the zero fill of the observed descriptor. -/
noncomputable def visitBiasElement (p : Params) (batch tile row head visit col : Nat) : Option ℝ :=
  biasBoxValue p (p.qOffset batch+row) head
    (p.biasColumn batch row (visitKey (Mma.trips p batch tile) visit col)).toNat

private theorem warmBiasColumnBound {p : Params} {batch tile iteration : Nat}
    (stage half : Fin 2) :
    warmBiasColumn stage half iteration (warmBiasResidualBit p batch tile)+64 ≤ 1280 := by
  have hBit := warmBiasResidualBit_le p batch tile
  have hHalf := half.isLt
  unfold warmBiasColumn
  split <;> omega

/-- A consumed warm Bias half supplies the two logical BF16 values for the actual
loader traversal, including the signed stage adjustment and packed-row padding. -/
theorem warmBiasWordOfSelectedHalf {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hCuQ : DrainCuQProtected p X)
    {stage : Fin 2} {g read wait : Nat} {repeated : Bool} {i : Fin 16} {word : Fin 4}
    {tensor : EvId} {o : TensorCopy.Observation} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X (g,read) repeated i
      (biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val) bytes)
    (hEarlier : wait < read) (hBox : AcquiredBiasBox p l X stage g wait tensor (biasVectorHalf i) o)
    (hOrder : BiasWordOrder p l X stage repeated i word g read tensor)
    (hIssue : X.get tensor =
      some ⟨warmBiasIssueSite stage (biasVectorHalf i),.tensorIssue p.biasMapAddress o.spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      let row := 256*co.1+128*stage.val+(g%l.block)%128
      let col := 8*i.val+2*word.val
      ∃ iteration < min (Mma.trips p batch co.1-1) 9,
        biasTensorOrdinal l X stage (biasVectorHalf i) tensor = iteration+1 ∧
        rebuild 3 bytes = .ok (biasLoadWord
          (visitBiasElement p batch co.1 row co.2 (iteration+1) col)
          (visitBiasElement p batch co.1 row co.2 (iteration+1) (col+1))) := by
  let half := biasVectorHalf i
  obtain ⟨batch,hb,hLo,hHi,iteration,hIter,hOrigin,hRank⟩ :=
    warmBiasInputOriginRanked hp hX hFrame hCuQ stage half hBox.subbox hIssue
  obtain ⟨other,ho,hOtherLo,hOtherHi,round,_,hOtherRank,hOrdinal⟩ :=
    warmBiasOrdinalExact hp hX hFrame hCuQ stage half hBox.subbox hIssue
  have hActive : tensor.1/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨owner,_,hOwner⟩ := tileBatch_existsUnique p hActive
  have heq := (hOwner other ⟨ho,hOtherLo,hOtherHi⟩).trans
    (hOwner batch ⟨hb,hLo,hHi⟩).symm
  subst other
  have hSame : round = iteration := by omega
  subst round
  rw [hBox.owner] at hLo hHi hIter hOrigin
  let co := assignedCoordinates p batch (g/l.block)
  let lane := (g%l.block)%128
  let row := 256*co.1+128*stage.val+lane
  let column := warmBiasColumn stage half iteration (warmBiasResidualBit p batch co.1)
  let low := 8*i.val+2*word.val
  have hSource := hBox.firstBiasBox
    (row := p.qOffset batch+256*co.1+128*stage.val) (head := co.2) (col := column) hOrigin
  obtain ⟨seen,barrier,cluster,hSeen,hSpec⟩ := hSource.spec
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hRead' : X.get (g,read) = some ⟨biasReadPc repeated i,
      .rd (biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val) bytes⟩ :=
    hRead
  have hWords := biasReadWordOfBox hp hX
    (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
    stage repeated i word (warmBiasColumnBound stage half) hHead hSeen hSpec
    hRead' hEarlier hSource.cta hSource.observed hOrder
  have hElement (k : Nat) (hk : k < 2) :
      visitBiasElement p batch co.1 row co.2 (iteration+1) (low+k) =
      biasBoxValue p (p.qOffset batch+256*co.1+128*stage.val+lane) co.2
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
    have hColumn := warmBiasColumnMatchesVisit p batch co.1 stage hIter hLane hCol
    dsimp only at hColumn
    rw [hHalf,hWithin] at hColumn
    change p.biasColumn batch row (visitKey (Mma.trips p batch co.1) (iteration+1) (low+k)) =
      (column+(8*(i.val%8)+2*word.val+k) : Nat) at hColumn
    unfold visitBiasElement
    rw [hColumn,Int.toNat_natCast]
    simp [row,Nat.add_assoc]
  refine ⟨batch,hb,hLo,hHi,iteration,hIter,hOrdinal,?_⟩
  change rebuild 3 bytes = .ok (biasLoadWord
    (visitBiasElement p batch co.1 row co.2 (iteration+1) low)
    (visitBiasElement p batch co.1 row co.2 (iteration+1) (low+1)))
  have hLow : visitBiasElement p batch co.1 row co.2 (iteration+1) low =
      biasBoxValue p (p.qOffset batch+256*co.1+128*stage.val+lane) co.2
        (column+(8*(i.val%8)+2*word.val)) := hElement 0 (by decide)
  rw [hLow,hElement 1 (by decide)]
  exact hWords

end PTX.Kernels.TmlFa4Fwd.Softmax
