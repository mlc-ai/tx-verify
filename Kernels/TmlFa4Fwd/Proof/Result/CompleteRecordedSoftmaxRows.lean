-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Result.RecordedSoftmaxRows
public import Kernels.TmlFa4Fwd.Proof.Thread.ReachedSoftmaxHistory
import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitObservedRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Result
open PTX PTX.Proof Epilogue Prologue Protocol Thread Thread.Correction
open _root_.PTX.Kernels.TmlFa4Fwd.Mma (trips)

/-- A repeat row whose recorded visits reach the last softmax state needs no
additional terminal numerical data. The final sum and finite reference follow from its history. -/
theorem completedSoftmaxRowsOfReplay {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m)
    (hReplay : ∀ producer < l.threads, ∀ stage : Fin 2, warpIndex l producer/4 = stage.val →
      ∀ batch < p.batch, tilePrefix p batch*p.heads ≤ producer/l.block →
      producer/l.block < tilePrefix p (batch+1)*p.heads →
      let coords := assignedCoordinates p batch (producer/l.block)
      let blocks := trips p batch coords.1
      let row := stageRow coords.1 stage+producer%l.block%128
      row < p.qLength batch → blocks ≠ 1 →
      ∃ refs sums,
        RecordedSoftmaxRowPrefix p l X producer batch coords.2 row stage blocks blocks refs sums ∧
        ReachedSoftmaxRowDrain p l X producer (refs (blocks-1)) (sums (blocks-1))) :
    CompletedSoftmaxRows p l X := by
  intro producer hg stage hStage batch hb hLo hHi
  dsimp only
  intro hRow hRepeat
  obtain ⟨refs,sums,hPrefix,hDrain⟩ := hReplay producer hg stage hStage batch hb hLo hHi
    hRow hRepeat
  have hBlocks := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).1
  obtain ⟨maximum,hReference,hTerminal⟩ :=
    hDrain.terminalLane hPrefix.recurrence hBlocks (hp.keyCount_pos hb hRow)
  exact ⟨refs,sums,maximum,hPrefix,hReference,hTerminal⟩

end PTX.Kernels.TmlFa4Fwd.Result
