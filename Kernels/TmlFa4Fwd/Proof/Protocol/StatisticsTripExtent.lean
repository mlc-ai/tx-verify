-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Statistics
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditExtent
public import Kernels.TmlFa4Fwd.Proof.SoftmaxExitPublications
public import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX Thread Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
include hp hX hCuQ

/-- A active producer's observed exit covers every statistics generation
through the trip count of its assigned tile. -/
theorem ordinalBeforeActiveExit (hUsedK : UsedKProtected p X) {producer pos batch ordinal : Nat}
    {stop : Event} (hWarp : warpIndex l producer < 8)
    (hWork : producer / l.block < tilePrefix p p.batch * p.heads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch+1) * p.heads)
    (hBound : ordinal ≤ Mma.trips p batch (assignedCoordinates p batch (producer/l.block)).1)
    (hGet : X.get (producer,pos) = some stop) (hExit : stop.kind = .exit) :
    ordinal < (Scores.before X (producer,pos)).notices := by
  have hg := Step.CtaBar.thread_lt_of_get hX hGet
  obtain ⟨picked,hPicked,hPLo,hPHi,hProducer,_⟩ :=
    Softmax.exitedActivePublicationCount hp hX hg hWarp hWork hCuQ hUsedK hGet hExit
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hBatch : picked = batch :=
    (hUnique picked ⟨hPicked,hPLo,hPHi⟩).trans
      (hUnique batch ⟨hb,hLo,hHi⟩).symm
  rw [hBatch] at hProducer
  exact hProducer.symm ▸ Nat.lt_succ_of_le hBound

/-- A paired active producer cannot exit before publishing the statistics generation
of an observed correction credit. Both roles derive their count from the same assigned tile. -/
theorem creditOrdinalBeforeActiveExit (hUsedK : UsedKProtected p X) {credit : EvId} {stage : Fin 2}
    {e : Event} (he : X.get credit = some e)
    (hAction : correctionAction e = some (.statsCredit stage)) {producer pos : Nat} {stop : Event}
    (hSame : producer / l.block = credit.1 / l.block) (hPair : Paired l producer credit.1 stage)
    (hWork : credit.1 / l.block < tilePrefix p p.batch * p.heads)
    (hGet : X.get (producer,pos) = some stop) (hExit : stop.kind = .exit) :
    (correctionBefore X credit).count (.statsCredit stage) <
      (Scores.before X (producer,pos)).notices := by
  obtain ⟨batch,hb,hLo,hHi,hCredit⟩ :=
    Correction.correctionCreditsWithinTrips hp hX hWork hUsedK stage he hAction
  have hWarp : warpIndex l producer < 8 := by
    have hLocal := Nat.mod_lt (warpIndex l credit.1) (by decide : 0 < 4)
    have hStage := stage.isLt
    unfold Paired Correction.statsBarrierId at hPair
    omega
  exact ordinalBeforeActiveExit hp hX hCuQ hUsedK hWarp (hSame.symm ▸ hWork)
    hb (hSame.symm ▸ hLo) (hSame.symm ▸ hHi) (by simpa only [hSame] using hCredit) hGet hExit

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
