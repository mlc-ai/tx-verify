-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RescaleWarpProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpBackedge

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- The two producer warps have published row statistics through every
noninitial generation of this tile. -/
def RepeatedStatisticsPublished (l : Launch) (X : Execution) (g trips : Nat) : Prop :=
  ∀ generation, 0 < generation → generation < trips → ∀ stage : Fin 2,
    ∀ peer < l.threads, peer/l.block = g/l.block →
      warpIndex l peer = (Protocol.Statistics.waitingWarp l g stage).val →
      ∃ i round, Scores.Publishes X (peer,i) round ∧
        generation ≤ observedBarrierOrdinal X (peer,i) (3+warpIndex l peer)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRepeat : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (published : RepeatedStatisticsPublished l X g
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1))
include hp hMax hFrame hg hw hb hLo hHi hRepeat published

/-- A paired correction warp processes each published generation and returns
both statistics slots of the last generation. At that point it has observed
every generation of both named statistics barriers. -/
theorem repeatedCorrectionLastReturnOfPublications :
    ∃ votes rank, Nonempty (Correction.RescaleWarpReturned p l X g batch 2 1
      (fun _ => Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) votes rank) := by
  classical
  let trips := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have bound : trips < 2^31 := by
    obtain ⟨_,bound,_⟩ := Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1
    obtain ⟨_,_,hTotal⟩ := hp.lengths batch hb
    dsimp [trips]
    omega
  have counts (gen : Nat) : Correction.rescaleNextGeneration
      (Correction.rescaleNextGeneration (fun _ => gen) 0) 1 = fun _ => gen+1 := by
    funext stage
    fin_cases stage <;> simp [Correction.rescaleNextGeneration]
  have walk (k : Nat) : ∀ gen votes rank, 0 < gen → gen+k+1 = trips →
      Correction.RescaleWarpJoin p l X g batch (k+2) 0 (fun _ => gen) votes rank →
      ∃ votes rank, Nonempty (Correction.RescaleWarpReturned p l X g batch 2 1
        (fun _ => trips) votes rank) := by
    induction k with
    | zero =>
      intro gen votes rank hGen hTotal c
      obtain ⟨_,_,⟨z⟩⟩ := rescaleWarpReturnedOfPublications hp hMax hFrame hg hw c
        (published gen hGen (by omega) 0)
      obtain ⟨one⟩ := z.stageOne hp hMax
      obtain ⟨_,_,⟨last⟩⟩ := rescaleWarpReturnedOfPublications hp hMax hFrame hg hw one
        (published gen hGen (by omega) 1)
      rw [counts,show gen+1 = trips by omega] at last
      exact ⟨_,_,⟨last⟩⟩
    | succ k ih =>
      intro gen votes rank hGen hTotal c
      obtain ⟨_,_,⟨z⟩⟩ := rescaleWarpReturnedOfPublications hp hMax hFrame hg hw c
        (published gen hGen (by omega) 0)
      obtain ⟨one⟩ := z.stageOne hp hMax
      obtain ⟨_,_,⟨last⟩⟩ := rescaleWarpReturnedOfPublications hp hMax hFrame hg hw one
        (published gen hGen (by omega) 1)
      obtain ⟨next⟩ := last.nextRound hp hMax (by omega) (by omega)
      rw [counts] at next
      exact ih _ _ _ (by omega) (by omega) next
  obtain ⟨start⟩ := openingRescaleWarpOfMaximal hp hMax (hFrame X hMax.1) hw hb hLo hHi hRepeat
  have n : trips-2+2 = trips := Nat.sub_add_cancel hRepeat
  apply walk (trips-2) 1 1 0 (by decide) (by omega)
  rw [n]
  exact start

/-- A paired correction warp processes each published generation and reaches
the first terminal statistics rendezvous on a tile of any active KV length. -/
theorem repeatedCorrectionTerminalWarpOfPublications :
    ∃ votes rank, Nonempty (Correction.RescaleWarpTerminal p l X g batch votes rank) := by
  obtain ⟨_,_,⟨last⟩⟩ := repeatedCorrectionLastReturnOfPublications hp hMax hFrame hg hw hb
    hLo hHi hRepeat published
  exact ⟨_,_,last.terminalWarp hp hMax⟩

end PTX.Kernels.TmlFa4Fwd.Progress
