-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.FirstRecurringMma
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringScoreProgress
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityAck
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreNumericsProgress
public import Kernels.TmlFa4Fwd.Proof.Progress.RecurringBiasDelivery
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedScoreProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScorePollRanks
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorScoreCount
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreRoundProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedAffineOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreBiasProgress
import Lemmas.Snoc.SnocExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Softmax Thread.Loader Protocol.Bias

/-- The physical Bias-ready phase has completed the specified generation. -/
def BiasGenerationDelivered (l : Launch) (X : Execution) (cta : Nat)
    (stage : Fin 2) (gen : Nat) : Prop :=
  let log := X.objects (biasReadyObject l cta stage)
  ∃ s, MBarrier.stateBefore log log.length = some s ∧ gen+1 ≤ s.phase

/-- A pending softmax lane can acquire its issued Bias generation. A lane
which has already advanced places no parity constraint on the final object. -/
theorem BiasGenerationDelivered.readyForPendingLane {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g gen : Nat} {stage : Fin 2}
    (delivered : BiasGenerationDelivered l X (g/l.block) stage gen)
    (member : warpIndex l g ∈ Thread.biasParticipants stage)
    (rank : (X.tr g).countP (Execution.isBarId (11+stage.val)) = gen)
    {t : TState} (run : Run kernel Assumptions.all l g {} (X.tr g) (some t)) :
    OpeningPollReady X (biasReadyObject l (g/l.block) stage) (gen%2) := by
  obtain ⟨s,hs,lower⟩ := delivered
  have live : ¬ Thread.Exited X g := by
    rintro ⟨i,⟨site,kind⟩,found,hKind⟩
    change kind = .exit at hKind
    subst kind
    exact no_exit_of_run run i site found
  have upper := biasFinalPhaseLeLaneRendezvous hp hMax.1 stage member live hs
  exact ⟨s,hs,by omega⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (frame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g < 4) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ g/l.block) (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (Epilogue.assignedCoordinates p batch (g/l.block)).1)
include hp hMax frame hg hw hb lo hi multiple

end PTX.Kernels.TmlFa4Fwd.Progress
