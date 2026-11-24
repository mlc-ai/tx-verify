-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitProbabilityPhase
import Kernels.TmlFa4Fwd.Proof.Protocol.TailProbabilityObservations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing Prologue Epilogue Thread.Scores

/-- A single-visit tail acquire observes the elected publication of each of the
four participating softmax warps. -/
theorem singleVisitTailCreditOfWarp {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {batch cta : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1)
    (stage : Fin 2) (warp : Fin 4) {k : Nat} {poll : Record Ref}
    (hRecord : (X.objects (probabilityObject l cta stage 1))[k]? = some poll)
    (hAction : poll.action = .pollParity 0 true)
    (hSuccess : poll.reply.waited = some true) :
    ∃ i, ProbabilityCredit l X i cta stage 1 ∧
      warpIndex l i.1 = 4 * stage.val + warp.val ∧ MbarObserved X (.thread i) poll.id := by
  have hSeen := singleVisitTailObservedPhaseZero hp hX hDone hFrame hb hLo hHi hTrip
    stage hRecord hAction hSuccess
  exact tailCreditOfObservedWarp hp hX stage warp hRecord hSuccess hSeen

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
