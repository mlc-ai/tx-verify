-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsCreditGate
public import Lemmas.Protocol.UnitsTrace

@[expose] public section

/-! # Who blocks a softmax thread at its credit poll, by trace counts

`CreditBlocked` (`creditBlocked`) counts a correction thread's credit arrivals in the credit
barrier's history (`MbarRing.Unit.unitsOf`). When no record of the history faults, these are the
thread's arrival events on the barrier (`MbarRing.Unit.unitsOf_eq_arrivals`). So a softmax thread
of stage `st` whose credit barrier ends in a phase of the parity its next poll does not find has
a correction thread of its CTA with one credit arrival on the stage fewer than its own successful
polls of the barrier (`credit_short`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

namespace Stats

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **A correction thread is one credit arrival short of a blocked softmax thread's successful
polls.** -/
theorem credit_short (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (htm : TmemFacts L X) (hinit : StatsInit L X) (hsoft : SoftArrives L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {c st h : Nat} (hst : st < 2) (hh : softIn L c st h)
    (hf : ∀ r ∈ X.objects (statsBar L c st), r.fault = none) {before : MBarrier.State}
    (hs : MBarrier.stateBefore (X.objects (statsBar L c st)) (X.objects (statsBar L c st)).length =
      some before)
    (hpar : before.phase % 2 = (okPolls (statsBar L c st) (X.tr h) + 1) % 2) :
    ∃ a, arrivals (statsBar L c st) (X.tr (corrThread L c a)) + 1 =
      okPolls (statsBar L c st) (X.tr h) := by
  obtain ⟨h1, a, ha⟩ := creditBlocked hpre hX ht htm hinit hsoft hspin c st h hst hh hs hpar
  rw [MbarRing.Unit.unitsOf_eq_arrivals hX hf] at ha
  exact ⟨a, by omega⟩

end Stats

end
end PTX.Kernels.FlashAttn4Fwd.Proof
