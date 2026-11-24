-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputHandoff
public import Lemmas.Protocol.UnitsTrace

@[expose] public section

/-! # Who blocks a store lane at its staged poll, by trace counts

`StoreBlocked` (`storeBlocked`) counts a correction thread's staged arrivals in the staged
barrier's history (`MbarRing.Unit.unitsOf`). When no record of the history faults, these are the
thread's arrival events on the barrier (`MbarRing.Unit.unitsOf_eq_arrivals`). So a store lane
whose stage's staged barrier ends in a phase of the parity its next poll does not find has a
correction thread of its CTA with as many staged arrivals on the stage as its own successful
polls of the barrier (`staged_short`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

namespace Output

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **A correction thread has no more staged arrivals than a blocked store lane's successful
polls.** -/
theorem staged_short (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : OutputFacts L X)
    (htm : TmemFacts L X) (hinit : OutputInit L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {c st h : Nat} (hst : st < 2) (hh : storeIn L c h)
    (hf : ∀ r ∈ X.objects (stagedBar L c st), r.fault = none) {before : MBarrier.State}
    (hs : MBarrier.stateBefore (X.objects (stagedBar L c st))
      (X.objects (stagedBar L c st)).length = some before)
    (hpar : before.phase % 2 = okPolls (stagedBar L c st) (X.tr h) % 2) :
    ∃ a, arrivals (stagedBar L c st) (X.tr (Stats.corrThread L c a)) =
      okPolls (stagedBar L c st) (X.tr h) := by
  obtain ⟨h1, a, ha⟩ := (storeBlocked hpre hX ht htm hinit hspin c st hst).1 h hh hs hpar
  rw [MbarRing.Unit.unitsOf_eq_arrivals hX hf] at ha
  exact ⟨a, by omega⟩

end Output

end
end PTX.Kernels.FlashAttn4Fwd.Proof
