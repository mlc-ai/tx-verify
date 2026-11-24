-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.OutputHandoff
public import Lemmas.Protocol.UnitsTrace

@[expose] public section

/-! # Who blocks a correction thread at its staging-free poll, by trace counts

`StoreBlocked` (`storeBlocked`) counts a store lane's free arrivals in the free barrier's history
(`MbarRing.Unit.unitsOf`). When no record of the history faults, these are the lane's arrival
events on the barrier (`MbarRing.Unit.unitsOf_eq_arrivals`). So a correction thread whose stage's
free barrier ends in a phase of the parity its next poll does not find has a store lane of its CTA
with one free arrival on the stage fewer than its own successful polls of the barrier
(`free_short`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

namespace Output

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **A store lane is one free arrival short of a blocked correction thread's successful
polls.** -/
theorem free_short (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : OutputFacts L X)
    (htm : TmemFacts L X) (hinit : OutputInit L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {c st h : Nat} (hst : st < 2) (hh : Stats.corrIn L c h)
    (hf : ∀ r ∈ X.objects (freeBar L c st), r.fault = none) {before : MBarrier.State}
    (hs : MBarrier.stateBefore (X.objects (freeBar L c st)) (X.objects (freeBar L c st)).length =
      some before)
    (hpar : before.phase % 2 = (okPolls (freeBar L c st) (X.tr h) + 1) % 2) :
    ∃ b, arrivals (freeBar L c st) (X.tr (storeThread L c b)) + 1 =
      okPolls (freeBar L c st) (X.tr h) := by
  obtain ⟨h1, b, hb⟩ := (storeBlocked hpre hX ht htm hinit hspin c st hst).2 h hh hs hpar
  rw [MbarRing.Unit.unitsOf_eq_arrivals hX hf] at hb
  exact ⟨b, by omega⟩

end Output

end
end PTX.Kernels.FlashAttn4Fwd.Proof
