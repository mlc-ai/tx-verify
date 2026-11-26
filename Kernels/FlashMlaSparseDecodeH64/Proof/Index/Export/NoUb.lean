-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexNoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.NoUbSite

@[expose] public section

/-! # The index warp makes no undefined behaviour

`index_noUb`: an event fired from a state of the index warp of a followed lane is no undefined
behaviour, and the machine stops at it only if it is the exit. The state before the event is
strictly good and satisfies the tag invariant (`ix_strictAt`: the window from the head's shuffle is
well formed, every loaded and shuffled word being 32-bit), so the event is the site's: the loads
read aligned words, the polls and stores name aligned words of the CTA's block, the shuffles send
registers of 32 bits (`ix_event`, `Index/NoUbSite.lean`, `Index/NoUbAlign.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The index warp makes no undefined behaviour.** -/
theorem index_noUb (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (g k : Nat) (e : Event) (he : X.get (g, k) = some e)
    (ha : AliveIn P L X g k .index) :
    (∀ f, e.kind ≠ .ub f) ∧ (StopsAt P L X g k → e.kind = .exit) := by
  obtain ⟨σ, hσ, hr⟩ := aliveIn_iff.mp ha
  obtain ⟨d, n, rfl⟩ : ∃ d n, σ = idxState P L g d n := by
    cases hr
    exact ⟨_, _, rfl⟩
  obtain ⟨⟨-, hK⟩, hnb, -, hnc⟩ := ix_event hp hX hFw he hσ
  refine ⟨hnb, fun hs => ?_⟩
  exact Index.succ_exit d hK hnb hnc (thread_next_none_sub (next_none_of_stops he hσ hs))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
