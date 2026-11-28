-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Bound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Lemmas.Kernel.BoundU

@[expose] public section

/-! # A followed thread's events are bounded

The trace-level bound of the bound leaf: in a consistent execution that the thread machine
follows, every launched thread makes at most a fixed number of counted events (`Event.counts`: a
failed poll does not count). The glued measure's top less the measure of the thread's state is a
rank that every step from a followed state keeps and every counted event lowers
(`Common/Bound.lean`, `measure_raise`), so `Frame.count_leU` bounds the counted events by the
top plus two (the stop and the death). The number depends on nothing (the roles' places are
capped, the index warp's loops by their 32-bit counters). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **Every thread of a followed consistent execution makes boundedly many counted events.** -/
theorem thread_counts (hp : Pre P L m) :
    ∃ N, ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X →
      ∀ g < L.threads, (X.tr g).countP Event.counts ≤ N := by
  refine ⟨top + 2, fun X hX hFw g hg => ?_⟩
  have hF := follow_iff.mp hFw
  have ht : Frame.Tracked (thread P L) X := fun h k hh => (hF h hh k).1
  have h := Frame.count_leU (fun _ _ => thread_sound hp) hX hg ht
    (fun σ => top - measure P L g σ) (fun _ => false) 0
    fun k d d' e he hσ _ hu hn => by
      obtain ⟨h1, h2⟩ := measure_raise hX hFw hg he hσ hu hn
      have := measure_le P L g d'
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      split
      · have := h2 ‹_›
        omega
      · omega
  have := measure_le P L g (thread P L g).init
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
