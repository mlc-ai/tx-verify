-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.Waits
public import Kernels.FlashAttn4Fwd.Proof.Progress.PollTime

@[expose] public section

/-! # Progress at the mbarrier polls

A released pending thread whose next event is an mbarrier poll (`nextKind d = .wait`) is at a
wait whose blockers are earlier than itself (`polls_of`), given that every such thread of a
maximal execution polls an object with a blocker when the object is not ready (`PollsBlocked`).
`Sched.mbarAt_of` turns that into an `MbarAt` with the blocker time one below the thread's, and
every poll site is timed at least at `Time.base` (`wait_base_le`).

`PollsBlocked` is proved outside the layers (`Polls/Waits.lean`), from the thread layer's
`ProgressPolls` and the protocols' blocker exports (`Protocol/*Blocked.lean`), one wait class per
site: the loader's empty waits and drain, the MMA warp's ring-full, P-ready, second P-ready and
handshake waits, the softmax S-full and credit waits, the correction's O-full and staging-free
waits, the store warp's staged waits. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

/-- **Every released pending thread at an mbarrier poll of a maximal execution polls an object
with a blocker when the object is not ready.** -/
def PollsBlocked (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g d, Maximal L kernel asms mem0 X → Frame.Pending L X g → Step.Released L X g →
    St L X g (X.tr g).length = some (some d) → nextKind d = .wait → Sched.PollBlocked (timed L) X g

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at an mbarrier poll is at a wait whose blockers are
earlier.** -/
theorem polls_of (hP : PollsBlocked L mem0) (hmax : Maximal L kernel asms mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hrel : Step.Released L X g) {d : ThreadD}
    (hσ : St L X g (X.tr g).length = some (some d)) (hk : nextKind d = .wait) :
    ∃ b, Sched.MbarAt (timed L) mem0 X g b ∧ b < endTime L X g ∧ 2 ≤ endTime L X g := by
  have ht := wait_base_le L g hk
  rw [← endTime_of hσ] at ht
  exact ⟨_, Sched.mbarAt_of (hP X g d hmax hp hrel hσ hk),
    by simp only [Time.base] at ht; omega, by simp only [Time.base] at ht; omega⟩

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
