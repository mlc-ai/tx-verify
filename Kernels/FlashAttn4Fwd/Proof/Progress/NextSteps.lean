-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.NextIssue
public import Kernels.FlashAttn4Fwd.Proof.Progress.NextTc
public import Kernels.FlashAttn4Fwd.Proof.Progress.NextColl

@[expose] public section

/-! # A released pending thread performs its next event

The kind of a released pending thread's next event (`nextKind`) picks its class: an mbarrier
initialization or arrival, a tensor copy or store issue, an MMA, a commit, a cluster barrier
operation (`NextIssue.lean`), a Tensor Memory load or store or their waits, a bulk-group wait
(`NextTc.lean`), a named-barrier arrival, a register request, a paired Tensor Memory operation
(`NextColl.lean`), a fence or bulk commit, a store, the allocation's address store, a read, the
exit (`NextFire.lean`). Each is performed (`next_steps`).

The other kinds (`NextKind.Rest`) are classes of their own: the mbarrier polls, which step by
their blockers' times (`MbarAt`), and the warp collectives (shuffle, election, warp barrier,
vote), which every lane of the warp performs together. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

/-- The kinds of next events whose classes are not in `next_steps`: an mbarrier poll and a warp
collective. -/
def _root_.PTX.Kernels.FlashAttn4Fwd.Proof.NextKind.Rest : NextKind → Prop
  | .wait | .warp => True
  | _ => False

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread whose next event is of a kind outside `NextKind.Rest`
steps.** -/
theorem next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hrel : Step.Released L X g) (hr : ¬ (nextKind d).Rest) : ThreadSteps L mem0 X g := by
  cases hk : nextKind d with
  | wait | warp => rw [hk] at hr; exact (hr trivial).elim
  | bar => exact bar_next_steps hc hp hσ hk hrel
  | reg => exact reg_next_steps hc hp hσ hk hrel
  | tmem => exact tmem_next_steps hc hp hσ hk hrel
  | cluster => exact cluster_next_steps hc hp hσ hk hrel
  | init => exact init_next_steps hc hp hσ hk hrel
  | arrive => exact arrive_next_steps hc hp hσ hk hrel
  | tensorLoad => exact tensorLoad_next_steps hc hp hσ hk hrel
  | tensorStore => exact tensorStore_next_steps hc hp hσ hk hrel
  | mma => exact mma_next_steps hc hp hσ hk hrel
  | commit => exact commit_next_steps hc hp hσ hk hrel
  | bulkWait => exact bulkWait_next_steps hc hp hσ hk hrel
  | tcLoad => exact tcLoad_next_steps hc hp hσ hk hrel
  | tcStore => exact tcStore_next_steps hc hp hσ hk hrel
  | read => exact read_next_steps hc hp hσ hk hrel
  | quiet => exact quiet_next_steps hc hp hσ hk hrel
  | store => exact store_next_steps hc hp hσ hk hrel
  | allocStore => exact allocStore_next_steps hc hp hσ hk hrel
  | exit => exact exit_next_steps hc hp hσ hk hrel

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
