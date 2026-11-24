-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.NextIssue
public import Lemmas.Step.CommitOrderExtend

@[expose] public section

/-!
# The mbarrier polls

A released pending thread whose next event polls an mbarrier object steps when, should the
object's final phase have the poll's parity, the execution has a blocker of the thread
(`Sched.PollBlocked`); `Sched.mbarAt_of` turns that into an `Sched.MbarAt` with the blocker time
one below the thread's, which steps by `Sched.mbar_at_steps`. `PollsBlocked` is the statement that
every such thread of a maximal execution polls an object with a blocker when the object is not
ready; each of the kernel's six poll sites (`Sm.Site.waitS`, `waitO`, `Loader.Site.wait`,
`Mma.Site.kvWait`, `pWait`, `Epi.Site.wait`) is one wait class of it (`Protocol`: the producers
of the polled barrier).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface MBarrier

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **Every released pending thread at an mbarrier poll of a maximal execution polls an object with
a blocker when the object is not ready.** -/
def PollsBlocked (T : Nat → TSt → Nat) (Q : Params) (L : Launch) (mem0 : Mem0) : Prop :=
  ∀ X g d, Maximal L kernel asms mem0 X → Frame.Pending L X g → Step.Released L X g →
    St Q L X g (X.tr g).length = some (some d) → nextKind d = .wait →
      Sched.PollBlocked (timed T Q L) X g

/-- **A released pending thread at an mbarrier poll is at a wait whose blockers are earlier**,
given that every state at a poll is timed at least 2. -/
theorem polls_of (hP : PollsBlocked T Q L mem0) (hmax : Maximal L kernel asms mem0 X)
    (hp : Frame.Pending L X g) (hrel : Step.Released L X g) {d : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some d)) (hk : nextKind d = .wait)
    (ht : 2 ≤ T g d) :
    ∃ b, Sched.MbarAt (timed T Q L) mem0 X g b ∧ b < Sched.threadTime (timed T Q L) X g ∧
      2 ≤ Sched.threadTime (timed T Q L) X g := by
  have ht' := threadTime_eq (T := T) hσ
  exact ⟨_, Sched.mbarAt_of (hP X g d hmax hp hrel hσ hk), by omega, by omega⟩

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
