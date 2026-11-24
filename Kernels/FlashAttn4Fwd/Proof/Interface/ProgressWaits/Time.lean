-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface
public import Kernels.FlashAttn4Fwd.Proof.Thread.Roles
public import Lemmas.Kernel.Progress.Rank

@[expose] public section

/-! # The time of a thread's machine state

The progress layer ranks a pending thread by the time of its next event: the time of its machine
state, by the site tables of `Thread/Roles.lean` (the prologue's and each role's, in the
coordinates of the role state). `stateTime` is that function. A thread's current time
(`endTime`) is the time of its state at its trace's end; when its machine has stopped there (its
run reaches undefined behaviour by local steps after its last event), it is one more than the
time of its state before its last event. The progress waits' facts
(`Interface/ProgressWaits/*.lean`) compare the times of threads blocked at a collective operation
with those of the lanes they wait for. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

/-- The time of a machine state of thread `g`. -/
def stateTime (L : Launch) (g : Nat) : ThreadD → Nat
  | .inl p => Progress.Time.prologue p.site
  | .inr (.idle s) => Progress.Time.idle s.site
  | .inr (.loader d) => Progress.Time.loader (Work.n L) (Work.T L g) d
  | .inr (.mma d) => Progress.Time.mma (Work.n L) (Work.T L g) d
  | .inr (.store d) => Progress.Time.store (Work.n L) (Work.T L g) d
  | .inr (.softmax d) => Progress.Time.softmax (Work.n L) (Work.T L g) (Softmax.stOf L g) d
  | .inr (.corr d) => Progress.Time.correction (Work.n L) (Work.T L g) d

/-- The machine of every thread with the site tables' times. -/
abbrev timed (L : Launch) : Sched.Timed kernel asms L := ⟨code L, stateTime L⟩

/-- The current time of thread `g` (`Sched.threadTime` of the site tables): the time of its state
at its trace's end, or, when its machine has stopped there, one more than the time of its state
before its last event (`0` otherwise). -/
scoped notation:max "endTime " L:max X:max => Sched.threadTime (timed L) X

/-- The current time of a thread at a state at its trace's end is that state's time. -/
theorem endTime_of {L : Launch} {X : Execution} {g : Nat} {d : ThreadD}
    (hσ : St L X g (X.tr g).length = some (some d)) : endTime L X g = stateTime L g d :=
  Sched.threadTime_of hσ

end
end PTX.Kernels.FlashAttn4Fwd.Proof
