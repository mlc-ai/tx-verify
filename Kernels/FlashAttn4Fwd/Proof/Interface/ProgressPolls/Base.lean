-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressNext
public import Lemmas.Kernel.Progress.Poll

@[expose] public section

/-! # The shapes of the thread facts at the mbarrier polls

A released thread whose next event is an mbarrier poll waits for the producers of the polled
object. The thread layer states, per wait class (`Interface/ProgressPolls/*.lean`), two kinds of
facts of single threads' runs:

* `PollsOn L X g m δ`: the thread's next event polls object `m` (by local steps it reaches a
  wait on `m`, successful or not, at one position and parity), and the parity is that of its
  successful polls of `m` plus `δ`;
* `Lags L X y g d`: in an execution without undefined behaviour, a producer thread `y` that has
  made no more producing events than the waiter's poll needs has not exited, and its state is
  earlier than the waiter's state `d` in the sequential schedule of `Thread/Roles.lean`
  (`stateTime`). Without that premise the fact fails: a correction thread whose credit arrival
  is undefined behaviour ends its run with its machine at the next site, later than the softmax
  poll waiting for that credit. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow

noncomputable section

/-- **Thread `g`'s next event polls `m`**, with the parity of its successful polls of `m` plus
`δ` (`Sched.PollsOn`). -/
abbrev PollsOn (L : Launch) (X : Execution) (g : Nat) (m : Loc) (δ : Nat) : Prop :=
  Sched.PollsOn kernel asms L X g m δ

/-- **Thread `y` lags thread `g` at its state `d`** (`Sched.Lags`): when the execution has no
undefined behaviour, `y` has not exited, and its current time (`endTime`) is earlier than `d`. -/
abbrev Lags (L : Launch) (X : Execution) (y g : Nat) (d : ThreadD) : Prop :=
  Sched.Lags (timed L) X y (stateTime L g d)

/-- Every election thread `y` made returned its own lane. -/
def SelfElected (L : Launch) (X : Execution) (y : Nat) : Prop :=
  ∀ j pc mask inst leader, X.Elect (y, j) pc mask inst leader → leader = laneOf L y

end
end PTX.Kernels.FlashAttn4Fwd.Proof
