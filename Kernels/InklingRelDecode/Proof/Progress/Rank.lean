-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Fire
public import Lemmas.Kernel.Progress.Poll
public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Kernel.Progress.Tc
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

/-!
# The time table of the progress descent

The progress descent ranks the obligations by the library's ranks (`Sched.rank`) of a time table
(`Sched.Timed`): the thread machines `code L Q` (`Interface.Select`) with a time `T g d` for each
abstract state. A pending thread ranks at twice the time of its next event (`Sched.threadTime`),
plus one while its last event blocks. The kernel issues no tensor store, so the store obligation
ranks 0 and is never open.

The time `T : Nat → TSt → Nat` is a function of the thread and the abstract machine state alone
(the layers above the thread layer have no other handle on a thread's place in the schedule). It is
a parameter of the progress layer; `Remaining.time` supplies it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

/-- The time table of the thread machines with the time `T`. -/
noncomputable abbrev timed (T : Nat → TSt → Nat) (Q : Params) (L : Launch) :
    Sched.Timed kernel asms L :=
  ⟨code L Q, T⟩

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {X : Execution} {g : Nat}

/-- A thread's time, by its machine states (`Sched.threadTime`). -/
theorem threadTime_unfold : Sched.threadTime (timed T Q L) X g =
    match St Q L X g (X.tr g).length with
    | some (some d) => T g d
    | some none => 0
    | none =>
      match St Q L X g ((X.tr g).length - 1) with
      | some (some d) => T g d + 1
      | _ => 0 := by
  unfold Sched.threadTime
  simp only [St, timed]
  split <;> rename_i h1 <;> simp only [h1]
  split <;> rename_i h2 <;> simp only [h2]

/-- A thread's time is the time of its state at its trace's end. -/
theorem threadTime_eq {d : TSt} (hσ : St Q L X g (X.tr g).length = some (some d)) :
    Sched.threadTime (timed T Q L) X g = T g d :=
  Sched.threadTime_of hσ

/-- A thread whose machine has stopped after its last event is one later than its state before
that event. -/
theorem threadTime_stop {d : TSt} (hd : St Q L X g ((X.tr g).length - 1) = some (some d))
    (hσ : St Q L X g (X.tr g).length = none) : Sched.threadTime (timed T Q L) X g = T g d + 1 :=
  Sched.threadTime_stop hd hσ

end PTX.Kernels.InklingRelDecode.Proof.Progress
