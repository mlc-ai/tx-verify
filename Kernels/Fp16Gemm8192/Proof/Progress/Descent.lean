-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Kernel.Obligation
public import Lemmas.Kernel.Next
public import Lemmas.Step.Released
public import Lemmas.Flow.Final
public import Lemmas.Kernel.Descent

@[expose] public section

/-! # The progress descent: ranks and the step for each obligation

A pending thread is ranked by the time of its next event in the sequential schedule of the rank
table (`ThreadD.vtime`), plus one while its last event still blocks (`Step.Released` fails).
The table's times are even, so a thread that must perform an event before another thread's
next event ranks below that thread whether or not either is blocked, and recording a pending
collective lowers the rank of the thread that issued it. A thread in
the exit stage ranks above every thread outside it (`exitBase`), so a thread waiting at the exit
barrier ranks above every thread that has not arrived. An asynchronous copy, MMA or request
ranks 1 and a commit's delivery 2, above the MMAs it waits for; a paired Tensor Memory or
register request ranks above every thread, whose collective requests it waits for.

Every open obligation of a maximal execution either extends it by a counted event or passes to
an open obligation of smaller rank in a maximal execution (`Descent.Steps` with `Descent.Obl` and
`rank`). Then every maximal execution is complete (`Descent.progress_of_steps`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX Classical

noncomputable section

/-- The kernel's assumptions hold of every execution. -/
theorem prod_wf {L : Launch} {mem0 : Mem0} (Y : Execution) : ∀ a ∈ Prod, a.wf L mem0 Y := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> trivial

/-- The kernel's assumptions put no well-formedness constraint on executions. -/
theorem prod_wfFree {L : Launch} {mem0 : Mem0} : Assumption.WfFree L mem0 Prod :=
  fun a ha Y => prod_wf Y a ha

/-- The time of thread `h`'s next event if it is outside the exit stage, else 0. -/
def baseTime (L : Launch) (X : Execution) (h : Nat) : Nat :=
  match Frame.stateAt (code L) X h (X.tr h).length with
  | some (some d) => if d.exitOff.isSome then 0 else d.vtime L h (X.tr h)
  | _ => 0

/-- A time above every thread's next event outside the exit stage. -/
def exitBase (L : Launch) (X : Execution) : Nat :=
  1 + ∑ h ∈ Finset.range L.threads, baseTime L X h

/-- The time of thread `g`'s next event: the rank table outside the exit stage, above
`exitBase` inside it. -/
def threadTime (L : Launch) (X : Execution) (g : Nat) : Nat :=
  match Frame.stateAt (code L) X g (X.tr g).length with
  | some (some d) =>
    match d.exitOff with
    | some o => exitBase L X + o
    | none => d.vtime L g (X.tr g)
  | _ => 0

/-- The rank of an obligation. -/
def rank (L : Launch) (X : Execution) : Descent.Obligation → Nat
  | .thread g => threadTime L X g + (if Step.Released L X g then 0 else 1)
  | .commit => 2
  | .tmem => exitBase L X + 20
  | _ => 1

/-- A thread ranks at most one above its time. -/
theorem rank_thread_le {L : Launch} {X : Execution} {g : Nat} :
    rank L X (.thread g) ≤ threadTime L X g + 1 := by
  simp only [rank]
  split <;> omega

/-- A thread whose last event is released ranks at its time. -/
theorem rank_released {L : Launch} {X : Execution} {g : Nat} (h : Step.Released L X g) :
    rank L X (.thread g) = threadTime L X g := by
  simp [rank, h]

/-- A thread outside the exit stage has the rank table's time. -/
theorem threadTime_of {L : Launch} {X : Execution} {g : Nat} {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (he : d.exitOff = none) :
    threadTime L X g = d.vtime L g (X.tr g) := by
  simp [threadTime, hσ, he]

/-- A thread in the exit stage has a time above every thread's outside it. -/
theorem baseTime_lt_exitBase {L : Launch} {X : Execution} {h : Nat} (hh : h < L.threads) :
    baseTime L X h < exitBase L X := by
  have := Finset.single_le_sum (f := baseTime L X) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hh)
  simp only [exitBase]
  omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
