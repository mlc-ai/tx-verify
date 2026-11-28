-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.PollRounds

@[expose] public section

/-! # The round of the score poll along one event

The count of successful polls at pc 1257 grows by one at a successful poll and stays at any other
event. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX

theorem poll_step {X : Execution} {g k : Nat} {ev : Event} (he : X.get (g, k) = some ev) :
    pollRound 1257 ((X.tr g).take (k + 1)) =
      pollRound 1257 ((X.tr g).take k) + (if okPollAt 1257 ev = true then 1 else 0) := by
  have h : (X.tr g)[k]? = some ev := he
  rw [pollRound, pollRound, List.take_add_one, h, List.countP_append]
  simp

theorem poll_same {X : Execution} {g k : Nat} {ev : Event} (he : X.get (g, k) = some ev)
    (ne : ev.pc ≠ 1257) :
    pollRound 1257 ((X.tr g).take (k + 1)) = pollRound 1257 ((X.tr g).take k) := by
  rw [poll_step he]
  obtain ⟨p, kd⟩ := ev
  have : okPollAt 1257 ⟨p, kd⟩ = false := by
    cases kd <;> simp only [okPollAt]
    rename_i a b ok c d
    cases ok <;> simp
    exact fun h => ne h
  simp [this]

theorem poll_mono {X : Execution} {g k k' : Nat} (h : k ≤ k') :
    pollRound 1257 ((X.tr g).take k) ≤ pollRound 1257 ((X.tr g).take k') :=
  by
  have : (X.tr g).take k = ((X.tr g).take k').take k := by rw [List.take_take, Nat.min_eq_left h]
  rw [pollRound, pollRound, this]
  exact (List.take_sublist _ _).countP_le

end PTX.Kernels.InklingRelDecode.Proof.Softmax
