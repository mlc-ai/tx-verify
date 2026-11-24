-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Thread.Facts
public import Lemmas.Kernel.Bound

@[expose] public section

/-! # Consistent executions have bounded size

A rank on a thread's abstract states that every step decreases by at least one (the reduction
loop by the cells left to read) bounds each thread's counted events (`Frame.bound_of_rank`). -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0}

/-- The events a thread has left, at most. -/
def rank (d : D) : Nat :=
  match d.site with
  | .input => 261 | .share => 260 | .bar => 259 | .sum => 3 + (255 - d.i) | .out => 2
  | .exit => 1

theorem rank_step {g : Nat} {d d' : D} {e : Event} (h : next g d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s with
  | input =>
    simp only [next] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    obtain ⟨-, rfl⟩ := h
    simp only [rank]; omega
  | share => cases h; simp only [rank]; omega
  | bar =>
    simp only [next] at h
    split_ifs at h <;> cases h <;> simp only [rank] <;> omega
  | sum =>
    simp only [next] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split_ifs at h with hlt <;> cases h <;> simp only [rank] <;> omega
  | out => cases h; simp only [rank]; omega
  | exit => simp [next] at h

/-- **Consistent executions have bounded size.** -/
theorem bound_goal (hpre : Pre L A B x mem0) : BoundGoal kernel Prod L mem0 :=
  Frame.bound_of_rank (C := codes A B L) (fun _ hg => sound hpre hg)
    (fun _ hX => (thread_facts hpre hX).tracked) (fun _ => rank)
    (fun _ _ _ _ _ h => rank_step h) 261 (fun _ _ => le_rfl)
    (fun X hX _ _ hb => absurd hb (noTma_of_consistent (by rfl : kernel.NoTma) hX).not_copy)

end
end PTX.Kernels.BlockSum.Proof
