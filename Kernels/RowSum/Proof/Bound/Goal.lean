-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Interface
public import Lemmas.Kernel.Bound

@[expose] public section

/-! # `row_sum`: bounded executions

A thread's machine loads the `K` elements of its row, stores the sum and exits, so the number of
events still ahead (`rank`) decreases with every event: a thread has at most `K + 3` counted
events, and every consistent execution has bounded size (`Frame.bound_of_rank`). -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0}

/-- The events still ahead of a state. -/
def rank (K : Nat) (d : ThreadD) : Nat :=
  match d.site with
  | .load => max (K - d.i) 1 + 1
  | .store => 1
  | .exit => 0

/-- Every machine step lowers the rank by its counted event. -/
theorem rank_step {g : Nat} {d d' : ThreadD} {e : Event}
    (hn : (code L A B M K g).next d e = some (some d')) :
    rank K d' + (if e.counts then 1 else 0) ≤ rank K d := by
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  obtain ⟨s, i, a⟩ := d
  cases s with
  | load =>
    simp only [code, next] at hn
    split at hn
    · split at hn
      · obtain ⟨a', -, hd⟩ := Option.map_eq_some_iff.mp hn
        cases hd
        by_cases h : i + 1 < K <;> simp only [rank, h, ↓reduceIte] <;> omega
      · cases hn
    · cases hn
  | store =>
    simp only [code, next] at hn
    cases hn
    simp only [rank]
    omega
  | exit => simp [code, next] at hn

/-- **Executions are bounded.** -/
theorem bound (hcode : CodeFacts L A B M K)
    (htf : ∀ X, Consistent L kernel Prod mem0 X → ThreadFacts L A B M K x X) :
    BoundGoal kernel Prod L mem0 :=
  Frame.bound_of_rank (C := codes L A B M K) hcode.sound (fun X hX => (htf X hX).tracked)
    (fun _ => rank K) (fun _ _ _ _ _ hn => rank_step hn) (K + 1)
    (fun g _ => by
      show rank K (if M ≤ g then ⟨.exit, 0, b32 0⟩ else if K = 0 then ⟨.store, 0, b32 0⟩
        else ⟨.load, 0, b32 0⟩) ≤ K + 1
      split_ifs <;> simp only [rank] <;> omega)
    (fun X hX _ _ hb => absurd hb (noTma_of_consistent (by rfl : kernel.NoTma) hX).not_copy)

end
end PTX.Kernels.RowSum.Proof
