-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Interface
public import Lemmas.Kernel.Bound

@[expose] public section

/-! # `copy_ldg`: executions are bounded

A thread's machine moves from the load to the store to the exit, so the number of sites still
ahead (`rank`) decreases with every event: a thread has at most four counted events, and every
consistent execution has bounded size (`Frame.bound_of_rank`). -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0}

/-- The sites still ahead of a state. -/
def rank : Site → Nat
  | .load => 2
  | .store _ => 1
  | .exit => 0

/-- Every machine step lowers the rank by its counted event. -/
theorem rank_step {g : Nat} {d d' : Site} {e : Event}
    (hn : (code L A B N g).next d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  cases d with
  | load =>
    simp only [code, next] at hn
    split at hn
    · split at hn
      · cases hn; simp only [rank]; omega
      · cases hn
    · cases hn
  | store =>
    simp only [code, next] at hn
    split at hn
    · cases hn; simp only [rank]; omega
    · cases hn
  | exit => simp [code, next] at hn

/-- **`BoundGoal`.** -/
theorem bound_goal (hpre : Pre L A B N x mem0)
    (hthr : ∀ X, Consistent L kernel Nc mem0 X → ThreadFacts L A B N X) :
    BoundGoal kernel Nc L mem0 :=
  Frame.bound_of_rank (C := code L A B N) (sound_all hpre) (fun X hX => (hthr X hX).tracked)
    (fun _ => rank) (fun _ _ _ _ _ hn => rank_step hn) 2
    (fun g _ => by
      show rank (if g < N then .load else .exit) ≤ 2
      split <;> simp [rank])
    (fun X hX i s hb => absurd hb (noTma_of_consistent (by rfl : kernel.NoTma) hX).not_copy)

end
end PTX.Kernels.CopyLdg.Proof
