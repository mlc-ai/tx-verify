-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Protocol.Events
public import Lemmas.Kernel.Bound

@[expose] public section

/-! # Consistent executions have bounded size

A rank on a thread's sites that every counted event lowers by one bounds each thread's counted
events (`Frame.bound_of_rank`); a failed poll counts nothing and keeps the site. The one copy
writes 16 bytes (`bulk_cases`). -/

namespace PTX.Kernels.TmaCopy.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0}

/-- The counted events a thread has left, at most. -/
def siteRank : Site → Nat
  | .init => 8 | .fence => 7 | .arrive => 6 | .bulk => 5 | .wait => 4 | .load => 3
  | .store _ => 2 | .exit => 1

/-- Every machine step lowers the rank by its counted event. -/
theorem rank_step {d d' : Site} {e : Event} (hn : next d e = some (some d')) :
    siteRank d' + (if e.counts then 1 else 0) ≤ siteRank d := by
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  obtain ⟨pc, k⟩ := e
  cases d with
  | wait =>
    cases k <;> simp only [next] at hn <;> try cases hn
    rename_i ok _ _
    cases ok <;> simp [siteRank, Event.counts]
  | load =>
    simp only [next] at hn
    split at hn
    · split at hn
      · cases hn; simp only [siteRank]; omega
      · cases hn
    · cases hn
  | store v =>
    simp only [next] at hn
    split at hn
    · cases hn; simp only [siteRank]; omega
    · cases hn
  | exit => simp [next] at hn
  | _ => cases hn; simp only [siteRank]; omega

/-- **Consistent executions have bounded size.** -/
theorem bound_goal (hpre : Pre L A B x mem0)
    (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A B X) :
    BoundGoal kernel [] L mem0 :=
  Frame.bound_of_rank (C := code L A B) (fun _ hg => sound hpre hg)
    (fun X hX => (hT X hX).tracked) (fun _ => siteRank) (fun _ _ _ _ _ hn => rank_step hn) 8
    (fun g _ => by
      show siteRank (if g = 0 then .init else .exit) ≤ 8
      split <;> simp [siteRank])
    (fun X hX _ _ hb => by
      obtain ⟨-, rfl⟩ := bulk_cases (hT X hX) hX hb
      simp [copySpec, bulkSpec])

end

end PTX.Kernels.TmaCopy.Proof
