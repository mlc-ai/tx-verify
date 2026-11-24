-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Facts
public import Kernels.RmsNorm.Proof.Protocol.Pos
public import Lemmas.Kernel.Bound

@[expose] public section

/-! # Consistent executions have bounded size

A rank on a thread's abstract states that every step decreases by at least one bounds each
thread's counted events (`Frame.bound_of_rank`): `80` per row left, and within a row the sites
in their order (`D.ord`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The events a thread has left, at most. -/
def rank (P : Params) (d : D) : Nat :=
  match d.site with
  | .shfl0 => 80 * (P.Bt + 1) + 1
  | .exit => 0
  | _ => 80 * (P.Bt - d.i) + (80 - d.ord)

theorem loadNext_cases {d d' : D} {e : Event} {k : List Value → Option D}
    (h : loadNext d e k = some (some d')) :
    (d'.site = d.site ∧ d'.sub = d.sub + 1 ∧ d.sub + 1 < 4 ∧ d'.i = d.i) ∨
    ∃ vs, k vs = some d' := by
  unfold loadNext at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split_ifs at h with hlt
  · cases h; exact .inl ⟨rfl, rfl, hlt, rfl⟩
  · obtain ⟨d'', hk', h'⟩ := Option.map_eq_some_iff.mp h
    cases h'
    exact .inr ⟨_, hk'⟩

theorem storeNext_cases {d d0 d' : D} (h : storeNext d d0 = some (some d')) :
    (d'.site = d.site ∧ d'.sub = d.sub + 1 ∧ d.sub + 1 < 4 ∧ d'.i = d.i) ∨ d' = d0 := by
  unfold storeNext at h
  split_ifs at h with hlt
  · cases h; exact .inl ⟨rfl, rfl, hlt, rfl⟩
  · cases h; exact .inr rfl

/-- The ranks of a step, by `simp_all` and, if needed, `omega`. -/
macro "rk_omega" : tactic => `(tactic| first
  | (simp_all [rank, D.ord, row]; done)
  | (simp_all [rank, D.ord, row]; omega))

/-- One step of a site: an element of a vector access, or the site's successor. -/
macro "rk_close" : tactic => `(tactic| first
  | (rcases loadNext_cases (by assumption) with ⟨h1, h2, h3, h4⟩ | ⟨vs, hk⟩
     · simp only [rank, D.ord, h1, h2, h4, *]; omega
     · (try split at hk) <;> first | (cases hk; done) |
          (cases hk; simp [rank, D.ord, tileA, tileB, *] <;> omega))
  | (rcases storeNext_cases (by assumption) with ⟨h1, h2, h3, h4⟩ | rfl
     · simp only [rank, D.ord, h1, h2, h4, *]; omega
     · simp [rank, D.ord, *]; omega))

theorem rank_step {g : Nat} {d d' : D} {e : Event} (h : next P g d e = some (some d')) :
    rank P d' + (if e.counts then 1 else 0) ≤ rank P d := by
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  suffices rank P d' + 1 ≤ rank P d by omega
  rcases hs : d.site with _ | _ | _ | _ | _ | _ | _ | k | _ | _ | _ | k | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ <;> simp only [next, hs] at h
  all_goals first
    | rk_close
    | ((repeat' split at h) <;> (try simp only [reduceCtorEq] at h) <;>
        (try (simp only [Option.some.injEq] at h; subst h)) <;> (try unfold bfaNext) <;>
        (try unfold bfbNext) <;> (try split_ifs) <;> rk_omega)

/-- **Consistent executions have bounded size.** -/
theorem bound_goal (hpre : Pre P L mem0) : BoundGoal kernel Prod L mem0 :=
  Frame.bound_of_rank (C := codes P L) (fun _ hg => sound hpre hg)
    (fun _ hX => (thread_facts hpre hX).tracked) (fun _ => rank P)
    (fun _ _ _ _ _ h => rank_step h) (80 * (P.Bt + 1) + 1) (fun _ _ => le_rfl)
    (fun _ hX _ _ ⟨_, hp⟩ => by
      obtain ⟨-, d, hA⟩ := event_facts hpre hX (thread_facts hpre hX) hp
        (by intro _ _ h; cases h)
      exact (copy_site hA.event).elim)

end
end PTX.Kernels.RmsNorm.Proof
