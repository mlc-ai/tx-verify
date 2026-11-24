-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Events
public import Lemmas.Kernel.Bound

@[expose] public section

/-! # Consistent executions have bounded size

A rank on a thread's sites that every counted event lowers by one bounds each thread's counted
events (`Frame.bound_of_rank`); a failed poll counts nothing and keeps the site. The copies write
4096 and 256 bytes (`Wit.bulk`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0}

/-- The counted events a thread has left, at most. -/
def siteRank : Site → Nat
  | .alloc => 30 | .allocSt => 29 | .init0 => 28 | .init1 => 27 | .fence => 26 | .arrive => 25
  | .bulkA => 24 | .bulkB => 23 | .bar0 _ => 22 | .load _ => 21 | .wait0 => 20 | .mma => 19
  | .commit => 18 | .wait1 => 17 | .fence1 => 16 | .ld => 15 | .waitLd => 14 | .st j => if j < 8
      then 13 - j else 6
  | .fenceB => 5 | .bar1 => 4 | .fence2 => 3 | .dealloc => 2 | .exit => 1

/-- Every machine step lowers the rank by its counted event. -/
theorem rank_step {g : Nat} {d d' : ThreadD} {e : Event} (hn : next g d e = some (some d')) :
    siteRank d'.site + (if e.counts then 1 else 0) ≤ siteRank d.site := by
  have hc : (if e.counts then 1 else 0) ≤ 1 := by split <;> omega
  obtain ⟨site, c, vals⟩ := d
  obtain ⟨pc, k⟩ := e
  cases site with
  | load z =>
    simp only [next] at hn
    split at hn
    · rename_i _ bs
      cases h : rdCol bs <;> simp only [h, Option.map_none, Option.map_some, reduceCtorEq,
        Option.some.injEq] at hn
      subst hn
      split <;> simp only [siteRank] <;> omega
    · cases hn
  | wait0 =>
    cases k <;> simp only [next] at hn <;> try cases hn
    rename_i ok _ _
    cases ok <;> simp [siteRank, Event.counts]
  | wait1 =>
    cases k <;> simp only [next] at hn <;> try cases hn
    rename_i ok _ _
    cases ok <;> simp [siteRank, Event.counts]
  | ld =>
    simp only [next] at hn
    split at hn
    · cases hn; simp only [siteRank]; omega
    · cases hn
  | st j =>
    simp only [next] at hn
    split at hn
    · cases hn
      by_cases hj : j < 7
      · simp only [hj, ↓reduceIte, siteRank, show j < 8 by omega, show j + 1 < 8 by omega]
        omega
      · simp only [hj, ↓reduceIte, siteRank]
        split_ifs <;> omega
    · cases hn
  | alloc =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    split <;> simp only [siteRank] <;> omega
  | fence2 =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    split <;> simp only [siteRank] <;> omega
  | exit => simp [next] at hn
  | _ =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    simp only [siteRank]
    first | omega | (split_ifs <;> omega)

/-- **Consistent executions have bounded size.** -/
theorem bound_goal (hpre : Pre L A B D a b mem0) (hC : ∀ g < L.threads, (code L A B D g).Sound)
    (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A B D X) :
    BoundGoal kernel [] L mem0 :=
  Frame.bound_of_rank (C := code L A B D) hC (fun X hX => (hT X hX).tracked)
    (fun _ d => siteRank d.site) (fun _ _ _ _ _ hn => rank_step hn) 30
    (fun g _ => by
      show siteRank (if g / 32 = 0 then Site.alloc else .bar0 false) ≤ 30
      split <;> simp [siteRank])
    (fun X hX ⟨g, j⟩ s ⟨pc, hb⟩ => by
      obtain ⟨P, m, u, hW⟩ := wit hpre (hT X hX) hX
      obtain ⟨-, -, -, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := hW.bulk hb <;> simp [specA, specB, bulkSpec])

end

end PTX.Kernels.TcGemm.Proof
