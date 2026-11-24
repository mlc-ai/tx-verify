-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-!
# Blocked-obligation descent

Kernel-independent shape of a progress argument. A maximal execution has no counted
consistent extension (`Maximal.not_grows`). Outstanding obligations are ranked by a
natural number. If every outstanding obligation of a maximal execution either yields a
counted consistent extension or is blocked by an outstanding obligation of strictly
smaller rank in some maximal execution, no maximal execution has an outstanding
obligation (`maximal_no_obligation`). The minimal-witness form (`exists_minimal`) is the
same well-foundedness argument on a fixed Nat-ranked type.
-/

namespace PTX.Proof.ProgressDescent
open PTX

/-- Some element of a nonempty Nat-ranked type has least rank. -/
theorem exists_minimal {α : Sort _} (rank : α → Nat) (h : Nonempty α) :
    ∃ a, ∀ b, rank a ≤ rank b := by
  classical
  have hex : ∃ n a, rank a = n := by obtain ⟨a⟩ := h; exact ⟨rank a, a, rfl⟩
  obtain ⟨a, ha⟩ := Nat.find_spec hex
  exact ⟨a, fun b => ha ▸ Nat.find_min' hex ⟨b, rfl⟩⟩

/-- Some witness of a satisfiable predicate has least rank among all its witnesses. -/
theorem exists_minimal_of {α : Sort _} {p : α → Prop} (rank : α → Nat) (h : ∃ a, p a) :
    ∃ a, p a ∧ ∀ b, p b → rank a ≤ rank b := by
  obtain ⟨⟨a, ha⟩, hmin⟩ := exists_minimal (α := {a // p a}) (fun a => rank a.1)
    (let ⟨a, ha⟩ := h; ⟨⟨a, ha⟩⟩)
  exact ⟨a, ha, fun b hb => hmin ⟨b, hb⟩⟩

/-- Strict descent on a Nat rank excludes every witness. -/
theorem not_of_descent {α : Sort _} {p : α → Prop} (rank : α → Nat)
    (h : ∀ a, p a → ∃ b, p b ∧ rank b < rank a) : ∀ a, ¬ p a := by
  intro a ha
  obtain ⟨m, hm, hmin⟩ := exists_minimal_of rank ⟨a, ha⟩
  obtain ⟨b, hb, hlt⟩ := h m hm
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (hmin b hb))

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A maximal execution has no counted consistent extension. -/
theorem _root_.PTX.Maximal.not_grows (hmax : Maximal L K A mem0 X) :
    ¬ ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  rintro ⟨Y, hY, hle, hs⟩
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hs (hmax.2 Y hY hle))

/-- Blocked-obligation descent. Each outstanding obligation of a maximal execution either
has a counted consistent extension or is blocked by an outstanding obligation of strictly
smaller rank in a maximal execution. Then no maximal execution has an outstanding
obligation. -/
theorem maximal_no_obligation {ι : Sort _} (Obl : Execution → ι → Prop)
    (rank : Execution → ι → Nat)
    (hstep : ∀ X o, Maximal L K A mem0 X → Obl X o →
      (∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L) ∨
      ∃ Y o', Maximal L K A mem0 Y ∧ Obl Y o' ∧ rank Y o' < rank X o) :
    ∀ X o, Maximal L K A mem0 X → ¬ Obl X o := by
  intro X o hmax ho
  refine not_of_descent (p := fun a : Execution ×' ι => Maximal L K A mem0 a.1 ∧ Obl a.1 a.2)
    (fun a => rank a.1 a.2) ?_ ⟨X, o⟩ ⟨hmax, ho⟩
  rintro ⟨X, o⟩ ⟨hmax, ho⟩
  rcases hstep X o hmax ho with hg | ⟨Y, o', hY, hY', hlt⟩
  · exact (hmax.not_grows hg).elim
  · exact ⟨⟨Y, o'⟩, ⟨hY, hY'⟩, hlt⟩

/-- Completeness from blocked-obligation descent: every incomplete maximal execution has
an outstanding obligation. -/
theorem maximal_complete_of_descent {ι : Sort _} (Obl : Execution → ι → Prop)
    (rank : Execution → ι → Nat)
    (hcover : ∀ X, Maximal L K A mem0 X → ¬ Complete L X → ∃ o, Obl X o)
    (hstep : ∀ X o, Maximal L K A mem0 X → Obl X o →
      (∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L) ∨
      ∃ Y o', Maximal L K A mem0 Y ∧ Obl Y o' ∧ rank Y o' < rank X o) :
    ∀ X, Maximal L K A mem0 X → Complete L X := by
  classical
  intro X hmax
  by_contra hn
  obtain ⟨o, ho⟩ := hcover X hmax hn
  exact maximal_no_obligation Obl rank hstep X o hmax ho

end PTX.Proof.ProgressDescent
