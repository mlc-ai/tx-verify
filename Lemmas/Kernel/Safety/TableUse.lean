-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Classes

@[expose] public section

/-! # Who uses an mbarrier object, from a role table and one evaluated check

A proof tool (review item 8, the library half of the per-object user classifications such as
tml-fa4's `kv_use`, `empty_use`, `sfull_use`). A kernel states, once per role, a literal table of
the objects a site's events may name and how (`uses : σ → List (Nat × U)`: offsets with a use
kind, an over-approximation; a ring slot that depends on the round lists every slot), where its
followed states sit (`site`, inside a finite list `sites`), and that every event of a state names
only objects of its site's table (`hev`, from the shape table). Then a family of objects `F` is
classified by one evaluated check over the table (`hchk`, by `decide`): every event of a followed
thread that names an object of `F` has a use kind `ok` accepts (`RoleTable.table_use`), and no
event names an object of `F` when no site's table lists one (`RoleTable.table_noUse`). Each new
object family is a new `F` and `ok`, not a new case analysis over the roles. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

/-- **An event naming an object of the family has a use kind the check accepts.** -/
theorem RoleTable.table_use (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
    (hT : T.ShapeOk S) (hF : T.Followed X S) {σ U : Type} (site : ∀ g, (C g).D → σ)
    (sites : List σ) (uses : σ → List (Nat × U)) (useOf : Event → U) (obj : Nat → Nat → Loc)
    (hsite : ∀ g, S g → ∀ d, T.J g d → site g d ∈ sites)
    (hev : ∀ g, S g → ∀ d e o, T.J g d → (C g).inv d → T.Ev g d e → MbarOf e (obj g o) →
      (o, useOf e) ∈ uses (site g d))
    (Fam : List Nat) (ok : U → Bool)
    (hchk : sites.all (fun s => (uses s).all fun p => !(Fam.contains p.1) || ok p.2) = true)
    {g k o : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hm : MbarOf e (obj g o)) (ho : o ∈ Fam) :
    ok (useOf e) = true := by
  obtain ⟨d, -, hJ, hi, hEv⟩ := RoleTable.ev_of_ne_ub hC hX hT hF hg he hub
  have hmem := hev g hg d e o hJ hi hEv hm
  have h1 := List.all_eq_true.mp hchk _ (hsite g hg d hJ)
  have h2 := List.all_eq_true.mp h1 _ hmem
  have hc : Fam.contains o = true := List.contains_iff_mem.mpr ho
  simp only [hc, Bool.not_true, Bool.false_or] at h2
  exact h2

/-- **No event of a followed thread names an object of the family** when no site's table lists
one. -/
theorem RoleTable.table_noUse (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S) (hF : T.Followed X S) {σ U : Type}
    (site : ∀ g, (C g).D → σ) (sites : List σ) (uses : σ → List (Nat × U))
    (useOf : Event → U) (obj : Nat → Nat → Loc)
    (hsite : ∀ g, S g → ∀ d, T.J g d → site g d ∈ sites)
    (hev : ∀ g, S g → ∀ d e o, T.J g d → (C g).inv d → T.Ev g d e → MbarOf e (obj g o) →
      (o, useOf e) ∈ uses (site g d))
    (Fam : List Nat) (hchk : sites.all (fun s => (uses s).all fun p => !(Fam.contains p.1)) = true)
    {g k o : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hm : MbarOf e (obj g o)) (ho : o ∈ Fam) : False := by
  have h := RoleTable.table_use hC hX hT hF site sites uses useOf obj hsite hev Fam
    (fun _ => false) (by simpa using hchk) hg he hub hm ho
  cases h

end
end PTX.Frame
