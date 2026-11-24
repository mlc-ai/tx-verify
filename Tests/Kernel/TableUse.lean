-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.TableUse

/-! # Classifying an object family by one evaluated check

Two sites: site 0's events may arrive on offset 32 or poll offset 56, site 1's may commit to
offset 56. The family `[56]` is used only by polls and commits (`ok`), checked by `decide` over
the table, so every event of a followed thread naming offset 56 is a poll or a commit. -/

namespace PTX.Tests.TableUse
open PTX PTX.Frame

/-- Use kinds of the example. -/
inductive U | arrive | poll | commit
  deriving DecidableEq

def uses : Nat → List (Nat × U)
  | 0 => [(32, .arrive), (56, .poll)]
  | _ => [(56, .commit)]

def ok : U → Bool
  | .arrive => false
  | _ => true

example {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
    {C : (g : Nat) → Flow.Code K A L g} {T : RoleTable C} {S : Nat → Prop}
    (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S)
    (hF : T.Followed X S) (site : ∀ g, (C g).D → Nat) (useOf : Event → U)
    (obj : Nat → Nat → Loc) (hsite : ∀ g, S g → ∀ d, T.J g d → site g d ∈ [0, 1])
    (hev : ∀ g, S g → ∀ d e o, T.J g d → (C g).inv d → T.Ev g d e → MbarOf e (obj g o) →
      (o, useOf e) ∈ uses (site g d))
    {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hm : MbarOf e (obj g 56)) :
    useOf e = .poll ∨ useOf e = .commit := by
  have h := RoleTable.table_use hC hX hT hF site [0, 1] uses useOf obj hsite hev [56] ok
    (by decide) hg he hub hm (by simp)
  revert h
  cases useOf e <;> simp [ok]

end PTX.Tests.TableUse
