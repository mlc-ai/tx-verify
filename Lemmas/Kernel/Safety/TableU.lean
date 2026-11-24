-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.FrameU
public import Lemmas.Kernel.Safety.Table
public import Lemmas.Kernel.UbLast

@[expose] public section

namespace PTX.Frame

open PTX.Flow
variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Code K A L g} {X : Execution} {T : RoleTable C} {S : Nat → Prop}

/-- Every event consumed by the prefix is an ordinary event. -/
def NoUbBefore (X : Execution) (g k : Nat) : Prop :=
  ∀ j < k, ∀ e, X.get (g,j) = some e → ∀ f, e.kind ≠ .ub f

theorem noUbBefore_of_get {g k : Nat} {e : Event} (hX : Consistent L K A mem0 X)
    (he : X.get (g,k) = some e) : NoUbBefore X g k := by
  rintro j hj ⟨pc, kind⟩ h f rfl
  exact (Nat.not_le_of_lt hj) (ub_last hX h he)

/-- Control sites need only identify the shape of events that did not fault. -/
structure RoleTable.ShapeOkU (T : RoleTable C) (S : Nat → Prop) : Prop where
  shape : ∀ g, S g → ∀ d t ins e o, T.J g d → (C g).AtD d t → (C g).inv d →
    K.code[(C g).pc d]? = some ins → Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o →
    (∀ f, e.kind ≠ .ub f) → T.Ev g d e

theorem RoleTable.ShapeOk.toShapeOkU {T : RoleTable C} (h : T.ShapeOk S) : T.ShapeOkU S :=
  ⟨fun g hg d t ins e o hJ hat hi hc hf _ => h.shape g hg d t ins e o hJ hat hi hc hf⟩

section shape
variable (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X) (hT : T.ShapeOkU S)
  (hF : T.Followed X S)
include hC hX hT hF

/-- An event fired from a followed state of a thread of `S` has the state's shape. -/
theorem RoleTable.ev_atU {g k : Nat} {d : (C g).D} {e : Event} (hg : S g)
    (he : X.get (g, k) = some e) (hσ : stateAt C X g k = some (some d))
    (hub : ∀ f, e.kind ≠ .ub f) :
    T.J g d ∧ (C g).inv d ∧ T.Ev g d e := by
  have hJ := (hF g hg k).2 d hσ
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := fired_siteU hC hX he hσ hub
  exact ⟨hJ, hi, hT.shape g hg d t ins e o hJ hat hi hc hf hub⟩

/-- **An event of a thread of `S` that is no undefined behaviour is fired from a followed state,
with its shape** (the shape obligation alone: a dead machine fires only undefined behaviour). -/
theorem RoleTable.ev_of_ne_ubU {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ d, stateAt C X g k = some (some d) ∧ T.J g d ∧ (C g).inv d ∧ T.Ev g d e := by
  rcases firedU (C := C) hC hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
  · cases σ with
    | none => exact absurd hσ (hF g hg k).1
    | some d => exact ⟨d, hσ, RoleTable.ev_atU hC hX hT hF hg he hσ hub⟩
  · exact absurd rfl (hub f)

/-- **A per-shape condition holds of every event of a thread of `S` of a kind `P` that excludes
undefined behaviour** (a write, an access, an issue): the form of the frames, which need the shape
obligation alone. -/
theorem RoleTable.forall_kindU {P : Event → Prop} {Q : Nat → Event → Prop}
    (hP : ∀ e, P e → ∀ f, e.kind ≠ .ub f)
    (hQ : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → P e → Q g e) {g k : Nat}
    {e : Event} (hg : S g) (he : X.get (g, k) = some e) (hpe : P e) : Q g e := by
  obtain ⟨d, -, hJ, hi, hev⟩ := RoleTable.ev_of_ne_ubU hC hX hT hF hg he (hP e hpe)
  exact hQ g hg d e hJ hi hev hpe

end shape
end PTX.Frame
