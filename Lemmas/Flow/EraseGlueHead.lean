-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Erase

@[expose] public section

/-! # Erasure through a glue whose first fragment erases too

A proof tool, generic over the kernel. `Erases.glue` keeps the first fragment `P` fixed. Here the
first fragment is itself a value machine `P'` that erases to `P` (`er0`), with exits that follow
the erased state (`exit' d = exit (er0 d)`); the roles erase as before. The glue erases by
`eraseSumH`: `er0` on the first fragment's states and the role's erasure on a role state. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The erasure of a glued state whose first fragment erases as well. -/
def eraseSumH {P' P : Code K A L g} {ι : Type} {R' R : ι → Code K A L g}
    (er0 : P'.D → P.D) (er : ∀ i, (R' i).D → (R i).D) :
    P'.D ⊕ (Σ i, (R' i).D) → P.D ⊕ (Σ i, (R i).D)
  | .inl d => .inl (er0 d)
  | .inr ⟨i, d⟩ => .inr ⟨i, er i d⟩

/-- **The glue keeps erasure when its first fragment erases**: exits that follow the erased
state, roles that erase. -/
theorem Erases.glueHead {P' P : Code K A L g} {ι : Type} {R' R : ι → Code K A L g}
    {exit' : P'.D → Option ι} {exit : P.D → Option ι} {er0 : P'.D → P.D}
    {er : ∀ i, (R' i).D → (R i).D} (hP : Erases P' P er0) (hx : ∀ d, exit' d = exit (er0 d))
    (h : ∀ i, Erases (R' i) (R i) (er i)) :
    Erases (Code.glue P' R' exit') (Code.glue P R exit) (eraseSumH er0 er) := by
  have hen : ∀ d, eraseSumH er0 er (enter P' R' exit' d) = enter P R exit (er0 d) := by
    intro d
    unfold enter
    rw [hx d]
    cases exit (er0 d) with
    | none => rfl
    | some i => simp only [eraseSumH, (h i).init]
  refine ⟨?_, fun {d e d'} hn => ?_⟩
  · rw [show (Code.glue P' R' exit').init = enter P' R' exit' P'.init from rfl, hen, hP.init]
  cases d with
  | inl d =>
    change (P'.next d e).map (Option.map (enter P' R' exit')) = _ at hn
    change (P.next (er0 d) e).map (Option.map (enter P R exit)) = _
    rcases hp : P'.next d e with _ | _ | b
    · rw [hp] at hn; cases hn
    · rw [hp] at hn; cases hn
    · rw [hp] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      rw [hP.next hp]
      simp only [Option.map_some, hen]
  | inr a =>
    obtain ⟨i, d⟩ := a
    change ((R' i).next d e).map
      (Option.map fun d' => (Sum.inr ⟨i, d'⟩ : P'.D ⊕ (Σ i, (R' i).D))) = _ at hn
    change ((R i).next (er i d) e).map
      (Option.map fun d' => (Sum.inr ⟨i, d'⟩ : P.D ⊕ (Σ i, (R i).D))) = _
    rcases hp : (R' i).next d e with _ | _ | b
    · rw [hp] at hn; cases hn
    · rw [hp] at hn; cases hn
    · rw [hp] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      rw [(h i).next hp]
      rfl

end
end PTX.Flow.Code
