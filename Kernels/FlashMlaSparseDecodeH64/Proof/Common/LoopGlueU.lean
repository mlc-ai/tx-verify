-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LoopGlue
public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Roles

@[expose] public section

/-! # The UB-tolerant step obligations of a dispatch level

Kernel-independent (a library candidate for lane L): `Code.loopGlue_steps` and
`Code.roleLoop_steps` with the UB-tolerant obligations of `Lemmas/Flow/CodeU.lean`. A role whose
site can fault on a word another thread wrote proves `StepAtU` there; a role with strict
obligations converts by `StepAt.toStepAtU`. The proofs are the strict ones with the concrete
successor's `GoodU` (a good state, or undefined behaviour during the crossing). -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

namespace Code

variable {P : Code K A L g} {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}
  {back : (i : ι) → (R i).D → Option P.D}

/-- **The UB-tolerant step obligations of the loop glue.** -/
theorem loopGlue_stepsU (hP : ∀ d, exit d = none → P.StepAtU d)
    (hR : ∀ i d, back i d = none → (R i).StepAtU d) (hglue : Handoff P R exit)
    (hback : Back P R back) (hinit : ∀ i, back i (R i).init = none) :
    ∀ d, (loopGlue P R exit back).StepAtU d := by
  intro d
  cases d with
  | inl d =>
    by_cases hx : exit d = none
    · have hs := hP d hx
      refine ⟨fun hinv => hs.site hinv.1, ?_⟩
      intro t e u ins hat hinv hc hf
      rcases hs.step ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (by show (P.next d e).map _ = _; rw [hn]; rfl))
      · exact .inl (.inr ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl,
          hl, hg.imp (good_enter_loop hglue hinit) id⟩)
      · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩
    · exact ⟨fun hinv => absurd hinv.2 hx, fun _ _ hinv => absurd hinv.2 hx⟩
  | inr s =>
    obtain ⟨i, d⟩ := s
    by_cases hb : back i d = none
    · have hs := hR i d hb
      refine ⟨fun hinv => hs.site hinv.1, ?_⟩
      intro t e u ins hat hinv hc hf
      rcases hs.step ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (by show ((R i).next d e).map _ = _; rw [hn]; rfl))
      · exact .inl (.inr ⟨backEnter P R exit back i d', t',
          by show ((R i).next d e).map _ = _; rw [hn]; rfl, hl,
          hg.imp (good_backEnter hglue hback hinit) id⟩)
      · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩
    · exact ⟨fun hinv => absurd hinv.2 hb, fun _ _ hinv => absurd hinv.2 hb⟩

variable {E : Type} {pcOf : E → Nat} {sel : E → P.D → Option ι}

/-- The hand-offs of a dispatch level with stubs at its entries' pcs, from one hand-off per
sub-role (as `roleLoop_steps`). -/
theorem handoff_gatedAt {enterOf : P.D → Option E}
    (hstub : ∀ d r, enterOf d = some r → P.inv d →
      P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [] ∧ StubSite K (pcOf r) = true)
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init) :
    Handoff P (withStubsAt R pcOf) (gatedExit enterOf sel) := by
  intro d j t hx hat hinv
  cases he : enterOf d with
  | none => simp [gatedExit, he] at hx
  | some r =>
    simp only [gatedExit, he, Option.map_some, Option.some.injEq] at hx
    cases hs : sel r d with
    | some i =>
      rw [hs] at hx
      subst hx
      exact hrole d r i t he hs hat hinv
    | none =>
      rw [hs] at hx
      subst hx
      obtain ⟨hpc, hsub, hacc, hsite⟩ := hstub d r he hinv
      obtain ⟨h1, h2, h3, h4, -⟩ := hat
      exact ⟨⟨h1.trans hpc, h2.trans hsub, h3.trans hacc, h4, trivial⟩, hsite⟩

/-- **The UB-tolerant step obligations of a dispatch level** (`roleLoop_steps` with
`StepAtU`). -/
theorem roleLoop_stepsU {enterOf : P.D → Option E}
    (hP : ∀ d, enterOf d = none → P.StepAtU d) (hR : ∀ i d, back i d = none → (R i).StepAtU d)
    (hstub : ∀ d r, enterOf d = some r → P.inv d →
      P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [] ∧ StubSite K (pcOf r) = true)
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init)
    (hback : ∀ i d p t, back i d = some p → (R i).AtD d t → (R i).inv d → P.AtD p t ∧ P.inv p)
    (hinit : ∀ i, back i (R i).init = none) :
    ∀ d, (roleLoop P R pcOf enterOf sel back).StepAtU d := by
  refine loopGlue_stepsU (fun d hx => hP d (gatedExit_none.mp hx))
    (fun j => match j with
      | .inl i => fun d hb => hR i d hb
      | .inr _ => fun d _ => (stopAt_steps d).toStepAtU) (handoff_gatedAt hstub hrole) ?_ ?_
  · rintro (i | r) d p t hb hat hinv
    · exact hback i d p t hb hat hinv
    · cases hb
  · rintro (i | r)
    · exact hinit i
    · rfl

end Code
end
end PTX.Flow
