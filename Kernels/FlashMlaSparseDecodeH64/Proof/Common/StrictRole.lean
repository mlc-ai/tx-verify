-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LoopGlueU
public import Lemmas.Flow.StrictLift

@[expose] public section

/-! # The strict step of one state for one event, at a dispatch level

Kernel-independent (a library candidate for lane L): `Code.roleLoop_inl_stepFor` and
`Code.roleLoop_inr_stepFor`, the strict step obligation (`Code.StepFor`) of the dispatcher's state
or of a sub-role's state of a `Code.roleLoop`, for one event, from that of the state it is built
from, with the hand-offs of `Code.roleLoop_stepsU`. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

namespace Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
  {P : Code K A L g} {ι E : Type} {R : ι → Code K A L g} {pcOf : E → Nat}
  {enterOf : P.D → Option E} {sel : E → P.D → Option ι}
  {back : (i : ι) → (R i).D → Option P.D}

/-- **The strict step of a dispatcher's state of a `Code.roleLoop`**, from the level's. -/
theorem roleLoop_inl_stepFor {d : P.D} {e : Event}
    (hP : enterOf d = none → P.StepFor d e)
    (hstub : ∀ d r, enterOf d = some r → P.inv d →
      P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [] ∧ StubSite K (pcOf r) = true)
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init)
    (hinit : ∀ i, back i (R i).init = none) :
    (roleLoop P R pcOf enterOf sel back).StepFor (Sum.inl d) e :=
  loopGlue_inl_stepFor (fun hx => hP (gatedExit_none.mp hx)) (handoff_gatedAt hstub hrole)
    (fun j => match j with
      | Sum.inl i => hinit i
      | Sum.inr _ => rfl)

/-- **The strict step of a sub-role's state of a `Code.roleLoop`**, from the role's. -/
theorem roleLoop_inr_stepFor {i : ι} {d : (R i).D} {e : Event}
    (hR : back i d = none → (R i).StepFor d e)
    (hstub : ∀ d r, enterOf d = some r → P.inv d →
      P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [] ∧ StubSite K (pcOf r) = true)
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init)
    (hback : ∀ i d p t, back i d = some p → (R i).AtD d t → (R i).inv d → P.AtD p t ∧ P.inv p)
    (hinit : ∀ i, back i (R i).init = none) :
    (roleLoop P R pcOf enterOf sel back).StepFor (.inr ⟨Sum.inl i, d⟩) e :=
  loopGlue_inr_stepFor (i := Sum.inl i) hR (handoff_gatedAt hstub hrole)
    (by
      rintro (i | r) d p t hb hat hinv
      · exact hback i d p t hb hat hinv
      · cases hb)
    (fun j => match j with
      | Sum.inl i => hinit i
      | Sum.inr _ => rfl)


end Code
end
end PTX.Flow
