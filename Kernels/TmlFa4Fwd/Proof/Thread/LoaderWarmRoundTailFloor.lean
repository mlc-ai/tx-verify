-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTailDone
public import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.ReturningPrefix
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryBoxProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The pcs of the warm tail above which the loader never branches back. -/
def TailFloor (floor : Nat) : Prop := floor = 1365 ∨ floor = 1371 ∨ floor = 1378

set_option maxRecDepth 100000 in
private theorem tailFloorAudit {floor : Nat} (h : TailFloor floor) :
    (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true ∧
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by kernel_rfl,by kernel_rfl⟩

set_option maxRecDepth 4096 in
/-- A lane that has passed a tail floor stays at or above it. -/
theorem tailFloorReach {l : Launch} {t floor : Nat} (hFloor : TailFloor floor)
    {s u : TState} {es : List Event} (h : TraceReach kernel Assumptions.all l t s es u)
    (hs : floor ≤ s.pc) : floor ≤ u.pc := by
  obtain ⟨hTail,hSeg⟩ := tailFloorAudit hFloor
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (eventTailStepOfAudit hTail hSeg hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (eventTailStepOfAudit hTail hSeg hs (.inr ⟨_,rfl,he⟩))

/-- An event inside a returning run returns, and the run continues from its result. -/
theorem stepAfterEvent {l : Launch} {t : Nat} {s q : TState} {es : List Event}
    (h : Run kernel Assumptions.all l t s es (some q)) {j : Nat} {e : Event}
    (he : es[j]? = some e) :
    ∃ t1 u, TraceReach kernel Assumptions.all l t s (es.take j) t1 ∧
      EStep kernel Assumptions.all l t t1 e (some u) ∧
      Run kernel Assumptions.all l t u (es.drop (j+1)) (some q) := by
  induction es generalizing s j with
  | nil => simp at he
  | cons e0 rest ih =>
    cases h with
    | step hTau hStep hRest =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at he
        subst he
        exact ⟨_,_,.of_local hTau,hStep,by simpa using hRest⟩
      | succ i =>
        obtain ⟨t1,u,hReach,hE,hRun⟩ := ih hRest (by simpa using he)
        have hFirst : TraceReach kernel Assumptions.all l t s [e0] _ :=
          (Run.step hTau hStep (.nil _)).returning_reach
        refine ⟨t1,u,?_,hE,by simpa using hRun⟩
        have h := hFirst.append hReach
        simpa using h

/-- A lane that recorded an event whose result lies above a tail floor never reaches a point
below the floor afterwards. -/
theorem noReturnBelowTailFloor {l : Launch} {X : Execution} {t j stop floor : Nat}
    (hFloor : TailFloor floor) {e : Event} (he : X.get (t,j) = some e) (hj : j < stop)
    (hResult : ∀ {s u : TState}, EStep kernel Assumptions.all l t s e (some u) → floor ≤ u.pc)
    {target : TState}
    (hTarget : TraceReach kernel Assumptions.all l t {} ((X.tr t).take stop) target)
    (hBelow : target.pc < floor) : False := by
  obtain ⟨q,hQ,hLocal⟩ := hTarget.returnedPrefix
  have hIn : ((X.tr t).take stop)[j]? = some e := by rwa [List.getElem?_take_of_lt hj]
  obtain ⟨_,u,_,hStep,hRest⟩ := stepAfterEvent hQ hIn
  have hCore := hRest.returning_reach.append (.of_local hLocal)
  rw [List.append_nil] at hCore
  have := tailFloorReach hFloor hCore (hResult hStep)
  omega

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
