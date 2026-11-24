-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Determinism
public import Lemmas.Flow.TraceReach

@[expose] public section

namespace PTX
open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The continuation of a recorded run starts in the unique state returned by its prefix. -/
theorem Run.after_returned_prefix {s u : TState} {before after : List Event}
    {o : Option TState} (hPrefix : Run K A L g s before (some u))
    (hRun : Run K A L g s (before ++ after) o) : Run K A L g u after o := by
  induction before generalizing s with
  | nil =>
    cases hPrefix
    exact hRun
  | cons e rest ih =>
    cases hPrefix with
    | step hLocal he hRest =>
      simp only [List.cons_append] at hRun
      generalize hTrace : rest ++ after = rem at hRun
      cases hRun with
      | step hLocal' he' hRest' =>
        have hSrc := stop_unique hLocal hLocal' (stops_of_estep he) (stops_of_estep he')
        subst hSrc
        obtain rfl := Option.some.inj (estep_det he he')
        exact ih hRest (hTrace.symm ▸ hRest')
      | last hLocal' he' =>
        have hSrc := stop_unique hLocal hLocal' (stops_of_estep he) (stops_of_estep he')
        subst hSrc
        cases estep_det he he'

/-- A returning run records a finite path of local and returning event steps. -/
theorem Run.returning_reach {s u : TState} {es : List Event}
    (hRun : Run K A L g s es (some u)) : TraceReach K A L g s es u := by
  induction es generalizing s with
  | nil =>
    cases hRun
    exact .refl _
  | cons e es ih =>
    cases hRun with
    | step hl he hr =>
      exact (TraceReach.of_local hl).append (.event he (ih hr))

end PTX
