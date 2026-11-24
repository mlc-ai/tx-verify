-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.WaitAcquire
public import Lemmas.Flow.EndSite

@[expose] public section

/-! # Retrying a poll

A proof tool. The template of an `mbarrier.try_wait` is undefined behaviour or a poll, which
may succeed (`mbarWait_tmpl`); a run never ends at a poll (`run_last_not_wait`). -/

namespace PTX.Flow

open PTX.Proof

/-- An `mbarrier.try_wait` template is undefined behaviour or a poll. -/
theorem mbarWait_tmpl {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {p' : Nat}
    {b : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} :
    (∃ f, eventTmpl A L g t (.mbarWait p' b off par acq sc) = .ub f) ∨
      ∃ m q k acq' sc', eventTmpl A L g t (.mbarWait p' b off par acq sc) = .wait m q k acq' sc' :=
        by
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure]
  cases hm : mbarLoc L g t b off with
  | error f => exact .inl ⟨f, by simp [ofExec, widenMbarScope]⟩
  | ok m =>
    cases hq : readBits L g t 32 par with
    | error f => exact .inl ⟨f, by simp [ofExec, widenMbarScope]⟩
    | ok q =>
      right
      simp only [ofExec, widenMbarScope]
      split_ifs <;> (try split) <;> first | exact ⟨_, _, _, _, _, rfl⟩ | simp_all

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A run that ends does not end at a poll. -/
theorem run_last_not_wait {t : TState} {es : List Event} (hr : Run K A L g t es none) :
    ∀ pc m p ok acq sc, es.getLast? ≠ some ⟨pc, .wait m p ok acq sc⟩ := by
  generalize ho : (none : Option TState) = o at hr
  induction hr with
  | nil => cases ho
  | @step t0 t1 t2 e0 rest o0 _ _ hrest ih =>
    intro pc m p ok acq sc h
    match rest, hrest with
    | [], hr => cases hr; cases ho
    | e' :: rest', _ =>
      exact ih ho pc m p ok acq sc (by simpa [List.getLast?_cons] using h)
  | last hl he =>
    intro pc m p ok acq sc h
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    obtain ⟨tm, -, hf⟩ := he
    cases tm <;> simp [Fires] at hf

end PTX.Flow
