-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Final
public import Lemmas.Flow.WaitAcquire

@[expose] public section

/-! # The template of a poll instruction

A proof tool. An `mbarrier.try_wait` instruction's template is undefined behaviour or a wait on
the object its address evaluates to, with a parity below 2 and the instruction's acquire flag
(`eventTmpl_mbarWait_cases`). A run that ends in a state ends with no event that ends the thread
(`Run.no_end`). -/

namespace PTX.Flow

/-- **The template of a poll instruction**: undefined behaviour, or a wait with a parity below 2
and the instruction's acquire flag. -/
theorem eventTmpl_mbarWait_cases {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {p b : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} :
    (∃ f, eventTmpl A L g t (.mbarWait p b off par acq sc) = .ub f) ∨
      ∃ m q k sc', q < 2 ∧
        eventTmpl A L g t (.mbarWait p b off par acq sc) = .wait m q k acq sc' := by
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure]
  cases hm : mbarLoc L g t b off with
  | error f =>
    left
    simp only [ofExec, widenMbarScope, ite_self]
    exact ⟨f, rfl⟩
  | ok m =>
    cases hq : readBits L g t 32 par with
    | error f =>
      left
      simp only [ofExec, widenMbarScope, ite_self]
      exact ⟨f, rfl⟩
    | ok q =>
      right
      simp only [ofExec]
      cases acq <;> cases sc <;> simp only [widenMbarScope] <;> split_ifs <;>
        exact ⟨m, _, _, _, Nat.mod_lt _ (by decide), rfl⟩

/-- **A poll instruction whose address and parity operands evaluate** has a wait template. -/
theorem eventTmpl_mbarWait_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {p b : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} {m : Loc} {q : BitVec 64}
    (hm : mbarLoc L g t b off = .ok m) (hq : readBits L g t 32 par = .ok q) :
    ∃ k sc', eventTmpl A L g t (.mbarWait p b off par acq sc) =
      .wait m (q.toNat % 2) k acq sc' := by
  simp only [eventTmpl, tmaTmpl, hm, hq, bind, Except.bind, pure, Except.pure, ofExec]
  cases acq <;> cases sc <;> simp only [widenMbarScope] <;> split_ifs <;> exact ⟨_, _, rfl⟩

/-- **A run that ends in a state** has no event that ends the thread. -/
theorem Run.no_end {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t t' : TState}
    {es : List Event} (hr : Run K A L g t es (some t')) : ∀ e ∈ es, ¬ Ends e := by
  generalize ho : some t' = o at hr
  induction hr with
  | nil => simp
  | step hl hs hrest ih =>
    intro e he hend
    rcases List.mem_cons.mp he with rfl | he
    · obtain ⟨m, -, hf⟩ := hs
      cases fires_end_none hf hend
    · exact ih ho e he hend
  | last hl hs => cases ho

end PTX.Flow
