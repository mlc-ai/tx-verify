-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU
public import Lemmas.Flow.Step.TcSteps

@[expose] public section

namespace PTX.Flow

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- The substep-one continuation of a successful hooked load, independent of the address
and of the returned words. -/
theorem fires_tcLd_loadU {ds : List Nat} {ta pc : Nat} {sh : TcShape} {t u : TState} {e : Event}
    (hsh : ∀ s, sh ≠ .packed16 s) (hw : A.any (·.tcLdWait t.pc) = true) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e (some u)) :
    ∃ a vals, e = ⟨pc, .tc (.ld a vals sh)⟩ ∧
      u = { setRegs (next t) ds vals with pc := t.pc, sub := 1 } := by
  simp only [eventTmpl, tcLdTmpl, hw, ↓reduceIte, hs, tcTmpl_tcLd_none hsh] at hf
  cases ha : readBits L g t 32 (.reg ta) with
  | error f =>
    simp only [ofExec, ha, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf <;> cases hf.2
  | ok addr =>
    simp only [ofExec, ha, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Tmpl.thenWaitLd, Fires, reduceCtorEq, and_false] at hf
    obtain ⟨vals, _, he, hu⟩ := hf
    exact ⟨_, vals, he, Option.some.inj hu⟩

/-- Register destinations discarded by a control machine preserve its live facts. -/
theorem holds_after_tcLd {t : TState} {ds live live' : List Nat} {vs : List Value}
    {val : Nat → Value} (h : Holds t.regs (factsFrom live val))
    (hc : live'.all (fun r => !ds.contains r && live.contains r) = true) :
    Holds (setRegs (next t) ds vs).regs (factsFrom live' val) := by
  apply holds_setRegs_frame (t := next t) (val := val) h
  intro r hr
  have hmem := List.all_eq_true.mp hc r hr
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, decide_eq_true_eq] at hmem
  exact ⟨hmem.1, hmem.2, rfl⟩

end PTX.Flow
