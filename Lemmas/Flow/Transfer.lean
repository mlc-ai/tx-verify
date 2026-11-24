-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code

@[expose] public section

/-! # A site obligation transferred along a map of states

A proof tool, generic over the kernel (promoted from the Inkling pilot). Two site machines
of one thread that agree on a state's program counter, facts, sub-step, accumulator and invariant
through a map `φ` of states, and whose successors agree through `φ` at that state, have the same
step obligation there (`Code.stepAt_map`). A machine whose sites are regrouped into families
reuses the obligations of the flat machine it regroups this way (the Inkling pilot's role
machines), and the events it fires are the flat machine's (`Code.fired_map`, `Code.atD_map`), so
the flat machine's per-site shape lemmas apply. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The step obligation along a map of states.** -/
theorem Code.stepAt_map {C C' : Code K A L g} (φ : C'.D → C.D) {d : C'.D}
    (hpc : C'.pc d = C.pc (φ d)) (hfacts : C'.facts d = C.facts (φ d))
    (hsub : C'.sub d = C.sub (φ d)) (hacc : C'.acc d = C.acc (φ d))
    (hinv : C'.inv d ↔ C.inv (φ d))
    (hsucc : ∀ e d', C'.next d e = some (some d') → (C.inv (φ d') → C'.inv d') ∧
      C'.pc d' = C.pc (φ d') ∧ C'.facts d' = C.facts (φ d') ∧ C'.sub d' = C.sub (φ d') ∧
      C'.acc d' = C.acc (φ d'))
    (hnext : ∀ e, C.next (φ d) e = (C'.next d e).map (Option.map φ))
    (h : C.StepAt (φ d)) : C'.StepAt d where
  site hi := by
    obtain ⟨ins, h1, h2, h3⟩ := h.site (hinv.mp hi)
    exact ⟨ins, hpc ▸ h1, h2, hfacts ▸ h3⟩
  step := by
    intro t e u ins hat hi hc hf
    have hat' : C.AtD (φ d) t := by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hat
      exact ⟨a1.trans hpc, a2.trans hsub, a3.trans hacc, a4, hfacts ▸ a5⟩
    rw [hpc] at hc hf
    have hn := hnext e
    rcases h.step ins hat' (hinv.mp hi) hc hf with (h1 | ⟨d0, t', h1, h2, h3⟩) | ⟨h1, h2⟩
    · left; left
      rw [h1] at hn
      cases hx : C'.next d e with
      | none => rw [hx] at hn; cases hn
      | some o =>
        rw [hx] at hn
        cases o with
        | none => rfl
        | some d' => simp only [Option.map_some] at hn; cases hn
    · left; right
      rw [h1] at hn
      cases hx : C'.next d e with
      | none => rw [hx] at hn; cases hn
      | some o =>
        cases o with
        | none => rw [hx] at hn; cases hn
        | some d' =>
          rw [hx] at hn
          simp only [Option.map_some, Option.some.injEq] at hn
          subst hn
          obtain ⟨hi', hp', hf', hs', ha'⟩ := hsucc e d' hx
          refine ⟨d', t', rfl, h2, ?_, hi' h3.2⟩
          obtain ⟨a1, a2, a3, a4, a5⟩ := h3.1
          exact ⟨a1.trans hp'.symm, a2.trans hs'.symm, a3.trans ha'.symm, a4, hf' ▸ a5⟩
    · right
      refine ⟨?_, h2⟩
      rw [h1] at hn
      cases hx : C'.next d e with
      | none => rfl
      | some o => rw [hx] at hn; cases hn


/-- **A concrete state of a state is a concrete state of its image**, for a map that keeps the
program counter, facts, sub-step and accumulator. -/
theorem Code.atD_map {C C' : Code K A L g} (φ : C'.D → C.D) {d : C'.D} {t : TState}
    (hpc : C'.pc d = C.pc (φ d)) (hfacts : C'.facts d = C.facts (φ d))
    (hsub : C'.sub d = C.sub (φ d)) (hacc : C'.acc d = C.acc (φ d)) (hat : C'.AtD d t) :
    C.AtD (φ d) t := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hat
  exact ⟨a1.trans hpc, a2.trans hsub, a3.trans hacc, a4, hfacts ▸ a5⟩

/-- **An event fired from a state is fired from its image** (the Inkling pilot's `fired_old`, for
any map that keeps the program counter, facts, sub-step, accumulator and invariant): the per-site
facts of the flat machine (its shape lemmas) apply to a regrouped machine's states. -/
theorem Code.fired_map {C C' : Code K A L g} (φ : C'.D → C.D) {d : C'.D} {e : Event}
    {o : Option TState}
    (hpc : C'.pc d = C.pc (φ d)) (hfacts : C'.facts d = C.facts (φ d))
    (hsub : C'.sub d = C.sub (φ d)) (hacc : C'.acc d = C.acc (φ d))
    (hinv : C'.inv d → C.inv (φ d)) (h : C'.toMachine.Fired (some d) e o) :
    C.toMachine.Fired (some (φ d)) e o := by
  obtain ⟨t, ⟨hat, hi⟩, hf⟩ := h
  refine ⟨t, ⟨Code.atD_map φ hpc hfacts hsub hacc hat, hinv hi⟩, ?_⟩
  simpa only [Code.toMachine, Code.tmpl, hpc] using hf

end
end PTX.Flow
