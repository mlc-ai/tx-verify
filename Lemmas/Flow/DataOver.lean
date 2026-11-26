-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Erase
public import Lemmas.Flow.Determinism

@[expose] public section

/-! # A value machine's steps from its control machine's

A proof tool, generic over the kernel. A value machine `C'` lies over a control machine `C`
(`Over C' C er dF`) when its states erase (`er`) to control states with the same pc, sub-step,
accumulator and invariant, its facts are the control facts followed by data facts `dF`, and every
step it follows is a step of `C` (it may stop following, `some none`, anywhere; it is dead only
where `C` is). Then a value state obeys its UB-tolerant obligations (`Over.stepAtU`) from

* the control machine's obligations (all of them: they are proved once, for `C`), and
* a **data step** (`DataStep`): after a followed event, every state that local steps reach and
  that performs an event holds the successor's data facts, or the thread is dead (`DataStep.of_run`:
  from one such state).

The concrete state the data step reaches is the one the control step reaches: both are the first
state after the event that performs an event (`stop_unique`). So a value lane proves no control
segment again: only the data facts along its float runs. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- `C'` lies over `C`: erasure `er`, data facts `dF`. -/
structure Over (C' C : Code K A L g) (er : C'.D → C.D) (dF : C'.D → List (Nat × Value)) :
    Prop where
  pc : ∀ d, C'.pc d = C.pc (er d)
  sub : ∀ d, C'.sub d = C.sub (er d)
  acc : ∀ d, C'.acc d = C.acc (er d)
  inv : ∀ d, C'.inv d ↔ C.inv (er d)
  facts : ∀ d, C'.facts d = C.facts (er d) ++ dF d
  next : ∀ {d e d'}, C'.next d e = some (some d') → C.next (er d) e = some (some (er d'))
  stop : ∀ {d e}, C'.next d e = none → C.next (er d) e = none

/-- A value machine over a control machine erases to it. -/
theorem Over.erases {C' C : Code K A L g} {er : C'.D → C.D} {dF : C'.D → List (Nat × Value)}
    (h : Over C' C er dF) (hi : er C'.init = C.init) : Erases C' C er :=
  ⟨hi, h.next⟩

/-- **The data step of a value state**: after a followed event, the successor's data facts at
the first state that performs an event, or a dead thread. -/
def DataStep (C' : Code K A L g) (dF : C'.D → List (Nat × Value)) (d : C'.D) : Prop :=
  ∀ {t e u d'} ins, C'.AtD d t → C'.inv d → K.code[C'.pc d]? = some ins →
    Fires (C'.pc d) (eventTmpl A L g t ins.op) e (some u) → C'.next d e = some (some d') →
    (∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' → Holds t'.regs (dF d')) ∨
      Machine.Dead (K := K) (A := A) (L := L) (g := g) u

/-- The data facts at one state after the event that performs an event are at every such state:
it is the first (`stop_unique`). -/
theorem DataStep.of_run {u t2 : TState} {F : List (Nat × Value)}
    (h : Relation.ReflTransGen (Tau K A L g) u t2) (hs : Stops K A L g t2) (hF : Holds t2.regs F) :
    ∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' → Holds t'.regs F :=
  fun _ h' hs' => stop_unique h h' hs hs' ▸ hF

/-- **A value state obeys its obligations** from the control machine's and its data step. -/
theorem Over.stepAtU {C' C : Code K A L g} {er : C'.D → C.D} {dF : C'.D → List (Nat × Value)}
    (hO : Over C' C er dF) (hS : ∀ c, C.StepAtU c) {d : C'.D} (hD : DataStep C' dF d) :
    C'.StepAtU d where
  site := by
    intro hi
    obtain ⟨ins, hc, hl, hg⟩ := (hS (er d)).site ((hO.inv d).mp hi)
    refine ⟨ins, by rw [hO.pc]; exact hc, hl, ?_⟩
    rw [hO.facts]
    cases hgd : ins.guard with
    | none => trivial
    | some pn =>
      rw [hgd] at hg
      exact List.mem_append_left _ hg
  step := by
    intro t e u ins ht hi hc hf
    have hF := ht.2.2.2.2
    rw [hO.facts, holds_append] at hF
    have htc : C.AtD (er d) t :=
      ⟨ht.1.trans (hO.pc d), ht.2.1.trans (hO.sub d), ht.2.2.1.trans (hO.acc d), ht.2.2.2.1, hF.1⟩
    have hic := (hO.inv d).mp hi
    rw [hO.pc] at hc hf
    rcases hn : C'.next d e with _ | _ | d'
    · rcases (hS (er d)).step ins htc hic hc hf with (hx | ⟨_, _, hx, -⟩) | ⟨-, hd⟩
      · rw [hO.stop hn] at hx; cases hx
      · rw [hO.stop hn] at hx; cases hx
      · exact .inr ⟨rfl, hd⟩
    · exact .inl (.inl rfl)
    · have hx := hO.next hn
      rcases (hS (er d)).step ins htc hic hc hf with (hy | ⟨c', t', hy, hl, hg⟩) | ⟨hy, -⟩
      · rw [hx] at hy; cases hy
      · rw [hx] at hy
        cases hy
        have hc' : K.code[C'.pc d]? = some ins := by rw [hO.pc]; exact hc
        have hf' : Fires (C'.pc d) (eventTmpl A L g t ins.op) e (some u) := by
          rw [hO.pc]; exact hf
        rcases hD ins ht hi hc' hf' hn with hF2 | ⟨s, f, hs, hub⟩
        · have hs1 : Stops K A L g t' := by
            rcases hg with hg | ⟨f, hf1⟩
            · obtain ⟨_, _, ho⟩ := site_outU (hS _) hg
              exact ⟨_, ho⟩
            · exact ⟨_, hf1⟩
          have hF2 := hF2 t' hl hs1
          refine .inl (.inr ⟨d', t', rfl, hl, ?_⟩)
          rcases hg with ⟨hat, hinv⟩ | hub
          · refine .inl ⟨⟨hat.1.trans (hO.pc d').symm, hat.2.1.trans (hO.sub d').symm,
              hat.2.2.1.trans (hO.acc d').symm, hat.2.2.2.1, ?_⟩, (hO.inv d').mpr hinv⟩
            rw [hO.facts, holds_append]
            exact ⟨hat.2.2.2.2, hF2⟩
          · exact .inr hub
        · exact .inl (.inr ⟨d', s, rfl, hs, .inr ⟨f, hub⟩⟩)
      · rw [hx] at hy; cases hy

end
end PTX.Flow.Code
