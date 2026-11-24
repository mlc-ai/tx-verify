-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code

@[expose] public section

namespace PTX.Flow.Code

open PTX.Proof
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} (C : Code K A L g)

/-- A followed control state can also describe the final UB of the concrete thread. -/
def GoodU : Option C.D → TState → Prop
  | none, t => Stops K A L g t
  | some d, t => C.Good (some d) t ∨ ∃ f, out K A L g t = .ev (.ub f)

def toMachineU : Machine K A L g :=
  { C.toMachine with Good := C.GoodU, tmpl := fun _ t => C.tmpl none t }

/-- The concrete successor reaches its predicted site or fires UB during the crossing. -/
structure StepAtU (d : C.D) : Prop where
  site : C.inv d → ∃ ins, K.code[C.pc d]? = some ins ∧ ins.op.isLocal = false ∧
    GuardTrue (C.facts d) ins.guard
  step : ∀ {t e u} ins, C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
    Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) →
    (C.next d e = some none ∨
      ∃ d' t', C.next d e = some (some d') ∧ Relation.ReflTransGen (Tau K A L g) u t' ∧
        C.GoodU (some d') t') ∨
    (C.next d e = none ∧ Machine.Dead (K := K) (A := A) (L := L) (g := g) u)

structure SoundU : Prop where
  start : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ C.AtD C.init t ∧ C.inv C.init
  steps : ∀ d, C.StepAtU d

variable {C}

theorem StepAt.toStepAtU {d : C.D} (h : C.StepAt d) : C.StepAtU d where
  site := h.site
  step := by
    intro t e u ins ht hi hc hf
    rcases h.step ins ht hi hc hf with (hn | ⟨d', s, hn, hl, hs⟩) | hd
    · exact .inl (.inl hn)
    · exact .inl (.inr ⟨d', s, hn, hl, .inl hs⟩)
    · exact .inr hd

theorem Sound.toSoundU (h : C.Sound) : C.SoundU :=
  ⟨h.start, fun d => (h.steps d).toStepAtU⟩

theorem site_outU {d : C.D} (hs : C.StepAtU d) {t : TState} (h : C.Good (some d) t) :
    ∃ ins, K.code[C.pc d]? = some ins ∧ out K A L g t = .ev (eventTmpl A L g t ins.op) := by
  obtain ⟨ht, hi⟩ := h
  obtain ⟨ins, hc, hl, hg⟩ := hs.site hi
  exact ⟨ins, hc, out_event ht.2.2.2.1 (ht.1.symm ▸ hc) (guardHolds_of ht.2.2.2.2 hg) hl⟩

theorem out_eq_stepsU (hs : ∀ d, C.StepAtU d) {σ : Option C.D} {t : TState}
    (h : C.GoodU σ t) : out K A L g t = .ev (C.toMachineU.tmpl σ t) := by
  have stop : Stops K A L g t := by
    cases σ with
    | none => exact h
    | some d =>
      rcases h with ha | ⟨f, hf⟩
      · obtain ⟨ins, _, ho⟩ := site_outU (hs d) ha
        exact ⟨_, ho⟩
      · exact ⟨_, hf⟩
  obtain ⟨m, hm⟩ := stop
  simp only [toMachineU, tmpl, hm]

theorem SoundU.machine (hC : C.SoundU) : C.toMachineU.Sound where
  start := by
    obtain ⟨s, hl, h⟩ := hC.start
    exact ⟨s, hl, Or.inl h⟩
  out_eq := fun h => out_eq_stepsU hC.steps h
  step := by
    intro σ t e u h hf
    cases σ with
    | none => exact .inl ⟨none, rfl, fun _ _ stop => stop⟩
    | some d =>
      change Fires t.pc (C.tmpl none t) e (some u) at hf
      rcases h with h | ⟨f, ho⟩
      · obtain ⟨ins, hc, ho⟩ := site_outU (hC.steps d) h
        simp only [tmpl, ho, h.1.1] at hf
        rcases (hC.steps d).step ins h.1 h.2 hc hf with (hn | ⟨d', s, hn, hl, hg⟩) | hd
        · exact .inl ⟨none, hn, fun _ _ stop => stop⟩
        · exact .inl ⟨some d', hn, Machine.reach_of (M := C.toMachineU)
            (fun h => out_eq_stepsU hC.steps h) hl hg⟩
        · exact .inr hd
      · simp only [tmpl, ho] at hf
        cases hf.2

end
end PTX.Flow.Code
