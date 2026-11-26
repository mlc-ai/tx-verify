-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataOverFor

@[expose] public section

/-! # The strict data step for one event

`DataStepE C' dF d e` is `DataStepS` for the event `e` only: a load's data step holds for an event
whose bytes rebuild, not for any payload (`EvRdOk`, `EvNcOk`). `Over.stepForE` is `Over.stepFor`
with it. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- An event that, when it reads (`rd`), reads bytes that rebuild to a value. -/
def EvRdOk (e : Event) : Prop := ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v

/-- An event that, when it is an `nc` read, reads bytes that rebuild to a value. -/
def EvNcOk (e : Event) : Prop := ∀ x bs, e.kind = .nc x bs → ∃ v, rebuild 3 bs = .ok v

/-- The data step of a value state for the event `e`, strictly. -/
def DataStepE (C' : Code K A L g) (dF : C'.D → List (Nat × Value)) (d : C'.D) (e : Event) :
    Prop :=
  ∀ {t u d'} ins, C'.AtD d t → C'.inv d → K.code[C'.pc d]? = some ins →
    Fires (C'.pc d) (eventTmpl A L g t ins.op) e (some u) → C'.next d e = some (some d') →
    ∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' → Holds t'.regs (dF d')

theorem DataStepE.of_all {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    (h : DataStepS C' dF d) (e : Event) : DataStepE C' dF d e :=
  fun ins hat hi hc hf hn => h ins hat hi hc hf hn

/-- **A value state takes the strict step for one event** from the control machine's exact step
and a strict data step for it. -/
theorem Over.stepForE {C' C : Code K A L g} {er : C'.D → C.D} {dF : C'.D → List (Nat × Value)}
    (hO : Over C' C er dF) (hSite : ∀ c, C.inv c → ∃ ins, K.code[C.pc c]? = some ins ∧
      ins.op.isLocal = false ∧ GuardTrue (C.facts c) ins.guard)
    {d : C'.D} (hS : C.inv (er d) → C.StepAt (er d))
    (e : Event) (hD : DataStepE C' dF d e) : C'.StepFor d e := by
  intro t u ins hat hi hc hf
  have hF := hat.2.2.2.2
  rw [hO.facts, holds_append] at hF
  have htc : C.AtD (er d) t :=
    ⟨hat.1.trans (hO.pc d), hat.2.1.trans (hO.sub d), hat.2.2.1.trans (hO.acc d), hat.2.2.2.1,
      hF.1⟩
  have hic := (hO.inv d).mp hi
  have hc' := hc
  have hf' := hf
  rw [hO.pc] at hc hf
  rcases (hS hic).step ins htc hic hc hf with (hy | ⟨c', t', hy, hl, hg⟩) | ⟨hy, hd⟩
  · rcases hn : C'.next d e with _ | _ | d'
    · rw [hO.stop hn] at hy; cases hy
    · exact .inl (.inl rfl)
    · rw [hO.next hn] at hy; cases hy
  · rcases hn : C'.next d e with _ | _ | d'
    · rw [hO.stop hn] at hy; cases hy
    · exact .inl (.inl rfl)
    · have hx := hO.next hn
      rw [hx] at hy
      obtain rfl := Option.some.inj (Option.some.inj hy)
      refine .inl (.inr ⟨d', t', rfl, hl, ?_⟩)
      obtain ⟨hat', hinv'⟩ := hg
      refine ⟨⟨hat'.1.trans (hO.pc d').symm, hat'.2.1.trans (hO.sub d').symm,
        hat'.2.2.1.trans (hO.acc d').symm, hat'.2.2.2.1, ?_⟩, (hO.inv d').mpr hinv'⟩
      rw [hO.facts, holds_append]
      obtain ⟨ins', hc2, hl2, hg2⟩ := hSite (er d') hinv'
      exact ⟨hat'.2.2.2.2, hD ins hat hi hc' hf' hn t' hl
        ⟨_, out_event hat'.2.2.2.1 (hat'.1.symm ▸ hc2) (guardHolds_of hat'.2.2.2.2 hg2) hl2⟩⟩
  · rcases hn : C'.next d e with _ | _ | d'
    · exact .inr ⟨rfl, hd⟩
    · exact .inl (.inl rfl)
    · rw [hO.next hn] at hy; cases hy

end
end PTX.Flow.Code
