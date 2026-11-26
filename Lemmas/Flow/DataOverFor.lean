-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataOverStrict
public import Lemmas.Flow.ReachFrame

@[expose] public section

/-! # The strict step of a value state from the control machine's and a strict data step

`Over.stepFor` is `Over.stepAtU` for the exact obligation: a value state obeys `Code.StepFor` from
the control machine's exact step (`Code.StepAt`) at the erased state and a **strict data step**
(`DataStepS`): after a followed event, every state that local steps reach and that performs an
event holds the successor's data facts (no dead alternative). `ReachS` is `Reach` without it: the
combinators `SegD.reachS`, `SegD.reachS_then`, `reachS_frameSet` carry the conditions of the runs
as hypotheses. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- From facts `F` at `p`: the first state that performs an event holds `G`. -/
def ReachS (K : Kernel) (A : List Assumption) (L : Launch) (g p : Nat)
    (F G : List (Nat × Value)) : Prop :=
  ∀ u, At u p F → ∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' →
    Holds t'.regs G

theorem ReachS.weaken_start {p : Nat} {F F' G : List (Nat × Value)} (h : ReachS K A L g p F G)
    (hF : ∀ R, Holds R F' → Holds R F) : ReachS K A L g p F' G :=
  fun u hu => h u (At.mono hu (hF _ hu.2.2.2.2))

/-- A strict `Reach` from a `Reach` at states that are not dead. -/
theorem ReachS.of_reach {p : Nat} {F G : List (Nat × Value)} (h : Reach K A L g p F G)
    (hn : ∀ u, At u p F → ¬ Machine.Dead (K := K) (A := A) (L := L) (g := g) u) :
    ReachS K A L g p F G := by
  intro u hu
  rcases h u hu with h1 | hd
  · exact h1
  · exact absurd hd (hn u hu)

/-- **Control code keeps the facts it does not write**, strictly. -/
theorem reachS_frameSet (hA : RulesFrame A) {S : List Nat} {H F : List (Nat × Value)} {p : Nat}
    (hB : frameSetB K S (H.map Prod.fst) = true) (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc)
    (hp : (S.contains p || evAtB K p) = true) (hF : ∀ R, Holds R F → Holds R H) :
    ReachS K A L g p F H := by
  intro u hu
  obtain ⟨hup, -, -, -, huF⟩ := hu
  exact fun t' hr _ => (rtg_frameSet hA hB hS (hup ▸ hp) (hF _ huF) hr).2

/-- **A run under its condition, then a strict `Reach`.** -/
theorem SegD.reachS_then {n s q : Nat} {F G H : List (Nat × Value)} {C : Prop}
    (h : SegD K A L g n s F q G C) (hC : C) (hR : ReachS K A L g q G H) :
    ReachS K A L g s F H := by
  intro u hu t' hr hs
  obtain ⟨t2, hrun, ht2⟩ := (h u hu).1 hC
  refine hR t2 ht2 t' ?_ hs
  rcases rtg_tau_total (run_rtg hrun) hr with h' | h'
  · exact h'
  · rcases Relation.ReflTransGen.cases_head h' with e | ⟨c, hc, -⟩
    · exact e ▸ .refl
    · exact absurd hc (not_tau_of_stops hs)

/-- **A run under its condition to an event instruction.** -/
theorem SegD.reachS {n s b : Nat} {F G G' : List (Nat × Value)} {C : Prop} {ins : Instr}
    (h : SegD K A L g n s F b G C) (hC : C) (hc : K.code[b]? = some ins)
    (hg : GuardTrue G ins.guard) (hl : ins.op.isLocal = false)
    (hG : C → ∀ R, Holds R G → Holds R G') : ReachS K A L g s F G' := by
  intro u hu
  obtain ⟨t2, hr, ht2⟩ := (h u hu).1 hC
  exact DataStep.of_run (run_rtg hr) (stops_of_at ht2 hc hg hl) (hG hC _ ht2.2.2.2.2)

/-- The data step of a value state, strictly. -/
def DataStepS (C' : Code K A L g) (dF : C'.D → List (Nat × Value)) (d : C'.D) : Prop :=
  ∀ {t e u d'} ins, C'.AtD d t → C'.inv d → K.code[C'.pc d]? = some ins →
    Fires (C'.pc d) (eventTmpl A L g t ins.op) e (some u) → C'.next d e = some (some d') →
    ∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' → Holds t'.regs (dF d')

/-- **A value state takes the strict step** from the control machine's exact step and a strict
data step. -/
theorem Over.stepFor {C' C : Code K A L g} {er : C'.D → C.D} {dF : C'.D → List (Nat × Value)}
    (hO : Over C' C er dF) (hSite : ∀ c, C.inv c → ∃ ins, K.code[C.pc c]? = some ins ∧
      ins.op.isLocal = false ∧ GuardTrue (C.facts c) ins.guard)
    {d : C'.D} (hS : C.inv (er d) → C.StepAt (er d))
    (hD : DataStepS C' dF d) (e : Event) : C'.StepFor d e := by
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
