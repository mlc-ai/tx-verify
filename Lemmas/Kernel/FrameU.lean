-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.EndSiteU
public import Lemmas.Kernel.Followed

@[expose] public section

namespace PTX.Frame

open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Code K A L g} {g k : Nat}
  (hC : ∀ g < L.threads, (C g).SoundU) (hX : Consistent L K A mem0 X)

include hC hX

theorem traceU (hg : g < L.threads) : (C g).toMachineU.Trace (some (C g).init) (X.tr g) :=
  (hC g hg).machine.produces (hX.thr g hg)

theorem firedU {e : Event} (he : X.get (g, k) = some e) :
    (∃ σ o, stateAt C X g k = some σ ∧ (C g).toMachineU.Fired σ e o) ∨
      (stateAt C X g k = none ∧ ∃ pc f, e = ⟨pc, .ub f⟩) := by
  have h := (traceU hC hX (lt_of_get hX he)).fired he
  rw [Code.after_eqU] at h
  exact h

omit hX in
theorem fired_site_ofU {d : (C g).D} {e : Event} {o : Option TState} (hg : g < L.threads)
    (hf : (C g).toMachineU.Fired (some d) e o) (hu : ∀ f, e.kind ≠ .ub f) :
    ∃ t ins, (C g).AtD d t ∧ (C g).inv d ∧ K.code[(C g).pc d]? = some ins ∧
      Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o :=
  Code.fired_siteU (hC g hg) hf hu

theorem fired_siteU {d : (C g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : stateAt C X g k = some (some d)) (hu : ∀ f, e.kind ≠ .ub f) :
    ∃ t ins o, (C g).AtD d t ∧ (C g).inv d ∧ K.code[(C g).pc d]? = some ins ∧
      Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o := by
  rcases firedU hC hX he with ⟨σ, o, hs, hf⟩ | ⟨hs, _⟩
  · rw [hσ] at hs
    cases hs
    obtain ⟨t, ins, h⟩ := fired_site_ofU hC (lt_of_get hX he) hf hu
    exact ⟨t, ins, o, h⟩
  · rw [hσ] at hs
    cases hs

theorem event_pcU {d : (C g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : stateAt C X g k = some (some d)) (hu : ∀ f, e.kind ≠ .ub f) : e.pc = (C g).pc d := by
  obtain ⟨_, _, _, _, _, _, hf⟩ := fired_siteU hC hX he hσ hu
  exact EventFrame.fires_source_pc hf

omit hX in
theorem end_atU (hg : g < L.threads) {t : TState} (hr : Run K A L g {} (X.tr g) (some t))
    {d : (C g).D} (hσ : stateAt C X g (X.tr g).length = some (some d)) :
    (∃ s ins, Relation.ReflTransGen (Tau K A L g) t s ∧ (C g).AtD d s ∧ (C g).inv d ∧
      K.code[(C g).pc d]? = some ins ∧ out K A L g s = .ev (eventTmpl A L g s ins.op)) ∨
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  rw [stateAt_end] at hσ
  obtain ⟨s, hl, hs | ⟨f, hf⟩⟩ := Code.end_siteU (hC g hg) hr hσ
  · obtain ⟨ins, hc, ho⟩ := Code.site_outU ((hC g hg).steps d) hs
    exact .inl ⟨s, ins, hl, hs.1, hs.2, hc, ho⟩
  · exact .inr ⟨s, f, hl, hf⟩

theorem good_stateU {J : ∀ g, (C g).D → Prop} {e : Event}
    (he : X.get (g, k) = some e) (hu : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : FollowedAt C J X g k) : ∃ d, stateAt C X g k = some (some d) ∧ J g d := by
  rcases firedU hC hX he with ⟨σ, _, hs, _⟩ | ⟨_, pc, f, rfl⟩
  · cases σ with
    | none => exact absurd hs hG.1
    | some d => exact ⟨d, hs, hG.2 d hs⟩
  · exact absurd rfl (hu pc f)

end PTX.Frame
