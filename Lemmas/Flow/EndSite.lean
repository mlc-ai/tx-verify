-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code
public import Lemmas.Flow.Determinism

@[expose] public section

/-! # Where a run of a code machine ends

A proof tool. After a run from the initial thread state that has not ended, local steps reach a
concrete state of the abstract state the machine is in (`Code.end_site`): the thread is at that
state's site, ready to perform its event. -/

namespace PTX.Flow

open PTX.Proof

namespace Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A stopped machine stays stopped. -/
theorem after_none (es : List Event) : C.toMachine.after none es = some none := by
  induction es with
  | nil => rfl
  | cons e es ih => exact ih

theorem end_site_from (hC : C.Sound) {es : List Event} {t u : TState} {d : C.D}
    (hg : ∃ t', Relation.ReflTransGen (Tau K A L g) t t' ∧ C.Good (some d) t')
    (hr : Run K A L g t es (some u)) {d' : C.D}
    (ha : C.toMachine.after (some d) es = some (some d')) :
    ∃ t', Relation.ReflTransGen (Tau K A L g) u t' ∧ C.Good (some d') t' := by
  generalize ho : some u = o at hr
  induction hr generalizing d with
  | nil t =>
    cases ho
    simp only [Machine.after] at ha
    cases ha
    exact hg
  | step hl he hrest ih =>
    obtain ⟨t', ht', hgood⟩ := hg
    have hs' : Stops K A L g t' := by
      obtain ⟨m, hm⟩ := (show ∃ m, out K A L g t' = .ev m from ⟨_, out_eq_of hC hgood⟩)
      exact ⟨m, hm⟩
    have heq := stop_unique hl ht' (stops_of_estep he) hs'
    subst heq
    have hat := hgood.1
    have hinv := hgood.2
    obtain ⟨m, hm, hf⟩ := he
    rw [out_eq_of hC hgood] at hm
    cases hm
    obtain ⟨ins, hc, -, -⟩ := (hC.steps d).site hinv
    change Fires _ (C.tmpl (some d) _) _ _ at hf
    simp only [tmpl, hc, hat.1] at hf
    rcases (hC.steps d).step ins hat hinv hc hf with (hn | ⟨d'', t'', hn, hl', hg'⟩) | ⟨hn, -⟩
    · change (C.next d _).bind (fun σ' => C.toMachine.after σ' _) = _ at ha
      rw [hn] at ha
      change C.toMachine.after none _ = _ at ha
      rw [after_none] at ha
      cases ha
    · refine ih ⟨t'', hl', hg'⟩ ?_ ho
      change (C.next d _).bind (fun σ' => C.toMachine.after σ' _) = _ at ha
      rw [hn] at ha
      exact ha
    · change (C.next d _).bind (fun σ' => C.toMachine.after σ' _) = _ at ha
      rw [hn] at ha
      cases ha
  | last => cases ho

/-- After a run from the initial thread state ending in abstract state `d`, local steps reach a
concrete state of `d`. -/
theorem end_site (hC : C.Sound) {es : List Event} {u : TState} {d : C.D}
    (hr : Run K A L g {} es (some u)) (ha : C.toMachine.after (some C.init) es = some (some d)) :
    ∃ t', Relation.ReflTransGen (Tau K A L g) u t' ∧ C.Good (some d) t' := by
  obtain ⟨t, hl, hat, hinv⟩ := hC.start
  exact end_site_from hC ⟨t, hl, hat, hinv⟩ hr ha

end Code

end PTX.Flow
