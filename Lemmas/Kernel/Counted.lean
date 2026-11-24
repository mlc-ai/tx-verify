-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame
public import Lemmas.Flow.Counted

@[expose] public section

/-! # The ghost counts of a thread's machine along its trace

For machines with a ghost ledger (`Code.counted`), the count of class `c` in the state before a
thread's `k`-th event is the number of the thread's first `k` events of class `c`
(`Frame.count_eq`), and a positive count names an earlier event of its class
(`exists_of_count`). No soundness is needed: a state reached by the machine took every one of
those events. A budget between two counts that the reference invariant states at a site holds
for the thread's events there (`budget_of_counts`). -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {κ : Type}

/-- The counts after a list of events, from counts `n0`. -/
theorem counted_after {C : Code K A L g} {cls : κ → Event → Bool} {d0 : C.D}
    {n0 : κ → Nat} {es : List Event} {dn : (C.counted cls).D}
    (h : (C.counted cls).toMachine.after (some (d0, n0)) es = some (some dn)) (c : κ) :
    dn.2 c = n0 c + es.countP (cls c) := by
  refine (C.counted cls).toMachine.after_induction
    (Q := fun σ es => ∀ dn, σ = some dn → dn.2 c = n0 c + es.countP (cls c))
    (by intro dn h; cases h; simp) ?_ es _ h dn rfl
  intro σ es e σ' ih hn dn' hσ'
  subst hσ'
  cases σ with
  | none => cases hn
  | some dn =>
    obtain ⟨-, h2⟩ := Code.counted_next_some (C := C) (d := dn.1) (n := dn.2) hn
    have := ih dn rfl
    rw [h2, List.countP_append]
    simp only [Code.bump, List.countP_cons, List.countP_nil]
    omega

/-- **A ghost count is the count of the thread's events of its class so far.** -/
theorem count_eq {C : (g : Nat) → Code K A L g} {cls : Nat → κ → Event → Bool} {X : Execution}
    {k : Nat} {dn : ((C g).counted (cls g)).D}
    (h : stateAt (fun g => (C g).counted (cls g)) X g k = some (some dn)) (c : κ) :
    dn.2 c = ((X.tr g).take k).countP (cls g c) := by
  have := counted_after (C := C g) (n0 := fun _ => 0) h c
  simpa using this

/-- An event of a class that a state's ghost counts have counted is an earlier event of the
thread. -/
theorem exists_of_count {C : (g : Nat) → Code K A L g} {cls : Nat → κ → Event → Bool}
    {X : Execution} {k : Nat} {dn : ((C g).counted (cls g)).D}
    (h : stateAt (fun g => (C g).counted (cls g)) X g k = some (some dn)) {c : κ}
    (hc : 0 < dn.2 c) : ∃ j < k, ∃ f, X.get (g, j) = some f ∧ cls g c f = true := by
  rw [count_eq h c] at hc
  obtain ⟨f, hf, hcf⟩ := List.countP_pos_iff.mp hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  rw [List.length_take] at hj
  refine ⟨j, by omega, _, ?_, hcf⟩
  show (X.tr g)[j]? = _
  rw [← List.getElem?_take_of_lt (show j < k by omega)]
  exact List.getElem?_eq_getElem _

/-- **A budget kept by ghost counts holds along the trace**: when every state of a counted
machine from which an event of kind `P` fires has count `c₁` below count `c₂` (a conjunct of the
reference invariant), the thread's events of class `c₁` before such an event are fewer than those
of class `c₂`. -/
theorem budget_of_counts {mem0 : Mem0} {C : (g : Nat) → Code K A L g}
    {cls : Nat → κ → Event → Bool} {X : Execution}
    (hC : ∀ g < L.threads, ((C g).counted (cls g)).Sound) (hX : Consistent L K A mem0 X)
    (ht : Tracked (fun g => (C g).counted (cls g)) X) {P : Event → Prop} {c₁ c₂ : κ}
    (hstate : ∀ g k d e, X.get (g, k) = some e →
      stateAt (fun g => (C g).counted (cls g)) X g k = some (some d) → P e → d.2 c₁ < d.2 c₂)
    {g k : Nat} {e : Event} (he : X.get (g, k) = some e) (hP : P e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ((X.tr g).take k).countP (cls g c₁) < ((X.tr g).take k).countP (cls g c₂) := by
  obtain ⟨d, hd⟩ := event_state hC hX ht he hub
  have h := hstate g k d e he hd hP
  rwa [count_eq hd c₁, count_eq hd c₂] at h

end

end PTX.Frame
