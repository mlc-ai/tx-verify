-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.NoUbStrictQPRunLane

@[expose] public section

/-! # The state and the stop state of a lane at the end of a strict window

`Frame.noUb_strictQPRun_lane` proves that the window's last event is no undefined behaviour. Here
the window's last event is any event: the lane's state before it is `Ok`, and the stop state at
which the event fires has the machine's facts and the window's invariant. -/

namespace PTX.Frame

open PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : ∀ g, Code K A L g} {X : Execution}

/-- **The strict window ends in a state and a stop state with the invariant.** -/
theorem strictQPRun_at (hC : ∀ g < L.threads, (C g).SoundU)
    (hX : Consistent L K A mem0 X) {g : Nat} {Q P : TState → Prop} {Wf : Event → Prop}
    {Ok : (C g).D → Prop} (hP : ∀ t, LaneAt K A L X g t → P t)
    (hS : ∀ d e, Ok d → (C g).StepForQP Q P Wf d e)
    (hOk : ∀ d e d', Ok d → Wf e → e.pc = (C g).pc d → (C g).next d e = some (some d') →
      Ok d')
    {k0 n : Nat} {dk0 dn : (C g).D} (h0 : stateAt C X g k0 = some (some dk0)) (hOk0 : Ok dk0)
    (hQ0 : ∀ t t1, LanePos K A L X g t ((X.tr g).drop k0) →
      Relation.ReflTransGen (Tau K A L g) t t1 → (C g).Good (some dk0) t1 → Q t1)
    (hn : k0 < n) (hdn : stateAt C X g n = some (some dn)) {e : Event}
    (he : X.get (g, n) = some e)
    (hW : ∀ j, k0 ≤ j → j < n → ∀ ej, X.get (g, j) = some ej → Wf ej) :
    Ok dn ∧ ∃ t0 t1 o', Run K A L g {} ((X.tr g).take n) (some t0) ∧
      Relation.ReflTransGen (Tau K A L g) t0 t1 ∧ (C g).Good (some dn) t1 ∧ Q t1 ∧
      EStep K A L g t1 e o' := by
  have hg := lt_of_get hX he
  obtain ⟨o, hr⟩ := hX.thr g hg
  obtain ⟨n', rfl⟩ : ∃ n', n = k0 + (n' + 1) := ⟨n - k0 - 1, by omega⟩
  have hd := stateAt_window h0 hdn
  have hW' : ∀ ej ∈ ((X.tr g).drop k0).take (n' + 1), Wf ej := by
    intro ej hej
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hej
    rw [List.getElem?_take] at hj
    split_ifs at hj with hjn
    rw [List.getElem?_drop] at hj
    exact hW (k0 + j) (by omega) (by omega) _ hj
  exact Code.strictQPRun_windowPc (hC g hg) hS hOk (lanePos_step hP) hr
    ⟨0, {}, by simpa using Run.nil _, by simp, .refl⟩ (Code.reach_init (hC g hg))
    (by unfold stateAt at h0; exact h0) hOk0 hQ0 hW' hd he

end PTX.Frame
