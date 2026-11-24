-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.ValuesByOrder
import Lemmas.Order.OrderBaseCausality
import Lemmas.Order.WaitOrderEnables
import Lemmas.Protocol.StagingHandoff

@[expose] public section

/-! # Tracking induction on actual causal predecessors -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

/-- An actual event dismisses the machine when it changes a followed state to some none. -/
def Dismisses (P : Params) (L : Launch) (X : Execution) (i : EvId) : Prop :=
  ∃ d e, X.get i = some e ∧ Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some d) ∧
    Machine.next P L i.1 d e = some none

theorem tracked_not_dismisses {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (ht : Frame.Tracked (Machine.code P L) X) (w : EvId) : ¬ Dismisses P L X w := by
  obtain ⟨g, j⟩ := w
  rintro ⟨d, e, he, hd, hn⟩
  have hz := Frame.stateAt_succ (C := Machine.code P L) he
  rw [hd] at hz
  exact ht g (j + 1) (Frame.lt_of_get hX he) (hz.trans hn)

theorem prior_dismissal {P : Params} {L : Launch} {X : Execution} {g i : Nat}
    (hi : i ≤ (X.tr g).length) (hd : Frame.stateAt (Machine.code P L) X g i = some none) :
    ∃ j < i, Dismisses P L X (g, j) := by
  induction i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ i ih =>
    have hi' : i < (X.tr g).length := by omega
    let e := (X.tr g)[i]
    have he : X.get (g, i) = some e := List.getElem?_eq_getElem hi'
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd] at hn
    cases hst : Frame.stateAt (Machine.code P L) X g i with
    | none => rw [hst] at hn; cases hn
    | some st =>
      cases st with
      | none =>
        obtain ⟨j, hj, hDismiss⟩ := ih hi'.le hst
        exact ⟨j, by omega, hDismiss⟩
      | some d =>
        rw [hst] at hn
        exact ⟨i, Nat.lt_succ_self i, d, e, he, hst, hn.symm⟩

/-- For a causal predecessor that has no ordinary memory footprint, every earlier event of its
thread is also a causal predecessor. Thus no earlier dismissal suffices at this endpoint. -/
theorem state_at_nonaccess_predecessor {P : Params} {L : Launch} {X : Execution}
    {g j : Nat} {target : EvId} {e : Event}
    (hBefore : baseCausality L X (g, j) target)
    (he : X.get (g, j) = some e) (hAcc : e.acc = none)
    (hPrior : ∀ w, baseCausality L X w target → ¬ Dismisses P L X w) :
    Frame.stateAt (Machine.code P L) X g j ≠ some none := by
  intro hBad
  obtain ⟨i, hi, hDismiss⟩ := prior_dismissal (PTX.len_of_get he).le hBad
  have hNone : (X.get (g, j)).bind Event.acc = none := by
    rw [he, Option.bind_some, hAcc]
  have hp : baseCausality L X (g, i) (g, j) :=
    .single (.inl (po_of_not_access rfl hi (PTX.len_of_get he) hNone))
  exact hPrior (g, i) (hp.trans hBefore) hDismiss

/-- A nonempty predicate of present events has a causal-minimal witness. -/
theorem causal_minimal_event {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (p : EvId → Prop)
    (hHasGet : ∀ e, p e → ∃ ev, X.get e = some ev) (hEx : ∃ e, p e) :
    ∃ i, p i ∧ ∀ j, baseCausality L X j i → ¬ p j :=
  Frame.causal_minimal hX p hHasGet hEx

/-- Global tracking follows if each actual step preserves tracking when no causally prior
actual event has dismissed. Source classification can therefore use proved causal predecessors
without requiring a global tracking premise. -/
theorem tracked_of_causal_steps {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hNext : ∀ g i d e, X.get (g, i) = some e →
      Frame.stateAt (Machine.code P L) X g i = some (some d) →
      (∀ w, baseCausality L X w (g, i) → ¬ Dismisses P L X w) →
      Machine.next P L g d e ≠ some none) :
    Frame.Tracked (Machine.code P L) X := by
  have claim := Frame.values_by_order hX (fun i => ¬ Dismisses P L X i)
    fun i _ _ ih ⟨d, e, he, hd, hn⟩ => hNext i.1 i.2 d e he hd
      (fun w hw hDis => by
        obtain ⟨_, ew, hGet, -⟩ := id hDis
        exact ih w ew hGet hw hDis) hn
  apply Frame.tracked_of
  intro g i d e _ he hd hn
  exact claim (g, i) e he ⟨d, e, he, hd, hn⟩

/-- The release observed by the current event's acquire belongs to a followed thread prefix
when every causal predecessor is protected from dismissal. -/
theorem observed_release_predecessor {P : Params} {L : Launch} {X : Execution}
    {g i q h j : Nat} {e : Event} {m : Loc} {rs as : MbarScope}
    (he : X.get (g, i) = some e) (hq : q < i)
    (hRelease : MbarRelease X (h, j) m rs)
    (hObserved : AsyncCopy.WaitObserves X (.thread (h, j)) (g, q) m true as)
    (hScopes : ScopesMeet L rs h as g)
    (hPrior : ∀ w, baseCausality L X w (g, i) → ¬ Dismisses P L X w) :
    Frame.stateAt (Machine.code P L) X h j ≠ some none := by
  have hBefore := Staging.baseCausality_of_handoff hRelease hObserved hScopes
    (e := (h, j)) (f := (g, i)) ⟨rfl, le_rfl⟩ ⟨rfl, hq, PTX.len_of_get he⟩
  obtain ⟨tx, count, tag, hGet⟩ := hRelease
  exact state_at_nonaccess_predecessor hBefore hGet rfl hPrior

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
