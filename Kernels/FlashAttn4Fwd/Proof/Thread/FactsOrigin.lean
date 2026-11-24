-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Origin
public import Lemmas.Flow.Final
public import Lemmas.Flow.UbStop

@[expose] public section

/-! # The origin of a continuing event

`event_origin` gives the state an event fires from, with an unknown successor. An event that
neither ends the thread (`Ends`: an exit or undefined behaviour) nor is the thread's last fires
with a successor state (`event_cont`, `prior_cont`), which is what the roles' site lemmas
(`Softmax.site_event`, `Correction.site_event`) take to name the event of a site (`Ev`). The
role of a state follows from the thread's warp (`role_of_warp`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An event that does not end its thread fires from its state and continues.** -/
theorem event_cont (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {J : Nat → ThreadD → List Event → Prop}
    (hJ : ∀ g < L.threads, RunInv L g (J g)) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hend : ¬ Ends e) :
    ∃ d t ins u, Frame.stateAt (code L) X g k = some (some d) ∧ J g d ((X.tr g).take k) ∧
      (code L g).AtD d t ∧ (code L g).inv d ∧ kernel.code[(code L g).pc d]? = some ins ∧
      Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e (some u) := by
  obtain ⟨d, t, ins, o, hσ, hJ', hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht hJ he (fun pc f h => hend (.inl ⟨f, by rw [h]⟩))
  cases o with
  | none => exact absurd (fires_none_ends hf) hend
  | some u => exact ⟨d, t, ins, u, hσ, hJ', hat, hi, hc, hf⟩

/-- **An event followed by another fires from its state and continues.** -/
theorem prior_cont (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {J : Nat → ThreadD → List Event → Prop}
    (hJ : ∀ g < L.threads, RunInv L g (J g)) {g j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hl : j + 1 < (X.tr g).length) :
    ∃ d t ins u, Frame.stateAt (code L) X g j = some (some d) ∧ J g d ((X.tr g).take j) ∧
      (code L g).AtD d t ∧ (code L g).inv d ∧ kernel.code[(code L g).pc d]? = some ins ∧
      Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e (some u) := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have hg := Frame.lt_of_get hX he
  obtain ⟨τ, u, ha, hf⟩ := (Frame.trace (C := code L) hC hX hg).fired_some he hl
  cases τ with
  | none => exact absurd ha (ht g j hg)
  | some d =>
    obtain ⟨t, ins, hat, hi, hc, hfi⟩ := Frame.fired_site_of (C := code L) hC hg hf
    exact ⟨d, t, ins, u, ha, RunInv.holds hpre hX hg (hJ g hg) (by omega) ha, hat, hi, hc, hfi⟩

/-- An event before a later event of its thread does not end the thread. -/
theorem not_ends_of_lt {g j k : Nat} {e e' : Event} (hX : Consistent L kernel asms mem0 X)
    (he : X.get (g, j) = some e) (he' : X.get (g, k) = some e') (hjk : j < k) : ¬ Ends e := by
  intro hend
  have hg := Frame.lt_of_get hX he
  obtain ⟨o, hr⟩ := hX.thr g hg
  have h1 := Run.end_last hr he hend
  have h2 : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he').1
  omega

/-- A thread's role state is the role of its warp. -/
theorem role_of_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) {g k : Nat}
    {r : Role} (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr r))) : r.kind.Warp (warpOf L g) :=
  role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg) k r hσ

/-- The run invariant that holds everywhere. -/
theorem trueJ_run (L : Launch) (g : Nat) : RunInv L g (fun _ _ => True) where
  init := trivial
  step := fun _ _ _ _ _ _ => trivial

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
