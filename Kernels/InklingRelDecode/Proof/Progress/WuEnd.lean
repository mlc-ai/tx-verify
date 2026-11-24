-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtAll
public import Kernels.InklingRelDecode.Proof.Interface.LedgerFacts

@[expose] public section

/-!
# The state a thread is at now, in an execution without undefined behaviour

`Sched.threadTime` of a thread is the time of its machine's state at the end of its trace, or one
above the time of the state before its last event when its machine stopped there. A thread with no
exit event is pending, so (`end_cases`) either its machine is at a state with its invariant, or it
stopped at its last event, fired from a state with its invariant. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Where a thread without an exit is now**: at a state with its invariant, or stopped at its
last event (fired from a state with its invariant). -/
theorem end_cases (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hub : ¬ HasUb X) {g : Nat} (hg : g < L.threads)
    (hnx : ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) :
    (∃ d, St Q L X g (X.tr g).length = some (some d) ∧ (threadCode L g Q).inv d) ∨
    (∃ d e, 0 < (X.tr g).length ∧ St Q L X g ((X.tr g).length - 1) = some (some d) ∧
      St Q L X g (X.tr g).length = none ∧ (threadCode L g Q).inv d ∧
      X.get (g, (X.tr g).length - 1) = some e) := by
  have hp := pending_of_noExit hX hg hnx
  cases hσ : St Q L X g (X.tr g).length with
  | none =>
    have hσ' : Frame.stateAt (code L Q) X g (X.tr g).length = none := hσ
    obtain ⟨i, d, hi, h1, h2⟩ := Frame.first_stop htr hg hσ'
    have hie : i + 1 = (X.tr g).length := by
      by_contra hne
      have hlt : i + 1 < (X.tr g).length := by omega
      obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i + 1]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
      rcases Frame.fired hS hX (show X.get (g, i + 1) = some e from he) with
        ⟨σ, o, hs, -⟩ | ⟨-, pc, f, rfl⟩
      · rw [h2] at hs
        cases hs
      · exact hub ⟨(g, i + 1), pc, f, he⟩
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hi' : (X.tr g).length - 1 = i := by omega
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX
      (show X.get (g, i) = some e from he) h1
    refine .inr ⟨d, e, by omega, by rw [hi']; exact h1, rfl, hinv, by rw [hi']; exact he⟩
  | some o =>
    cases o with
    | none => exact absurd hσ (htr g _ hg)
    | some d =>
      refine .inl ⟨d, rfl, ?_⟩
      obtain ⟨t, hr⟩ := Frame.run_some hX hub hp
      have hσ' : Frame.stateAt (code L Q) X g (X.tr g).length = some (some d) := hσ
      obtain ⟨-, -, -, -, hinv, -⟩ := Frame.end_at hS hg hr hσ'
      exact hinv

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
