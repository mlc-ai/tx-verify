-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc

@[expose] public section

/-! # Where the machines stop (fields `ub_stop`, `stop_cause` of `TcFacts`)

* **Undefined behaviour.** An undefined-behaviour event fires only from an undefined-behaviour
  template (`fires_ub`), so when no site of a thread's machine has one (`Code.TmplOk`), every such
  event comes after the machine stopped (`Code.ub_stopped`). `TcFacts_ub_stop` takes that fact of
  each role's sites as its premise (`SitesTmplOk`).
* **Stops.** In a followed execution (`Frame.Tracked`) the state after an event is never
  `some none`; it is `none` only when the role's successor function rejects the event at a
  followed state. `TcFacts_stop_cause` reduces the field to that fact of each role's successor
  function (`NextStopsAtExitOrBadRead`): every event the machine rejects is the thread's exit or
  comes after a read the machine does not follow.

Both premises are per-site facts of the role machines (one per role package); they are
stated here as the functions' facts and listed in the assembly. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- No site of any thread's machine has an undefined-behaviour template (per role: the
prologue's, the loader's, the MMA warp's, the store warp's, the softmax and correction warps'
and the idle warp's sites). -/
def SitesTmplOk (L : Launch) : Prop := ∀ g < L.threads, (code L g).TmplOk

/-- **Undefined behaviour fires only after the thread's machine stopped.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.TcFacts_ub_stop (hpre : Pre P L mem0)
    (hX : Consistent L kernel asms mem0 X) (_ht : Frame.Tracked (code L) X)
    (hok : SitesTmplOk L) :
    ∀ {g k pc : Nat} {f : Fault}, g < L.threads → X.get (g, k) = some ⟨pc, .ub f⟩ →
      St L X g k = none ∨ St L X g k = some none := by
  intro g k pc f hg he
  obtain ⟨o, hr⟩ := hX.thr g hg
  exact Code.ub_stopped (sound hpre hg) (hok g hg) ⟨o, hr⟩ he

/-- The role machines' successor functions reject an event at a followed state only when it is
the thread's exit or comes after a read the machine does not follow. -/
def NextStopsAtExitOrBadRead (L : Launch) (X : Execution) : Prop :=
  ∀ {g i : Nat} {d : ThreadD} {e : Event}, g < L.threads → St L X g i = some (some d) →
    X.get (g, i) = some e → (code L g).next d e = none →
      (∃ pc, e = ⟨pc, .exit⟩) ∨ ∃ j ≤ i, BadRead L X g j

/-- **A machine stops only at its exit or after a read it does not follow.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.TcFacts_stop_cause (_hpre : Pre P L mem0)
    (_hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X)
    (hnext : NextStopsAtExitOrBadRead L X) :
    ∀ {g i : Nat} {d : ThreadD}, g < L.threads → St L X g i = some (some d) →
      (St L X g (i + 1) = none ∨ St L X g (i + 1) = some none) →
      (∃ pc, X.get (g, i) = some ⟨pc, .exit⟩) ∨ ∃ j ≤ i, BadRead L X g j := by
  intro g i d hg hσ hst
  rcases hst with hst | hst
  · cases he : (X.tr g)[i]? with
    | none =>
      have hle : (X.tr g).length ≤ i := by
        by_contra h
        rw [List.getElem?_eq_getElem (by omega)] at he
        cases he
      have h1 : St L X g (i + 1) = St L X g i := by
        unfold St
        rw [Frame.stateAt_of_le (by omega), Frame.stateAt_of_le hle]
      rw [h1, hσ] at hst
      cases hst
    | some e =>
      have hσ' : Frame.stateAt (code L) X g i = some (some d) := hσ
      have h1 : St L X g (i + 1) = (code L g).next d e := by
        unfold St
        rw [Frame.stateAt_succ he, hσ']
        rfl
      rcases hnext hg hσ he (h1 ▸ hst) with ⟨pc, rfl⟩ | hb
      · exact .inl ⟨pc, he⟩
      · exact .inr hb
  · exact absurd hst (ht g (i + 1) hg)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
