-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixPremises
public import Kernels.InklingRelDecode.Proof.Interface.InputRead
public import Kernels.InklingRelDecode.Proof.Interface.IpTmZero

@[expose] public section

/-!
# Tracking up to the base-word stops

The machines follow every Tensor Memory base word the common start loads. They stop
(`some none`) on a word that is not good at two states only (`BaseStop`): the prologue's last
event `bar18` (`ProA.wGood` fails) and the worker's dispatch into the MMA role (`WComp.baseOk`
fails). Both are after the thread's two barrier-0 arrivals; `bar18` is after the prologue's proxy
fence `fnc0` and is the thread's barrier-1 arrival of ordinal 0.

`weakTracked_of` proves, from `hnext` at every other state (`NextRestW`: the states that are
neither `Discharged` nor a base-word stop), that every thread is followed at every event up to its
stop event: a thread whose machine no longer follows it stopped at an earlier `BaseStop` state.
It needs no fact about another thread: the launch bytes of the input reads come from the read-only
input assumption (`launchRead_of_wf`), so the induction runs along one thread's events.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The base-word stops**: the prologue's last event with a base word that is not good, and the
worker's dispatch with an inherited base word that is not good. -/
def BaseStop : TSt → Prop
  | .d (.pro d) => d.site = .bar18 ∧ ProA.wGood d.dt = false
  | .w (.worker w) => w.site = .ldRole ∧ ¬ WComp.baseOk w.P
  | _ => False

/-- `hnext` at every state that is neither `Discharged` nor a base-word stop. -/
def NextRestW (Q : Params) (L : Launch) (mem0 : Mem0) (X : Execution) : Prop :=
  ∀ (g k : Nat) (s : TSt) (e : Event), g < L.threads → (X.tr g)[k]? = some e →
    St Q L X g k = some (some s) → ¬ Discharged s → ¬ BaseStop s →
    (∀ j < k, Good Q L mem0 X (g, j)) → LaunchRead Q mem0 X (g, k) →
    (threadCode L g Q).next s e ≠ some none

/-- **Every thread is followed up to its base-word stop**: where the machine no longer follows a
thread, the thread was at a `BaseStop` state earlier. -/
def WeakTracked (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k, g < L.threads → St Q L X g k = some none →
    ∃ j < k, ∃ s, St Q L X g j = some (some s) ∧ BaseStop s

/-- **`WeakTracked`** from `hnext` at the states that are neither `Discharged` nor a base-word
stop, by induction along each thread. -/
theorem weakTracked_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hR : NextRestW Q L mem0 X) :
    WeakTracked Q L X := by
  have hL := launchRead_of_wf hpre hX
  intro g k hg
  induction k with
  | zero =>
    intro h
    have h' : Frame.stateAt (code L Q) X g 0 = some none := h
    rw [Frame.stateAt_zero] at h'
    simp at h'
  | succ k ih =>
    intro h
    by_cases hk : k < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      have h' : Frame.stateAt (code L Q) X g (k + 1) = some none := h
      rw [Frame.stateAt_succ he] at h'
      cases hs : Frame.stateAt (code L Q) X g k with
      | none => rw [hs] at h'; simp at h'
      | some σ =>
        cases σ with
        | none =>
          obtain ⟨j, hj, s, h1, h2⟩ := ih hs
          exact ⟨j, by omega, s, h1, h2⟩
        | some s =>
          rw [hs] at h'
          have hσ : St Q L X g k = some (some s) := hs
          by_cases hb : BaseStop s
          · exact ⟨k, by omega, s, hσ, hb⟩
          · exfalso
            have hpo : ∀ j < k, Good Q L mem0 X (g, j) := by
              intro j hj
              refine ⟨fun hn => ?_, hL _⟩
              have := someNone_mono (Q := Q) hn (show j + 1 ≤ k by omega)
              have hσ' : Frame.stateAt (code L Q) X g k = some (some s) := hσ
              rw [hσ'] at this
              cases this
            have hne : (threadCode L g Q).next s e ≠ some none := by
              by_cases hd : Discharged s
              · exact discharged_next_ne hpre hX hS hT hg he hσ hpo (hL _) hd
              · exact hR g k s e hg he hσ hd hb hpo (hL _)
            exact hne h'
    · have h1 : St Q L X g (k + 1) = St Q L X g k := by
        show Frame.stateAt (code L Q) X g (k + 1) = Frame.stateAt (code L Q) X g k
        rw [Frame.stateAt_of_le (by omega),
          Frame.stateAt_of_le (show (X.tr g).length ≤ k by omega)]
      rw [h1] at h
      obtain ⟨j, hj, s, h2, h3⟩ := ih h
      exact ⟨j, by omega, s, h2, h3⟩

/-- With every base-word stop excluded, the machines follow every thread. -/
theorem tracked_of_weak (hW : WeakTracked Q L X)
    (hB : ∀ g j s, g < L.threads → St Q L X g j = some (some s) → ¬ BaseStop s) :
    Frame.Tracked (code L Q) X := by
  intro g k hg h
  obtain ⟨j, -, s, h1, h2⟩ := hW g k hg h
  exact hB g j s hg h1 h2

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
