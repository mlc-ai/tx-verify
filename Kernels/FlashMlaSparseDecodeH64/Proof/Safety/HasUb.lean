-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
public import Lemmas.Flow.UbStop
public import Lemmas.Flow.UbStop
import Lemmas.Flow.Final

public section

/-! # Undefined behaviour obligations of the actual thread stream -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Checked event templates and continuing returned events exclude undefined behaviour. -/
theorem no_ub_of_live_steps (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hTemplates : ∀ {g i : Nat} {d : Machine.ThreadD}, g < L.threads →
      Frame.stateAt (Machine.code P L) X g i = some (some d) → ∀ t ins,
        (Machine.code P L g).AtD d t → (Machine.code P L g).inv d →
        kernel.code[(Machine.code P L g).pc d]? = some ins →
        ∀ f, eventTmpl Assumptions.all L g t ins.op ≠ .ub f)
    (hContinue : ∀ {g j d e}, X.get (g, j) = some e →
      Frame.stateAt (Machine.code P L) X g j = some (some d) →
      (∀ f, e.kind ≠ .ub f) → e.kind ≠ .exit → Machine.next P L g d e ≠ none) :
    ¬ HasUb X := by
  rintro ⟨⟨g, i⟩, tag, fault, he⟩
  have hg := Frame.lt_of_get hX he
  rcases Code.ub_stopped_at (hs g hg) (hX.thr g hg) he
      (fun d hd t ins ha hi hc => hTemplates hg hd t ins ha hi hc fault) with hStop | hDismiss
  · obtain ⟨j, d, hj, hLive, hDead⟩ := Frame.first_stop ht hg hStop
    have hi : i < (X.tr g).length := PTX.len_of_get he
    have hj' : j < (X.tr g).length := by omega
    let v := (X.tr g)[j]
    have hv : X.get (g, j) = some v := List.getElem?_eq_getElem hj'
    have hn := Frame.stateAt_succ (C := Machine.code P L) hv
    rw [hLive, hDead] at hn
    have hnext : Machine.next P L g d v = none := hn.symm
    obtain ⟨_, _, _, ⟨_, _, hFire⟩⟩ :=
      ((hs g hg).machine.produces (hX.thr g hg)).fired_some hv (by omega)
    have hEnds : ¬ Ends v := by
      intro hh
      cases fires_end_none hFire hh
    exact hContinue hv hLive (fun f hf => hEnds (.inl ⟨f, hf⟩))
      (fun hExit => hEnds (.inr hExit)) hnext
  · exact ht g i hg hDismiss

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
