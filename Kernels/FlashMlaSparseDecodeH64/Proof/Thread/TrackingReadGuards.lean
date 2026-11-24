-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MachineTracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking

@[expose] public section

/-! # Actual read guards in the thread tracking induction -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- Only a shared scale or raw load can dismiss an already followed dequantizer. -/
theorem dequant_dismissal_is_read {g i : Nat} {d : Wg2.D} {e : Event}
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hn : Machine.next P L g (.wg2 d) e = some none) :
    ¬ Wg2.ValidRead d e ∧
      ((∃ r j, d.site = .scale r j) ∨ (∃ r j, d.site = .raw r j)) ∧
      ∃ a bs, e.kind = .rd a bs := by
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g (Frame.lt_of_get hX he))).fired_at he hd
  have hbad (hr : Wg2.ValidRead d e) : False := Wg2.never_dismiss hpre hX hs hd he hf hr hn
  refine ⟨hbad, ?_, ?_⟩
  · cases hsite : d.site
    case scale r j => exact .inl ⟨r, j, rfl⟩
    case raw r j => exact .inr ⟨r, j, rfl⟩
    all_goals exact (hbad (by simp [Wg2.ValidRead, hsite])).elim
  · by_contra h
    push Not at h
    apply hbad
    cases hsite : d.site <;> simp [Wg2.ValidRead, hsite, h]

/-- A followed softmax state in the actual first score-load prefix cannot be dismissed. -/
theorem softmax_first_mask_prefix_next (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    {g i : Nat} {d : Wg0.D} {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hEarly : Wg0.BeforeFirstQk P d ∨ Wg0.BeforeMaskRead d.site) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  rcases hEarly with hbefore | hbefore
  · rcases Wg0.composed_beforeFirstQk_next hpre hX hs he hd hbefore with h | ⟨q, h, _⟩
    · rw [h]; simp
    · rw [h]; simp
  · rcases Wg0.composed_beforeMaskRead_next hX hs he hd hbefore with h | ⟨q, h, _⟩
    · rw [h]; simp
    · rw [h]; simp

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
