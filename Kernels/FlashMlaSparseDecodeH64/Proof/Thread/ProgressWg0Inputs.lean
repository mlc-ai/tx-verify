-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0Inputs

public section

/-! # Counted extensions for the softmax launch input reads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- A released softmax lane at its sink, main length or extra length reads the launch bytes. -/
theorem softmax_input_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) {g : Nat} {d : Wg0.D} (hp : Frame.Pending L X g)
    (hrel : PTX.Step.Released L X g)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hInput : d.site = .sink ∨ d.site = .lenOrig ∨ d.site = .lenExtra) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hNonempty : X.tr g ≠ [] := by
    intro h
    rw [h, List.length_nil, Frame.stateAt_zero] at hState
    cases hState
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  obtain ⟨a, k, hTemplate⟩ := UbWg0.input_template hpre ha hi hc hInput
  rw [hTemplate] at hout
  exact nc_extension hX hp.1 (.inl hNonempty) hrel hRun hTau hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
