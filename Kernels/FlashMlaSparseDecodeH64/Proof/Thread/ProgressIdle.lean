-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbPrologue

public section

/-! # Counted extensions for the idle length reads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- The idle lane reads the launch bytes of either optional length word. -/
theorem idle_length_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {s : Thread.Site} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.idle s)))
    (hInput : s = .loadTopk ∨ s = .loadExtra) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hNonempty : X.tr g ≠ [] := by
    intro h
    rw [h, List.length_nil, Frame.stateAt_zero] at hState
    cases hState
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  rcases hInput with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_41)
    change out kernel Assumptions.all L g u =
      .ev (eventTmpl Assumptions.all L g u (.mem Thread.ncLoadTopk)) at hout
    rw [Thread.event_loadTopk hpre ha] at hout
    exact nc_extension hX hp.1 (.inl hNonempty) hrel hRun hTau hout
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_42)
    change out kernel Assumptions.all L g u =
      .ev (eventTmpl Assumptions.all L g u (.mem Thread.ncLoadExtra)) at hout
    rw [Thread.event_loadExtra hpre ha] at hout
    exact nc_extension hX hp.1 (.inl hNonempty) hrel hRun hTau hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
