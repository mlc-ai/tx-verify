-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.WarpSync
public import Kernels.FlashAttn4Fwd.Proof.Safety.WarpGuards

@[expose] public section

/-! # Synchronized polls and agreeing `tcgen05` collectives, from the warp facts

Every event of a launched thread other than undefined behaviour fires from a state of its machine
(`live_of_get`, as the machine follows every thread). So the warp facts (`WarpSyncFacts`), stated
at the machine's states, hold at every poll, collective and exit:

* **Synchronized polls** (`poll_synced`). Two lanes of a warp polling at one position in one
  round poll one object with one parity (`poll_round`), at a branch `Assumptions.pollAgree`
  selects (`poll_selected`); in different rounds, when they poll different objects, they are
  ordered (`poll_order`). This is the input of `Safety.no_warpDivergent`.
* **No warp-collective `tcgen05` mismatch** (`no_tcMismatch`, the `tcgen05` class of
  `AlignedMismatch`). The `n`-th collective events of two
  lanes of a warp are at the position and have the operands the warp's `n`-th entry gives
  (`tc_seq`). A lane performs fewer collective events than its warp's number, and has performed
  at least that many when it exits (`tc_count`); so a lane of the warp that exits has performed
  more than `n` of them whenever another lane performs its `n`-th. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An event of a launched thread other than undefined behaviour fires from a state of its
machine.** -/
theorem live_of_get (ht : ThreadFacts L X) (hX : Consistent L kernel asms mem0 X) {g k : Nat}
    {e : Event} (he : X.get (g, k) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ d, St L X g k = some (some d) :=
  Frame.event_state (C := code L) ht.sound hX ht.tracked he hub

/-- **Polls of one position by two lanes of a warp of different objects are ordered.** -/
theorem poll_synced (ht : ThreadFacts L X) (hX : Consistent L kernel asms mem0 X)
    (hw : WarpSyncFacts L X) : PollSynced L kernel asms X := by
  obtain ⟨R, hR⟩ := hw.poll_round
  refine PollSynced.of_rounds (warpKey L) R warpKey_eq (fun hg he => ?_)
    (fun pc h => poll_selected (pc + 1) h) hw.poll_order
  obtain ⟨d, hd⟩ := live_of_get ht hX he (by intro _ _ h; cases h)
  exact hR hg hd he

/-- **No warp-collective `tcgen05` mismatch**: two lanes of a warp at their `n`-th collective
event execute one instruction with the same operands (`tcgen05` divergence clause of
`AlignedMismatch`), and no lane of the warp exits before performing it (exit clause). -/
theorem no_tcMismatch (ht : ThreadFacts L X) (hX : Consistent L kernel asms mem0 X)
    (hw : WarpSyncFacts L X) :
    ¬ AlignedClass.tc.Divergent L kernel X ∧ ¬ AlignedClass.tc.Exited L kernel X := by
  obtain ⟨F, hF⟩ := hw.tc_seq
  obtain ⟨T, hlt, hex⟩ := hw.tc_count
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨g, kg⟩, ⟨h, kh⟩, n, pcg, pch, ke, kf, hsw, hgk, hhk, hge, hhe, hne⟩ :=
      (AlignedClass.divergent_tc_iff L).mp h
    obtain ⟨dg, hdg⟩ := live_of_get ht hX hge (by intro _ _ h; cases h)
    obtain ⟨dh, hdh⟩ := live_of_get ht hX hhe (by intro _ _ h; cases h)
    have h1 := hF (Frame.lt_of_get hX hge) hdg hge hgk
    have h2 := hF (Frame.lt_of_get hX hhe) hdh hhe hhk
    rw [warpKey_eq hsw, h2] at h1
    simp only [Prod.mk.injEq] at h1
    rcases hne with hne | hne
    · exact hne h1.1.symm
    · exact hne h1.2.symm
  · obtain ⟨⟨g, kg⟩, ⟨h, kh⟩, n, hsw, hgk, ⟨⟨pcx, hhx⟩, hle⟩⟩ :=
      (AlignedClass.exited_tc_iff L).mp h
    obtain ⟨ev, hev, hcoll⟩ := hgk.1
    obtain ⟨dg, hdg⟩ := live_of_get ht hX hev (by rintro pc f rfl; simp [isTcColl] at hcoll)
    have hn := hlt (Frame.lt_of_get hX hev) hdg hgk
    obtain ⟨dh, hdh⟩ := live_of_get ht hX hhx (by intro _ _ h; cases h)
    have hT := hex (Frame.lt_of_get hX hhx) hdh hhx
    rw [← warpKey_eq hsw] at hT
    have hsub : ((X.tr h).take kh).countP isTcColl ≤ (X.tr h).countP isTcColl :=
      (List.take_sublist _ _).countP_le
    simp only at hle hn hT
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
