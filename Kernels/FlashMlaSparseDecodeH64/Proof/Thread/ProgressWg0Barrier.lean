-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
import Lemmas.Step.Issue

public section

/-! # Counted arrivals at the softmax warpgroup's named barriers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- At its pair or warpgroup named barrier, a released lane appends its sync arrival. -/
theorem softmax_named_bar_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg0.D} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hRel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hd : Wg0BarrierTrace.Bar9Site d.site ∨ d.site = .pairBar) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  have hTemplate : ∃ id count, eventTmpl Assumptions.all L g u ins.op =
      .bar id (PTX.next u) (some count) .sync := by
    rcases hd with h9 | hPair
    · exact ⟨9, 128, Wg0BarrierTrace.bar9_template hpre ha hc h9⟩
    · exact ⟨_, 64, Wg0BarrierTrace.pair_bar_template hpre ha hc hPair⟩
  obtain ⟨id, count, hTmpl⟩ := hTemplate
  rw [hTmpl] at hout
  exact PTX.Step.bar_counted_extension hX hp.1 (.inl hn) hRel
    (Interface.all_wf_snoc_of_not_nc hX (fun _ _ h => Kind.noConfusion h)
      (fun h => Kind.noConfusion h)) hRun hTau ⟨_, hout, rfl, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
