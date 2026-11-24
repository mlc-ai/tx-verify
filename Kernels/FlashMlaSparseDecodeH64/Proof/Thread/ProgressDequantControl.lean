-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbDequantData
import Lemmas.Order.GuardSnoc
import Lemmas.Step.Issue

public section

/-! # The dequantizer's optional lengths and async proxy fence -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- A released dequantizer can read the selected optional length. -/
theorem dequant_length_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg2.D} {orig : Bool} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hRel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg2 d)))
    (hd : d.site = Wg2.runtimeLenSite orig) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (Wg2.runtimeLenLoad_code orig))
  rw [UbDequant.length_template hpre hd ha] at hout
  exact nc_extension hX hp.1 (.inl hn) hRel hRun hTau hout

/-- The proxy fence before the dequantization publication has a counted extension. -/
theorem dequant_fence_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg2.D} (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hSafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hp : Frame.Pending L X g) (hRel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg2 d)))
    (hd : d.site = .fence) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX (fun hub => hSafe (.inl hub)) hp
  obtain ⟨u, ins, hTau, _, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_5)
  rw [Wg2.event_fence] at hout
  let event : Event := ⟨u.pc, .fenceProxy (.async (some (.shared .cta))) none⟩
  have hStep : EStep kernel Assumptions.all L g u event (some (PTX.next u)) :=
    ⟨_, hout, rfl, rfl⟩
  refine PTX.Step.quiet_counted_extension_reads hX hord hp.1 (.inl hn) hRel hRun hTau
    hStep trivial (fun _ h => Kind.noConfusion h) ?_
    (fun _ _ _ _ _ _ h => Kind.noConfusion h) (fun _ _ h => Kind.noConfusion h)
    (fun _ _ h => Kind.noConfusion h) (fun _ _ _ h => Kind.noConfusion h) rfl
    (fun _ h => Kind.noConfusion h) rfl ?_ ?_
  · intro l
    rw [AsyncCopy.objectAction, snoc_get_new]
  · exact Interface.all_wf_snoc_of_not_nc hX (fun _ _ h => Kind.noConfusion h)
      (fun h => Kind.noConfusion h)
  · exact (sync_guarded hX hSafe).snoc
      (fun _ _ _ _ he => write_no_release hX he)
      (fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim)
      (no_thread_fence hX)
      (ev := event) (fun _ _ h => Kind.noConfusion h) (fun _ _ _ h => Kind.noConfusion h)
      (fun _ _ h => Kind.noConfusion h)
      (fun _ _ _ _ _ h => Kind.noConfusion (congrArg Event.kind h))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
