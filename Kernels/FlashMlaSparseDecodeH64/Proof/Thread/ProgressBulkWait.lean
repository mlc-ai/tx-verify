-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Lemmas.Step.BulkWait

public section

/-! # The opening bulk-group wait issues as a real thread event -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- The released softmax lane at the opening bulk wait issues its actual wait instruction. -/
theorem bulk_wait_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) {g : Nat} {d : Wg0.D} (hp : Frame.Pending L X g)
    (hrel : PTX.Step.Released L X g)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hSite : d.site = .bulkWait) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hNonempty : X.tr g ≠ [] := by
    intro h
    rw [h, List.length_nil, Frame.stateAt_zero] at hState
    cases hState
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, _, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hSite] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_198)
  exact PTX.Step.BulkWait.bulk_wait_counted_extension hX hp.1 hNonempty hrel
    (Interface.all_wf_snoc_of_not_nc hX (by intros; nofun) (by nofun))
    hRun hTau ⟨_, hout, rfl, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
