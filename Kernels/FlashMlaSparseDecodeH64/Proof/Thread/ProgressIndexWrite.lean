-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWrite
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbIndexData

public section

/-! # Issuing the index warp's shared writes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- A released index lane can append its coordinate word or validity byte. -/
theorem index_write_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Index.D} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.index d)))
    (hd : (∃ extra high, d.site = .coord extra high) ∨ ∃ extra, d.site = .valid extra) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  obtain ⟨a, bs, v, hWeak, hTemplate⟩ := UbIndex.write_template hpre hd ha hi hc
  rw [hTemplate] at hout
  exact role_write_extension hpre hs hX ht hub hp.1 hrel hSigma (fun _ h => by cases h)
    hRun hTau hWeak hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
