-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents

public section

/-! # Issuing the index warp's ready publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- A released index lane can publish its written coordinates and validity byte. -/
theorem index_arrival_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Index.D} {extra : Bool} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hsg : SyncGuarded L kernel X)
    (hnr : ∀ e tag a bs, X.get e = some ⟨tag, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e tag a old new, X.get e = some ⟨tag, .rmw a old new⟩ → a.release = false)
    (hnf : ∀ e sem scope, ¬ X.ThreadFence e sem scope)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.index d)))
    (hd : d.site = .ready extra) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  rw [RingEvents.validReady_template hpre hd ha hi hc] at hout
  exact role_arrival_extension hX hord hsg hnr hnrmw hnf hp.1 hn hrel hRun hTau hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
