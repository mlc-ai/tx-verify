-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeCommit

@[expose] public section

/-!
# `Safety.Protocol.lifetime`

`Life.lifetime` is exactly the statement of the field `Safety.Protocol.lifetime`
(`¬ SharedLifetimeUnsafe L kernel asms X`) from `Pre`, the thread facts, and five named premises
(each a row of "thread-layer gaps", see the development notes):

* `ho : OdoneWait Q L X` (the barrier of the softmax region's `o_done` poll, a field of `Safety`'s
  own premises, shared with `mbarPlaced_of`) and `hT` (`Premises.tmplOk`): placement of the uses;
* `F : ∀ c < L.grid, Tmem1.OFinalFacts L X c` (the MMA warp of every launched CTA and its one
  commit to `o_final`; shared with `tmemAccess`);
* `hobs : CopyObserved L X` (every tensor load is observed by a poll of `kv_ready`);
* `hS : SObserved L X` (every commit to `s_ready` is observed by a poll);
* `hN : NextCommit L X` (a commit at a `kv_empty`/`o_done` site is followed by another commit of
  its thread).

The commits at `kv_empty` and `o_done` need no observer: `Assumptions.commitOrder` chains them to
the next commit. The `o_final` commit is observed by the epilogue (`exit_poll`) and every MMA is
tracked by it (`mmaFinished`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Life
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Safety

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Safety.Protocol.lifetime`**: every shared use completes before an exit of its CTA. -/
theorem lifetime (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (ho : OdoneWait Q L X)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (F : ∀ c < L.grid, Tmem1.OFinalFacts L X c)
    (hobs : CopyObserved L X) (hS : SObserved L X) (hN : NextCommit L X) :
    ¬ SharedLifetimeUnsafe L kernel asms X := by
  have own := own_of hpre hX hf ho hT
  exact no_sharedLifetimeUnsafe hX own (copyFinished hX own hobs) (mmaFinished hpre hX hf F)
    (commitFinished hpre hX hf own F hS hN)

end
end PTX.Kernels.InklingRelDecode.Proof.Life
