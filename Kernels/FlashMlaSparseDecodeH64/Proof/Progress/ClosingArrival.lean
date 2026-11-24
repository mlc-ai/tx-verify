-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingArrivalRelease
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Closing
import Lemmas.Kernel.ProgressDescent
import Lemmas.Step.Issue

public section

/-! # A released role never remains before its closing arrival at maximality -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- Every role can issue the CTA closing arrival once its predecessor has released. -/
theorem closing_arrival_not_pending {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Machine.ThreadD} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hsite : ScoreClosingGate.ClosingSite d) : False := by
  obtain ⟨t, t1, hrun, hlocal, he⟩ := ClosingArrival.event hpre hmax.1 hs hub hp hd hsite
  exact hmax.not_grows (PTX.Step.bar_counted_extension hmax.1 hp.1
    (.inl (ClosingProgress.nonempty_tail hd (by rintro rfl; exact hsite))) hrel
    (Interface.all_wf_snoc_of_not_nc hmax.1 (by intros; simp) (by simp)) hrun hlocal he)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
