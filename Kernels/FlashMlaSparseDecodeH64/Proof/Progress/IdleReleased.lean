-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Lemmas.Step.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.ClosingArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.OutputDrain
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressIdle

public section

/-! # Progress at released idle and terminal states -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- The idle lane can advance at every released state. -/
theorem idle_released_not_pending {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {s : Thread.Site} (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g (.idle s)) (hrel : PTX.Step.Released L X g) : False := by
  have hSafe := Safety.no_unsafe_of_tracked hpre hmax.1 hs ht
  have hub : ¬ HasUb X := fun h => hSafe (.inl h)
  cases s with
  | loadTopk =>
    exact hmax.not_grows (idle_length_extension hpre hmax.1 hs hub hp.1 hrel hp.2 (.inl rfl))
  | loadExtra =>
    exact hmax.not_grows (idle_length_extension hpre hmax.1 hs hub hp.1 hrel hp.2 (.inr rfl))
  | sync => exact closing_arrival_not_pending hpre hmax hs hub hp.1 hrel hp.2 rfl
  | exit => exact return_not_pending_of_output hpre hmax hs ht hSafe hub hp.1 hrel hp.2 rfl

/-- Once released at the common terminal state, the lane can return with drained stores. -/
theorem done_released_not_pending {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hp : PendingState P L X g .done) (hrel : PTX.Step.Released L X g) : False := by
  have hSafe := Safety.no_unsafe_of_tracked hpre hmax.1 hs ht
  exact return_not_pending_of_output hpre hmax hs ht hSafe (fun h => hSafe (.inl h))
    hp.1 hrel hp.2 trivial

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
