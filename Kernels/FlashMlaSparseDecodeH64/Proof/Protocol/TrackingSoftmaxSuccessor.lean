-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TrackingMaskSuccessor
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxFixedSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0RescaleSuccessor
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0RunningPeak
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.CausalPvValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantInputs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCausalInduction

@[expose] public section

/-! # Tracking the actual numerical guards -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Output load guards. -/
private def SoftmaxValueGuard : Wg0.Site → Prop
  | .rescaleWait _
  | .oWait _ => True
  | _ => False

private theorem data_guard_partition (site : Wg0.Site) :
    SoftmaxDataSite site →
      site = .maskRead ∨ site = .rescaleFence ∨ site = .maxRead ∨ site = .rescaleVote ∨
        site = .lseRead ∨ (∃ k, site = .peerRead k) ∨ SoftmaxValueGuard site := by
  cases site <;> simp [SoftmaxDataSite, SoftmaxValueGuard]

/-- Every thread follows its role machine on a consistent launch. -/
theorem tracked
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    Frame.Tracked (Machine.code P L) X := by
  refine tracked_of_causal_softmax_steps (P := P) (L := L) (X := X) hpre hX hs ?_
  intro g i d e he hd hPrior
  by_cases hSite : d.site = .maskRead
  · exact mask_next_tracked hpre hX hs he hd hSite hPrior
  by_cases hFence : d.site = .rescaleFence
  · exact Wg0RescaleSuccessor.fence_never_dismiss he hd hFence
  by_cases hMax : d.site = .maxRead
  · rcases Wg0MaxSuccessor.actual_next hpre hX hs (Result.qk_values hpre hX hs)
      he hd hMax hPrior with h | ⟨_, h, _⟩ <;> simp [h]
  by_cases hVote : d.site = .rescaleVote
  · rcases Wg0VoteSuccessor.actual_next hpre hX hs (Result.qk_values hpre hX hs)
      he hd hVote hPrior with h | ⟨_, h, _⟩ <;> simp [h]
  by_cases hLse : d.site = .lseRead
  · exact Result.Wg0RunningPeak.causal_lse_read_never_dismiss hpre hX hs he hd hLse hPrior
  by_cases hPeer : ∃ k, d.site = .peerRead k
  · obtain ⟨k, hk⟩ := hPeer
    exact Wg0PeerQkValues.actual_never_dismiss hpre hX hs (Result.qk_values hpre hX hs)
      he hd hk hPrior
  by_cases hGuard : SoftmaxValueGuard d.site
  · cases h : d.site <;> simp only [SoftmaxValueGuard, h] at hGuard
    case rescaleWait tile =>
      exact Result.causal_output_wait_never_dismiss hpre hX hs he hd (.inl h) hPrior
    case oWait tile =>
      exact Result.causal_output_wait_never_dismiss hpre hX hs he hd (.inr h) hPrior
  apply fixed_softmax_next hpre hX hs he hd
  intro h
  rcases data_guard_partition d.site h with
    hMask | hRescale | hMaximum | hVoteSite | hLseSite | hRead | hValueSite <;> contradiction

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
