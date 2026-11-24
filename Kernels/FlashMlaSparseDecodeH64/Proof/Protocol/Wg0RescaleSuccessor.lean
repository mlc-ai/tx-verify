-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0VoteSuccessor
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0RescaleGainTrace

@[expose] public section

/-! # The reference vote supplies the gain at rescale -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0RescaleSuccessor

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {X : Execution}
variable {g i : Nat} {d : D} {e : Event}

/-- A reached rescale site retains the finite gain computed by the reference vote. -/
theorem output_gain
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : Wg0RescaleGainTrace.GainSite d.site) :
    outputWord d.gainWord = true := by
  obtain ⟨_, _, _, u, _, _, _, hVote, hNext, hGain⟩ :=
    Wg0RescaleGainTrace.gain_from_vote hlen hd hsite
  rw [hGain]
  exact Wg0VoteSuccessor.gain_of_accepted_vote hVote hNext

/-- The rescale fence has the gain it needs to open the first tile. -/
theorem fence_never_dismiss
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleFence) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  have hg := output_gain (PTX.len_of_get he).le hd (by rw [hsite]; trivial)
  cases hk : e.kind <;> simp [Machine.next, Wg0.next, nextSite, hsite, hk]
  case tc cmd =>
    cases cmd
    case fenceAfter => simp [hg]
    all_goals simp

/-- At the rescale wait only the loaded tile's words need verification. -/
theorem wait_never_dismiss
    {tile : Fin 4} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile) (hWords : goodOutputWords d.rescaleWords = true) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  have hg := output_gain (PTX.len_of_get he).le hd (by rw [hsite]; trivial)
  cases hk : e.kind <;> simp [Machine.next, Wg0.next, nextSite, hsite, hk]
  case tc cmd =>
    cases cmd
    case waitLd => simp [hg, hWords]
    all_goals simp

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0RescaleSuccessor
