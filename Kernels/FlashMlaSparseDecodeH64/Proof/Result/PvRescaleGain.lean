-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.CanonicalPvReference
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ReferencePrefix

@[expose] public section

/-! # The actual gain between successive PV reference scales -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow PTX.Proof Protocol Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A reached state following the vote has the canonical reference and its exact gain.
A false vote leaves the previous reference unchanged. -/
theorem pv_rescale_gain {g i : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (ha : Wg0VoteCount.ordinal d = d.block + 1) (hb : 0 < d.block) :
    let head := Wg0.head L g
    let ref := canonicalPvReference P L X (ctaOf L g) d.block head
    let prior := canonicalPvReference P L X (ctaOf L g) (d.block - 1) head
    reference d = ref ∧ valFloat .f32 d.gainWord = .ok ((2 : ℝ) ^ (prior - ref)) ∧
      (d.voteTaken = false → prior = ref) := by
  dsimp only
  obtain ⟨j, v, tag, take, mid, _, hj, hV, hSite, hBlock, hMid, hRefD, hTake, hGain⟩ :=
    Wg0ReferencePrefix.after_vote hX hs ht he hd ha
  have hp := canonical_reference_before_vote hpre hX hs ht rfl hj hV hSite
  have hc := canonical_pv_vote_reference hpre hX hs ht _ _ rfl hj
    ⟨.any, 2 ^ 32 - 1, _, rfl⟩ hV hSite hBlock hMid
  have hRatio := canonical_vote_gain hpre hX hs ht rfl hj
    ⟨.any, 2 ^ 32 - 1, _, rfl⟩ hV hSite hMid
  simp only [hBlock, ite_eq_right hb.ne'] at hp hRatio
  refine ⟨hRefD.trans hc, ?_, ?_⟩
  · rwa [hGain]
  · intro hFalse
    have htFalse : take = false := hTake.symm.trans hFalse
    rw [htFalse] at hMid
    have hEq : mid = { v with gainWord := b32 1065353216 } :=
      Option.some.inj hMid.symm
    rw [← hp, ← hc, hEq]
    rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
