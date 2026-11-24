-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

@[expose] public section

/-! # Earlier concrete returns count towards the slot's release ordinal -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem actual_softmax_return_count_le {g start i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hStart : start ≤ i)
    (hAnchor : FirstMaskAnchor P L X g start) (hTag : e.pc = Wg0.Site.validFree.pc)
    {block : Nat}
    (hBlock : block = (((X.tr g).drop start).take (i - start)).countP isProbabilityPublication) :
    block / 4 ≤ arrivals (free L (ctaOf L g) (indexSlot block)) ((X.tr g).take i) := by
  induction i using Nat.strong_induction_on generalizing block e with
  | h i ih =>
    by_cases hFirst : block < 4
    · rw [Nat.div_eq_of_lt hFirst]
      exact Nat.zero_le _
    obtain ⟨b, hb, _, _, q, _, hq, _, hPrevious⟩ :=
      actual_softmax_return_ordinal hpre hX hs he hStart hAnchor hTag
    have hSame := hb.trans hBlock.symm
    subst b
    let prev := block - 4
    obtain ⟨j, hjStart, hj, f, hf, hSite, hPrev⟩ := hPrevious prev (by unfold prev; omega)
    have hLe : j < i := hj.trans hq
    have hBound := ih j hLe hf hjStart hSite hPrev
    have hSlot : indexSlot prev = indexSlot block := by
      apply Fin.ext
      change prev % 4 = block % 4
      unfold prev
      omega
    rw [hSlot] at hBound
    obtain ⟨b', hb', _, hKind, _⟩ :=
      actual_softmax_return_ordinal hpre hX hs hf hjStart hAnchor hSite
    rw [hb', ← hPrev] at hKind
    let m := free L (ctaOf L g) (indexSlot block)
    change f.kind = .arrive (free L (ctaOf L g) (indexSlot prev)) 0 1 true .cta at hKind
    rw [hSlot] at hKind
    have hCount := countP_take_succ hf (show arrivesOn m f = true by
      simp [arrivesOn, sourceArrive, hKind, m])
    have hMono := countP_take_mono (arrivesOn m) (X.tr g) (show j + 1 ≤ i by omega)
    change prev / 4 ≤ ((X.tr g).take j).countP (arrivesOn m) at hBound
    change block / 4 ≤ ((X.tr g).take i).countP (arrivesOn m)
    rw [hCount] at hMono
    unfold prev at hBound
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
