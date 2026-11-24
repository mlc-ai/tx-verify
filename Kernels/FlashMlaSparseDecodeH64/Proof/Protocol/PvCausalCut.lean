-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxFixedSteps
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0GemmTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingPhases
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingSources

@[expose] public section

/-! # A softmax consumer follows the earlier numerical guards in its CTA -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvCausalCut

open PTX PTX.Flow GemmRing MachineTracking

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The reader's barrier prefix is beyond the probabilities of the PV block being evaluated. -/
structure Cut (P : Params) (L : Launch) (X : Execution) (g i block : Nat) : Prop where
  present : ∃ e, X.get (g, i) = some e
  blockLt : block < Wg0.blocksOf P L g
  count : 2 * block + 2 < ((X.tr g).take i).countP (Execution.isBarId 9)
  prior : ∀ w, baseCausality L X w (g, i) → ¬ Dismisses P L X w

theorem blocks_eq {g h : Nat} (hc : ctaOf L h = ctaOf L g) :
    Wg0.blocksOf P L h = Wg0.blocksOf P L g := by
  simp only [Wg0.blocksOf, Wg0.eOf, ctaidY, hc]

/-- Every earlier loop guard in this CTA is on the causal prefix of the output read. -/
theorem no_earlier_dismissal {g i block h j : Nat} {q : Wg0.D} {f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hCut : Cut P L X g i block)
    (hCta : ctaOf L h = ctaOf L g)
    (hf : X.get (h, j) = some f)
    (hq : Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 q)))
    (hData : SoftmaxDataSite q.site) (hNotBar : Execution.isBarId 9 f = false)
    (hNotEpi : q.site.inEpilogue = false) (hBlock : q.block ≤ block) :
    ¬ Dismisses P L X (h, j) := by
  obtain ⟨e, he⟩ := hCut.present
  have hh := Frame.lt_of_get hX hf
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hf hq
  have hInv : Wg0.Inv P L h q := hInv
  have hCount := Wg0BarrierCount.count_at_wg0 hpre hX (hs h hh).machine hf hq
  have hBound : Wg0BarrierCount.ordinal q ≤ 2 * q.block + 2 := by
    cases hSite : q.site <;>
      simp [hSite, SoftmaxDataSite, Wg0.Site.inEpilogue] at hData hNotEpi
    all_goals simp [Wg0BarrierCount.ordinal, Wg0BarrierCount.localOrdinal, hSite]
  have hEarlier := hCut.count
  have hBlockLt := hCut.blockLt
  rw [← blocks_eq (P := P) hCta] at hBlockLt
  exact hCut.prior _ (Wg0PeerReadback.order_of_bar9_counts hpre hX hs
    ⟨hh, hg, hCta⟩ hInv.warpLt hInv.wg hf he hNotBar (by omega) (by omega))

private theorem guard_published_blocks {q : Wg0.D} (hData : SoftmaxDataSite q.site) :
    Wg0GemmTrace.publishedBlocks q = q.block + (if q.site.inEpilogue then 1 else 0) := by
  cases hSite : q.site <;> simp [hSite, SoftmaxDataSite] at hData
  all_goals simp [Wg0GemmTrace.publishedBlocks, hSite]

/-- A loop guard has already acquired its own block's QK notification. -/
theorem guard_qk_count {h j : Nat} {q : Wg0.D} {f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hf : X.get (h, j) = some f)
    (hq : Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 q)))
    (hData : SoftmaxDataSite q.site) (hBody : q.site.inEpilogue = false) :
    okPolls (GemmRing.qk L (ctaOf L h) (rawSlot q.block)) ((X.tr h).take j) = q.block / 2 + 1 := by
  have hh := Frame.lt_of_get hX hf
  have hCount := Wg0GemmTrace.qk_successes_of_state hpre (rawSlot q.block)
    ((hs h hh).machine.produces (hX.thr h hh)) hq
  have hHeld : Wg0GemmTrace.held q.site = true := by
    cases hk : q.site <;> simp [hk, SoftmaxDataSite, Wg0.Site.inEpilogue] at hData hBody
    all_goals rfl
  have hPublished : Wg0GemmTrace.publishedBlocks q = q.block := by
    rw [guard_published_blocks hData, hBody]
    rfl
  rw [hHeld, hPublished] at hCount
  change okPolls (GemmRing.qk L (ctaOf L h) (rawSlot q.block)) ((X.tr h).take j) =
    (q.block + (1 - q.block % 2)) / 2 + (if q.block % 2 = q.block % 2 ∧ true = true
      then 1 else 0) at hCount
  simp only [and_self, ↓reduceIte] at hCount
  omega

/-- The publication of the selected probability block has a followed softmax source. -/
theorem publication_followed {g i block h a tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hCut : Cut P L X g i block) (hc : ctaOf L h = ctaOf L g) (hWg : wgOf L h = 0)
    (ha : X.get (h, a) = some
      ⟨tag, .arrive (GemmRing.score L (ctaOf L h) (rawSlot block)) 0 1 true .cta⟩)
    (hCount : arrivals (GemmRing.score L (ctaOf L h) (rawSlot block)) ((X.tr h).take a) =
      block / 2) :
    Frame.stateAt (Machine.code P L) X h a ≠ some none := by
  intro hDismiss
  obtain ⟨j, hj, q, f, hf, hq, hData, hNotBar, hBad⟩ :=
    dismissed_softmax_guard hpre hX hs hWg ha hDismiss
  have hh := Frame.lt_of_get hX hf
  have hPub := Wg0GemmTrace.score_arrivals_of_state hpre (rawSlot block)
    ((hs h hh).machine.produces (hX.thr h hh)) hq
  let m := GemmRing.score L (ctaOf L h) (rawSlot block)
  change arrivals m ((X.tr h).take j) =
    (Wg0GemmTrace.publishedBlocks q + (1 - block % 2)) / 2 at hPub
  have hMono : arrivals m ((X.tr h).take j) ≤ arrivals m ((X.tr h).take a) :=
    (List.take_sublist_take_left hj.le).countP_le
  change arrivals m ((X.tr h).take a) = block / 2 at hCount
  have hPublished : Wg0GemmTrace.publishedBlocks q ≤ block := by omega
  have hQPub := guard_published_blocks hData
  have hBlockLt := hCut.blockLt
  rw [← blocks_eq (P := P) hc] at hBlockLt
  have hNotEpi : q.site.inEpilogue = false := by
    cases hEpi : q.site.inEpilogue
    · rfl
    · obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hf hq
      have hLast := (show Wg0.Inv P L h q from hInv).epilogueLast hEpi
      simp only [hEpi, ↓reduceIte] at hQPub
      omega
  exact no_earlier_dismissal hpre hX hs hCut hc hf hq hData hNotBar hNotEpi
    (by omega) hBad

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvCausalCut
