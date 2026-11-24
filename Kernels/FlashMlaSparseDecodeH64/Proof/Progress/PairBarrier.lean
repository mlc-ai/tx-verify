-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.NamedBarrier
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits

public section

/-! # A softmax exchange waits for an earlier lane of its pair -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Wg0 Protocol.Wg0PeerOrder
open _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem member_warp {g : Nat} {p : Fin 2} (hpre : Pre P L mem0)
    (h : g % L.block / 32 ∈ pairWarps p) : warpOf L g % 2 = p.val := by
  have hW : warpOf L g ∈ pairWarps p := by
    simpa only [warpOf, tidOf_eq hpre, hpre.block] using h
  simp only [pairWarps, Finset.mem_insert, Finset.mem_singleton] at hW
  have hp := p.isLt
  omega

private theorem pair_count_after_done (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    {g i : Nat} (hg : g < L.threads) (hwg : wgOf L g = 0)
    {p : Fin 2} (hw : warpOf L g % 2 = p.val)
    (hDone : Frame.stateAt (Machine.code P L) X g i = some (some .done)) :
    blocksOf P L g ≤ (X.tr g).countP (Execution.isBarId (10 + p.val)) := by
  have hSound := (hs g hg).machine
  obtain ⟨j, _, d, _, hState, hSite, he, _⟩ :=
    Wg0OutputVisits.barrierBeforeDone hpre hX hg hSound hwg hDone 0
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hState
  have hLast := (show Inv P L g d from hInv).epilogueLast (by rw [hSite]; rfl)
  have hOrd := Wg0PeerTrace.count_at_wg0 hpre hX hSound he hState
  simp only [hw, Wg0PeerTrace.ordinal, hSite, Wg0PeerTrace.completedPair] at hOrd
  rw [← hLast, ← hOrd]
  exact (List.take_sublist _ _).countP_le

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
private theorem before_pair_priority {g h : Nat} {d q : D}
    (hRow : ctaidY L g = ctaidY L h)
    (hd : Inv P L g d) (hq : Inv P L h q) (hSite : d.site = .pairBar)
    (hOrdinal : Wg0PeerTrace.ordinal q ≤ d.block) :
    softmaxTime P L h q ≤ softmaxTime P L g d := by
  have hLt := hd.blockLt
  have hLast := hq.epilogueLast
  have hSub := hq.subLt
  simp only [blocksOf, eOf, hRow] at hLt hLast
  clear hd hq
  cases hQ : q.site
  all_goals
    simp only [Wg0PeerTrace.ordinal, Wg0PeerTrace.completedPair, hQ] at hOrdinal
    simp [hQ, Site.inEpilogue, Site.elems] at hSub hLast
    simp only [softmaxTime, hSite, hQ, wg0Ordinal, blockTime, completionTime, hRow]
    omega

/-- A last arrival at barrier 10 or 11 either releases or has a missing participant of strictly
earlier priority. The two pair identities use the same checked barrier-history progress. -/
theorem pair_release_or_earlier (hpre : Pre P L mem0)
    (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hub : ¬ HasUb X)
    (hNoFault : ∀ Y, Consistent L kernel Assumptions.all mem0 Y → ¬ CtaBarFault L Y)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    {g tag : Nat} {p : Fin 2}
    (he : X.IsBarrier (g, (X.tr g).length - 1) (10 + p.val) (some 64) tag) :
    ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)) ∧
      ((∃ Y, Maximal L kernel Assumptions.all mem0 Y ∧ Y.tr = X.tr ∧ PTX.Step.Released L Y g) ∨
        ∃ other q, SameCta L g other ∧ Frame.Pending L X other ∧
          Frame.stateAt (Machine.code P L) X other (X.tr other).length = some (some q) ∧
          priority P L other q < priority P L g (.wg0 d)) := by
  have hg := Frame.lt_of_get hmax.1 he
  obtain ⟨before, hB, hSite, _, hParity, _, _⟩ :=
    Wg0PeerTrace.pair_at hpre hmax.1 (hs g hg).machine ht he rfl
  obtain ⟨_, _, _, _, hI, _, _⟩ := Frame.fired_site hs hmax.1 he hB
  have hInv : Inv P L g before := hI
  have hOrd := Wg0PeerTrace.pairOrdinal hpre hmax.1 (hs g hg).machine he hB hSite
  rw [hParity] at hOrd
  let d : D := { before with site := .peerRead 0 }
  have hLen : (X.tr g).length - 1 < (X.tr g).length := PTX.len_of_get he
  have hIndex : (X.tr g).length - 1 + 1 = (X.tr g).length := by omega
  have hTail : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.wg0 d)) := by
    rw [← hIndex, Frame.stateAt_succ he, hB, Option.bind_some]
    change Machine.next P L g (.wg0 before) ⟨tag, .bar (10 + p.val) (some 64) .sync⟩ = _
    simp [Machine.next, Wg0.next, Wg0.nextSite, hSite, d]
    rfl
  have hAfter : softmaxTime P L g before < softmaxTime P L g d := by
    simp [softmaxTime, hSite, d, wg0Ordinal, blockTime]
  have hWarps (w : Nat) (h : w ∈ pairWarps p) : w < 4 := by
    simp only [pairWarps, Finset.mem_insert, Finset.mem_singleton] at h
    have := p.isLt
    omega
  have hExit h (hc : SameCta L g h) (hm : h % L.block / 32 ∈ pairWarps p)
      (hwg : wgOf L h = 0) i et (he' : X.get (h, i) = some ⟨et, .exit⟩) :
      ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId (10 + p.val)) <
        (X.tr h).countP (Execution.isBarId (10 + p.val)) := by
    have hDone := Wg0OutputVisits.doneAtExit hmax.1 (hs h hc.2.1).machine ht hwg he' rfl
    have hCount := pair_count_after_done hpre hmax.1 hs hc.2.1 hwg (member_warp hpre hm) hDone
    have hRow : blocksOf P L g = blocksOf P L h := by
      simp only [blocksOf, eOf, ctaidY, ctaOf, hc.2.2]
    rw [hOrd]
    exact lt_of_lt_of_le (hRow ▸ hInv.blockLt) hCount
  refine ⟨d, hTail, ?_⟩
  rcases named_release_or_missing hpre hmax hNoFault (pairShape hpre p)
    (pairSources hpre hmax.1 hs p) hWarps he hExit with
    hRelease | ⟨h, hc, hm, hwg, hp, hMissing⟩
  · exact .inl hRelease
  obtain ⟨q, hQ⟩ := hLive h hp
  refine .inr ⟨h, q, hc, hp, hQ, ?_⟩
  have hRow : ctaidY L g = ctaidY L h := by simp only [ctaidY, ctaOf, hc.2.2]
  have hWarp := member_warp hpre hm
  rcases Wg0OutputVisits.softmax_state_cases hmax.1 hp.1 (hs h hp.1).machine hwg hQ with
    ⟨s, rfl⟩ | ⟨peer, rfl⟩ | rfl
  · have hPrior : priority P L h (.prologue s) < softmaxTime P L g before := by
      simp only [priority, softmaxTime, hSite, wg0Ordinal, blockTime]
      omega
    exact hPrior.trans hAfter
  · obtain ⟨_, hRun⟩ := Frame.run_some hmax.1 hub hp
    obtain ⟨_, _, _, _, hv, _, _⟩ := Frame.end_at hs hp.1 hRun hQ
    have hCount := Wg0PeerTrace.count_at_wg0_tail hpre hmax.1 (hs h hp.1).machine hp.1 hQ
    rw [hWarp] at hCount
    rw [hOrd, hCount] at hMissing
    exact lt_of_le_of_lt (before_pair_priority hRow hInv hv hSite hMissing) hAfter
  · have hDone := pair_count_after_done hpre hmax.1 hs hp.1 hwg hWarp hQ
    have hLt := hInv.blockLt
    simp only [blocksOf, eOf, hRow] at hLt
    simp only [blocksOf, eOf] at hDone
    rw [hOrd] at hMissing
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
