-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFallbackRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Epilogue Prologue Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem nextFallbackOffsetsOfMaximal {g old ordinal : Nat} (hg : g < l.threads)
    (hMore : old + 31 < p.batch) (hProtected : DrainCuQProtected p X)
    (c : FallbackScanCursor l X g 1988 ordinal (mmaFallbackBackedgeFacts p l g old)) :
    Nonempty (FallbackScanCursor l X g 2000 ordinal (fallbackOffsetFacts p l g (old + 31))) := by
  have hFrame : At c.state 1988 (groupScanFacts .select old p.batch (g / l.block) ++
      (7194, b32 (tilePrefix p (old + 31) * p.heads)) :: fallbackAbi p l g) := by
    simpa only [mmaFallbackBackedgeFacts, mmaFallbackCutoff, Nat.min_eq_right hMore.le]
      using c.checkpoint
  obtain ⟨u, hu, hU⟩ := advanceFallbackSearch hp hMore hFrame
  obtain ⟨before, ready, hBound, hRel, hReady, hPast, hTau, hTail, hEvent⟩ :=
    fallbackLaneCuQReadOfMaximal hp hMax hg hMore.le hProtected
      (by at_select hU) c.runPrefix (c.localSteps.trans (run_rtg hu)) c.continuation
      c.pos_pos c.pos_le c.released
  let index := old + 31 + laneOf l g
  let pos := if index ≤ p.batch then c.pos + 1 else c.pos
  have hCount : ((X.tr g).take pos).countP Execution.isShfl = ordinal ∧
      ((X.tr g).take pos).countP isFullWarpVote = 0 := by
    by_cases hi : index ≤ p.batch
    · rw [show pos = c.pos + 1 by simp [pos, hi], List.take_add_one,
        show (X.tr g)[c.pos]? = _ from hEvent hi]
      exact ⟨by simpa [Execution.isShfl] using c.shuffleCount,
        by simpa [isWarpVote, voteClass] using c.ballotCount⟩
    · simpa only [pos, ite_eq_right hi] using And.intro c.shuffleCount c.ballotCount
  have hPositive : 0 < pos := by
    have := c.pos_pos
    dsimp only [pos]
    split_ifs <;> omega
  exact ⟨⟨pos, before, ready, c.lastState, hPositive, hBound, hCount.1, hCount.2, hRel,
    hReady, hPast, hTau, hTail⟩⟩

/-- Read the adjacent offsets, replay all five up exchanges, broadcast the total, and take the
selected-group branch or loop back using the updated cutoff. -/
theorem fallbackGroupOfMaximal {g first count : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    (cur : ∀ h, SameWarp l g h → FallbackScanCursor l X h 2000 count
      (fallbackOffsetFacts p l h first)) :
    let more := mmaFallbackCutoff p first ≤ g / l.block
    Nonempty (FallbackScanCursor l X g (if more then 1988 else 2042) (count + 7)
      (if more then mmaFallbackBackedgeFacts p l g first
        else mmaSelectedGroupFacts p l g first)) := by
  classical
  apply fallbackRouteOfMaximal hp hMax hg hFirst
  intro h hWarp
  refine Classical.choice (fallbackUpOfMaximal hp hMax hWarp.1.2.1 hFirst ?_)
  intro peer hPeer
  exact Classical.choice (fallbackTileCountOfMaximal hp hMax hPeer.1.2.1 hFirst
    (fun k hK => cur k (Step.sameWarp_trans hWarp (Step.sameWarp_trans hPeer hK))))

private theorem fallbackOffsetsOfMaximal (hProtected : DrainCuQProtected p X) (group : Nat)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (hMore : 31 * (group + 1) < p.batch)
    (hLo : tilePrefix p (31 * (group + 1)) * p.heads ≤ g / l.block) :
    Nonempty (FallbackScanCursor l X g 2000 (11 + 7 * group)
      (fallbackOffsetFacts p l g (31 * (group + 1)))) := by
  classical
  induction group generalizing g with
  | zero => exact firstFallbackOffsetCursor hp hMax hg hw hProtected hMore hLo
  | succ group ih =>
    let old := 31 * (group + 1)
    have hNext : old + 31 = 31 * (group + 1 + 1) := by dsimp [old]; omega
    have hMore' : old + 31 < p.batch := hNext ▸ hMore
    have hBefore : tilePrefix p old * p.heads ≤ g / l.block :=
      (Nat.mul_le_mul_right _ (tilePrefix_mono p (show old ≤ old + 31 by omega))).trans
        (hNext ▸ hLo)
    have hCut : mmaFallbackCutoff p old ≤ g / l.block := by
      rw [mmaFallbackCutoff, Nat.min_eq_right hMore'.le, hNext]
      exact hLo
    have hRoute := fallbackGroupOfMaximal hp hMax hg (show old ≤ p.batch by omega)
      (fun peer hPeer => Classical.choice (ih hPeer.1.2.1 (hPeer.2.symm.trans hw)
        (show old < p.batch by omega) (hPeer.1.2.2 ▸ hBefore)))
    dsimp only at hRoute
    rw [ite_eq_left hCut, ite_eq_left hCut] at hRoute
    obtain ⟨c⟩ := hRoute
    have hRestore := nextFallbackOffsetsOfMaximal hp hMax hg hMore' hProtected c
    simpa only [hNext, show 11 + 7 * group + 7 = 11 + 7 * (group + 1) by omega] using hRestore

/-- Every active later group reaches the common MMA selection boundary with its true request
coordinates, inclusive prefix values, and actual shuffle ordinal. -/
theorem laterMmaGroupOfMaximal (hProtected : DrainCuQProtected p X) (group : Nat) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (hMore : 31 * (group + 1) < p.batch)
    (hLo : tilePrefix p (31 * (group + 1)) * p.heads ≤ g / l.block)
    (hHi : g / l.block < mmaFallbackCutoff p (31 * (group + 1))) :
    Nonempty (FallbackScanCursor l X g 2042 (18 + 7 * group)
      (mmaSelectedGroupFacts p l g (31 * (group + 1)))) := by
  classical
  have hRoute := fallbackGroupOfMaximal hp hMax hg hMore.le
    (fun peer hPeer => Classical.choice (fallbackOffsetsOfMaximal hp hMax hProtected group
      hPeer.1.2.1 (hPeer.2.symm.trans hw) hMore (hPeer.1.2.2 ▸ hLo)))
  dsimp only at hRoute
  have hOrdinal : 11 + 7 * group + 7 = 18 + 7 * group := by omega
  simpa only [ite_eq_right (Nat.not_le_of_lt hHi), hOrdinal] using hRoute

/-- A padded CTA scans through the final populated group and returns to the exhausted
search boundary. The remaining local branch bypasses tile selection. -/
theorem idleFinalMmaGroupOfMaximal {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hProtected : DrainCuQProtected p X) (hBatch : 31 < p.batch)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    let group := (p.batch - 1) / 31
    let first := 31 * group
    Nonempty (FallbackScanCursor l X g 1988 (11 + 7 * group)
      (mmaFallbackBackedgeFacts p l g first)) := by
  classical
  let group := (p.batch - 1) / 31
  let first := 31 * group
  have hPart : (p.batch - 1) % 31 + first = p.batch - 1 := Nat.mod_add_div _ _
  have hRest : (p.batch - 1) % 31 < 31 := Nat.mod_lt _ (by decide)
  have hGroup : 0 < group := by dsimp [group]; omega
  have hFirst : first < p.batch := by omega
  have hLast : p.batch ≤ first + 31 := by omega
  have hOld := (Nat.mul_le_mul_right p.heads (tilePrefix_mono p hFirst.le)).trans hIdle
  have hCut : mmaFallbackCutoff p first ≤ g / l.block := by
    rwa [mmaFallbackCutoff, Nat.min_eq_left hLast]
  let before := group - 1
  have hBase : 31 * (before + 1) = first := by dsimp [before, first]; omega
  have hRoute := fallbackGroupOfMaximal hp hMax hg hFirst.le (count := 11 + 7 * before)
    (fun peer hs => Classical.choice (by
      simpa only [hBase] using fallbackOffsetsOfMaximal hp hMax hProtected before
        hs.1.2.1 (hs.2.symm.trans hw) (hBase.symm ▸ hFirst) (hBase.symm ▸ hs.1.2.2 ▸ hOld)))
  dsimp only at hRoute ⊢
  have hOrdinal : 11 + 7 * before + 7 = 11 + 7 * group := by dsimp [before]; omega
  simpa only [ite_eq_left hCut, hOrdinal] using hRoute

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
