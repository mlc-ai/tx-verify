-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLaterSelectionProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderBatchSelect
import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

private theorem selectionOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g warp first batch shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 297 (fun lane =>
      (89, .pred (decide (first + lane < batch))) ::
        (1079, b32 (tilePrefix p first * p.heads)) ::
        loaderVoteCarry p l g warp first lane) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 302 (loaderChosenFacts p l g warp first batch)
      shuffles (votes+1) ends) := by
  let hit := fun lane => decide (first+lane < batch)
  let post := fun (lane : Nat) (word : BitVec 32) =>
    next (setReg (cur.state lane) 1751 (b32 word.toNat))
  have hNext (lane : Nat) (hl : lane < 32) :=
    loaderSelectionNext hp cur.toSchedulerWarpAt lane hl
  have hMore := cur.ballotSuffix hp hMax hg hit post hNext
  obtain ⟨result,hPos,hEvent⟩ :=
    loaderSelectBatchPresent hp hMax.1 hg hFirst hGroup hBatch cur.toSchedulerWarpAt hMore
  refine ⟨{ toSchedulerWarpAt := result
            positive := ?_
            bounded := ?_
            released := ?_
            recorded := ?_ }⟩
  · rw [hPos]
    exact fun _ _ => Nat.succ_pos _
  · rw [hPos]
    intro lane hl
    obtain ⟨_,he,_⟩ := hEvent lane hl
    exact len_of_get he
  · rw [hPos]
    intro lane hl
    obtain ⟨_,he,_⟩ := hEvent lane hl
    exact releasedIfLast he (by intro h; cases h)
  · intro lane hl
    obtain ⟨word,he,hState⟩ := hEvent lane hl
    have hLen : cur.pos lane < (X.tr (warpLane l g lane)).length := len_of_get he
    rw [hPos,hState,List.take_succ_eq_append_getElem hLen,(List.getElem?_eq_some_iff.mp he).2]
    apply (cur.recorded lane hl).snoc (cur.localSteps lane hl)
    exact ⟨_,(hNext lane hl).stop,word,by rw [(cur.checkpoint lane hl).1],rfl⟩

/-- A loader warp selects the assigned request even after one or more scheduler backedges. -/
theorem selectedBatchOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X)
    {batch : Nat} (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 302
      (loaderChosenFacts p l g (warpIndex l g) (31 * (batch / 31)) batch)
      (10 + 7 * (batch / 31)) 1 ends) := by
  let group := batch / 31
  let first := 31 * group
  have hPart := Nat.div_add_mod batch 31
  have hRem := Nat.mod_lt batch (show 0 < 31 by decide)
  have hFirst : first ≤ batch := by dsimp [first, group]; omega
  have hGroup : batch < first + 31 := by dsimp [first, group]; omega
  have hLower : tilePrefix p first * p.heads ≤ g / l.block :=
    (Nat.mul_le_mul_right _ (tilePrefix_mono p hFirst)).trans hLo
  have hUpper : g / l.block < tilePrefix p (min p.batch (first + 31)) * p.heads := by
    have hLe : batch + 1 ≤ min p.batch (first + 31) := Nat.le_min.mpr ⟨by omega, by omega⟩
    exact hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hLe))
  change ∃ ends, Nonempty (SchedulerWarpReached l X g 302
    (loaderChosenFacts p l g (warpIndex l g) first batch) (10 + 7 * group) 1 ends)
  cases hGroupIndex : group with
  | zero =>
    have hZero : first = 0 := by simp [first, hGroupIndex]
    have hGroup' : batch < 31 := by omega
    have hActive : g / l.block < tilePrefix p (min p.batch 31) * p.heads := by
      simpa only [hZero, Nat.zero_add] using hUpper
    have hRoute := firstRouteOfMaximal hp hMax hg hw hCuQ
    rw [ite_eq_left hActive] at hRoute
    obtain ⟨ends,⟨cur⟩⟩ := hRoute
    obtain ⟨prep,hPos,hBefore⟩ :=
      loaderFirstBallotReadyPreserving hp hg hGroup' hBatch hLo hHi cur.toSchedulerWarpAt
    have hReady : SchedulerWarpReached l X g 297 (fun lane =>
        (89, .pred (decide (0 + lane < batch))) ::
          (1079, b32 (tilePrefix p 0 * p.heads)) ::
          loaderVoteCarry p l g (warpIndex l g) 0 lane) 10 0 ends := by
      simpa only [Nat.zero_add, tilePrefix, Finset.range_zero, Finset.sum_empty, Nat.zero_mul]
        using cur.reframe prep hPos hBefore
    exact ⟨ends,by simpa only [hZero] using
      selectionOfMaximal hp hMax hg (Nat.zero_le batch) hGroup' hBatch hReady⟩
  | succ n =>
    have hIndex : first = 31 * (n + 1) := by simp [first, hGroupIndex]
    have hEnd : first + 31 = 31 * (n + 2) := by omega
    obtain ⟨ends,⟨cur⟩⟩ := laterLoaderGroupOfMaximal hp hMax hg hw hCuQ n
      (by omega) (hIndex ▸ hLower) (hEnd ▸ hUpper)
    have hCur : SchedulerWarpReached l X g 288
        (loaderLaterChoiceFacts p l g (warpIndex l g) first) (10 + 7 * n.succ) 0 ends := by
      simpa only [hIndex] using cur
    obtain ⟨prep,hPos,hBefore⟩ :=
      loaderGroupBallotReadyPreserving hp hg hFirst hGroup hBatch hLo hHi hCur.toSchedulerWarpAt
    exact ⟨ends,selectionOfMaximal hp hMax hg hFirst hGroup hBatch
      (hCur.reframe prep hPos hBefore)⟩

end PTX.Kernels.TmlFa4Fwd.Loader
