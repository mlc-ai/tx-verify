-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadySpillRoute
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem steadyPointerCellsApart (l : Launch) (g byte : Nat) (value : Bool)
    (hb : byte < 8) : ¬ (pointerSaveAccess l g (steadySpillSite value) 1).Covers
      ((pointerSaveAccess l g (steadySpillSite value) 0).loc.at byte) := by
  cases value <;>
    simp [pointerSaveAccess, pointerSaveAddress, pointerReloadAddress,
      steadySpillSite, Acc.Covers, Loc.InRange, Loc.at] <;> omega

set_option maxRecDepth 100000 in
/-- The observed steady K or V pass saves both actual lane pointers before entering the copies. -/
theorem steadyOperandSpillsOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1)
    (hMin : 9 ≤ iteration) (value : Bool)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hLate : pointerSavePc (steadySpillSite value) < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : SteadyRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let row := primingLaneRow (trips - 2 - iteration) tid
    ∃ pos ≤ j, ∃ s ending,
      At s (steadySpillExit value)
        (steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
      Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
      ((X.tr thread).take pos).countP Execution.isShfl =
        primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) +
          (if value then 32 else 0) ∧
      ∀ slot : Fin 2, ∃ write < pos,
        X.Writes (thread, write) (pointerSaveAccess l thread (steadySpillSite value) slot)
          (b64 (steadyOperandPointer p value batch (co.2 / 6) (row + 64 * slot.val))).toBytes ∧
        ∀ byte < 8, ∀ k < pos, ∀ a, X.Access (thread, k) a true →
          a.Covers ((pointerSaveAccess l thread (steadySpillSite value) slot).loc.at byte) →
            k ≤ write := by
  have hEarlier : 1423 < pointerSavePc (steadySpillSite value) := by cases value <;> decide
  obtain ⟨pos, hFirst, hSecond, hOrder, s, ending, hs, hr, hsRank⟩ :=
    steadyRoundPageWordsOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi hMany hMin he
      (hEarlier.trans hLate) hSafe hDemand
  obtain ⟨start, hStart, hStartRun, index, hIndex, hBefore, t, stop, ht, htRun, htRank⟩ :=
    steadySpillStartFromPages value hs hr he hOrder hLate hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let row := primingLaneRow (trips - 2 - iteration) tid
  let F := steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
  let site := steadySpillSite value
  let metaNext := pos + primingScratchReads p batch row + 2
  let metaExit := metaNext + primingScratchReads p batch (row + 64) + 2
  change metaExit ≤ index at hIndex
  change ((X.tr thread).take index).countP Execution.isShfl =
    ((X.tr thread).take metaExit).countP Execution.isShfl + (if value then 32 else 0) at htRank
  have hFirstBefore : metaNext ≤ index := by dsimp [metaExit] at hIndex; omega
  have hSecondBefore : metaExit ≤ index + 3 := by omega
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by dsimp [co]; unfold Params.heads at hHead; omega
  have hWindow (i : Nat) (hCount : ((X.tr thread).take i).countP Execution.isShfl =
      ((X.tr thread).take index).countP Execution.isShfl) :
      ((X.tr thread).take i).countP Execution.isShfl ≤
      ((X.tr thread).take metaExit).countP Execution.isShfl + 32 := by
    rw [hCount, htRank]
    cases value <;> simp
  have hDemand0 : PrefixDemand X thread index (pointerSavePc site) stop :=
    .inr ⟨j, e, hBefore, hLate, he⟩
  obtain ⟨hLow0, hHigh0, hSave0, a, ha, haRun⟩ :=
    steadyOperandPointerSave hp hX (pos := pos) (index := index) (row := row)
      hb hh value 0 true hFirst hFirstBefore ht htRun hDemand0 (fun target =>
        steadyPageWordsLatest hp hX hFirst hSecond (hStart.mono trivial) hStartRun
          (hWindow index rfl) 0 target)
  have hReadLow : (recurringScratchWord site false).pc ≤ pointerSavePc site := by
    cases value <;> decide
  have hReadHigh : (recurringScratchWord site true).pc ≤ pointerSavePc site := by
    cases value <;> decide
  have haBefore := afterObservedPointerSave he hBefore hLow0 hHigh0 hSave0 hLate
    hReadLow hReadHigh le_rfl
  obtain ⟨b, hbLocal, hbAt⟩ := steadySpillRoute (g := thread) (F := F) value true
    (by intro operand; cases operand <;> kernel_rfl) ha
  obtain ⟨c, hc, hcAt⟩ := steadySpillSecond (g := thread) value
    (by intro operand; cases operand <;> kernel_rfl) hbAt
  have hcRun := haRun.after_local_nonempty (run_rtg (run_comp hbLocal hc))
    (traceAfterObservedEvent he haBefore)
  have hRank0 := (countShuffleTakeOfNonshuffle hSave0 rfl).trans
    ((countShuffleTakeOfNonshuffle hHigh0 rfl).trans (countShuffleTakeOfNonshuffle hLow0 rfl))
  have hDemand1 : PrefixDemand X thread (index + 3) (pointerSavePc site) stop :=
    .inr ⟨j, e, haBefore, hLate, he⟩
  obtain ⟨hLow1, hHigh1, hSave1, d, hd, hdRun⟩ :=
    steadyOperandPointerSave hp hX (pos := metaNext) (index := index + 3) (row := row + 64)
      hb hh value 1 false hSecond hSecondBefore hcAt hcRun hDemand1 (fun target =>
        steadyPageWordsLatest hp hX hFirst hSecond (hStart.mono trivial) hStartRun
          (hWindow (index + 3) hRank0) 1 target)
  have hdBefore := afterObservedPointerSave he haBefore hLow1 hHigh1 hSave1 hLate
    hReadLow hReadHigh le_rfl
  obtain ⟨u, hu, huAt⟩ := steadySpillRoute (g := thread) (F := F) value false
    (by intro operand; cases operand <;> kernel_rfl) hd
  have huRun := hdRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hdBefore)
  have hRank1 := (countShuffleTakeOfNonshuffle hSave1 rfl).trans
    ((countShuffleTakeOfNonshuffle hHigh1 rfl).trans (countShuffleTakeOfNonshuffle hLow1 rfl))
  refine ⟨index + 3 + 3, hdBefore, u, stop, huAt.mono huAt.2.2.2.2.2.2, huRun, ?_, ?_⟩
  · rw [hRank1, hRank0, htRank, hsRank]
  intro slot
  fin_cases slot
  · refine ⟨index + 2, by omega, ?_, ?_⟩
    · exact ⟨_, by simpa [co, thread, tid, row, site] using hSave0⟩
    intro byte hByte k hk a hA hCover
    by_contra! hPast
    have hWhich : k = index + 3 ∨ k = index + 3 + 1 ∨ k = index + 3 + 2 := by omega
    rcases hWhich with rfl | rfl | rfl
    · exact observedReadNoWrite hLow1 hA
    · exact observedReadNoWrite hHigh1 hA
    have hAcc : a = pointerSaveAccess l thread site 1 := by
      rcases hA with ⟨_, _, hFalse⟩ | ⟨_, ⟨pc, hGet⟩, _⟩ | ⟨_, _, pc, hGet⟩
      · cases hFalse
      · exact (Kind.wr.inj (congrArg Event.kind (Option.some.inj (hGet.symm.trans hSave1)))).1
      · cases Option.some.inj (hGet.symm.trans hSave1)
    exact steadyPointerCellsApart l thread byte value hByte (hAcc ▸ hCover)
  · exact ⟨index + 3 + 2, by omega,
      ⟨_, by simpa [co, thread, tid, row, site] using hSave1⟩, by intros; omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
