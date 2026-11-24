-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPageSlots
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- Replay the selected steady round from its entry to the first scratch slot. -/
theorem steadyPageIndexAtRound {l : Launch} {p : Params}
    {g lane batch iteration : Nat}
    (hIter : iteration ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 2)
    (hBound : 128 * (Mma.trips p batch
      (assignedCoordinates p batch (g / l.block)).1 - 2) + 127 < 2 ^ 31)
    {s : TState}
    (hs : let co := assignedCoordinates p batch (g / l.block)
      let tid := warpLane l g lane % l.block
      let trips := Mma.trips p batch co.1
      At s 1396 ((7181, b32 iteration) ::
        steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid)) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let tile := trips - 2 - iteration
    let row := primingLaneRow tile tid
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l thread) s u ∧
      At u 1403 ([(1148, b32 row), (2131, b32 0)] ++
        steadySlotFrame p l batch (co.2 / 6) trips (warpIndex l g) tid tile 0 true) := by
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let tile := trips - 2 - iteration
  let row := primingLaneRow tile tid
  let F := steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
  change iteration ≤ trips - 2 at hIter
  change 128 * (trips - 2) + 127 < 2 ^ 31 at hBound
  obtain ⟨t, ht, hT⟩ := steadyPageTileSeed (g := thread) (tid := tid) hIter
    (by omega) s (hs.mono ⟨holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2.1,
      holds_lookup hs.2.2.2.2 rfl, trivial⟩)
  obtain ⟨_, htFrame⟩ := loaderSegmentFrame (regs := F.map Prod.fst)
    (lower := 1396) (stop := 1401) (by decide) (by decide) (by kernel_rfl)
    ht hs.1.ge (by simp [hs.1])
  have hF := holdsSchedulerFrame hs.2.2.2.2.2 htFrame (fun _ hm => List.mem_map_of_mem hm)
  have ht' : At t 1401 ([(7182, b32 (0 : Fin 2).val), (778, .pred true),
      (1148, b32 row)] ++ F) :=
    hT.mono ⟨hT.2.2.2.2.2.1, hT.2.2.2.2.2.2.1, hT.2.2.2.2.1, hF⟩
  obtain ⟨u, hu, huAt⟩ := steadyPageSlotInput (g := thread) 0 true ht'
  exact ⟨u, run_rtg (run_comp ht hu), huAt⟩

/-- An observed steady round refreshes the two actual page-table cells for its
descending logical tile, with the original lane and selected request. -/
theorem steadyRoundPageWordsOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1)
    (hMin : 9 ≤ iteration)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1423 < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : SteadyRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let tile := trips - 2 - iteration
    let row := primingLaneRow tile tid
    ∃ pos,
      let second := pos + primingScratchReads p batch row + 2
      let endPosition := second + primingScratchReads p batch (row + 64) + 2
      SteadyPageWords p l X thread pos batch row 0 ∧
        SteadyPageWords p l X thread second batch (row + 64) 1 ∧ endPosition ≤ j ∧
        ∃ s ending, At s 1424 (steadySlotFrame p l batch (co.2 / 6) trips (warpIndex l g)
            tid tile 1 false) ∧
          Run kernel Assumptions.all l thread s ((X.tr thread).drop endPosition) ending ∧
          ((X.tr thread).take endPosition).countP Execution.isShfl =
            primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) := by
  obtain ⟨hIter, hBound, pos, hOrder, s, ending, hs, hr, hsRank⟩ :=
    steadyRoundEntryOfEvent hp hX hg hw hl
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hCTA hb hLo hHi hMany hMin
      he (by omega) hSafe hDemand
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let tile := trips - 2 - iteration
  let row := primingLaneRow tile tid
  change iteration ≤ trips - 2 at hIter
  change 128 * (trips - 2) + 127 < 2 ^ 31 at hBound
  have hRow : row + 64 < 2 ^ 31 := by
    have hDiv := Nat.mod_lt (tid / 8) (show 0 < 8 by decide)
    have hMod := Nat.mod_lt tid (show 0 < 8 by decide)
    dsimp [row, primingLaneRow, kvCopyColumn, packetSrcOff, tile]
    omega
  obtain ⟨u, hu, huAt⟩ := steadyPageIndexAtRound hIter hBound hs
  have huRun := hr.after_local_nonempty hu
    (traceAfterObservedEvent he hOrder)
  obtain ⟨hFirst, hSecond, hBefore, v, hv, hvRun, _, hvRank⟩ :=
    steadyPageWordsFromIndex hp hX hFrame hb hRow huAt huRun he hOrder hPc
  exact ⟨pos, hFirst, hSecond, hBefore, v, ending, hv, hvRun, hvRank.trans hsRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
