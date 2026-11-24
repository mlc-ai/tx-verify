-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundEntry
import Kernels.TmlFa4Fwd.Proof.LoaderRecurringIndexSeed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- The actual warm round-entry registers determine the first scratch slot input. -/
theorem warmPageIndexAtRound {l : Launch} {p : Params}
    {g lane batch iteration : Nat}
    (hIteration : iteration ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 2)
    (hTileBound : 128 * (Mma.trips p batch
      (assignedCoordinates p batch (g / l.block)).1 - 2) + 127 < 2 ^ 31)
    (hTid : warpLane l g lane % l.block < 512)
    {s : TState}
    (hs : let co := assignedCoordinates p batch (g / l.block)
      let tid := warpLane l g lane % l.block
      let trips := Mma.trips p batch co.1
      At s 917 ([(7174, b32 iteration), (1116, b32 (trips - 2))] ++
        warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid)) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let tile := trips - 2 - iteration
    let row := primingLaneRow tile tid
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l thread) s u ∧
      At u 929 ([(1969, b32 row), (1964, b32 0), (7175, b32 0), (8, .pred true),
        (1118, b32 (128 * tile)), (1119, b32 (8 * (tid % 8)))] ++
        warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) := by
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let tile := trips - 2 - iteration
  let F := warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
  change iteration ≤ trips - 2 at hIteration
  change 128 * (trips - 2) + 127 < 2 ^ 31 at hTileBound
  have hHigh : 128 * (trips - 2) < 2 ^ 32 := by omega
  have hTile : 128 * tile + 127 < 2 ^ 31 := by unfold tile; omega
  obtain ⟨t, ht, htAt⟩ := warmPageTileSeedCore (g := thread) hIteration hHigh s
    (hs.mono ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.1, trivial⟩)
  obtain ⟨htA, htFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    (by kernel_rfl) (by kernel_rfl) ht
  have hF := holdsSchedulerFrame hs.2.2.2.2.2.2 htFrame (fun _ hx => List.mem_map_of_mem hx)
  have ht' : At t 921 ([(1118, b32 (128 * tile)), (1061, b32 tid),
      (7175, b32 (0 : Fin 2).val), (775, .pred true)] ++ F) := htAt.mono
    ⟨htAt.2.2.2.2.1, holds_lookup hF rfl, htAt.2.2.2.2.2.1, htAt.2.2.2.2.2.2.1, hF⟩
  obtain ⟨u, hu, huAt⟩ := warmPageIndexRunFromSlot (g := thread) hTile hTid 0 true
    (by kernel_rfl) ht'
  exact ⟨u, run_rtg (run_comp htA hu), huAt⟩

/-- The page lookup of any observed warm iteration uses the decreasing launch tile. -/
theorem warmRoundFirstPageIndexOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 929 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : WarmRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let tile := trips - 2 - iteration
    let row := primingLaneRow tile tid
    row + 64 < 2 ^ 31 ∧ ∃ pos ≤ j, ∃ s ending,
      At s 929 ([(1969, b32 row), (1964, b32 0), (7175, b32 0), (8, .pred true),
        (1118, b32 (128 * tile)), (1119, b32 (8 * (tid % 8)))] ++
        warmStartFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
      Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
      ((X.tr thread).take pos).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration := by
  obtain ⟨_, hIteration, hTileBound, pos, hBefore, s, ending, hs, hr, hsRank⟩ :=
    warmRoundEntryOfEvent hp hX hg hw hl writes hCTA hb hLo hHi he
      (by omega) hSafe hDemand
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let tile := trips - 2 - iteration
  have hTile : 128 * tile + 127 < 2 ^ 31 := by
    change 128 * (trips - 2) + 127 < 2 ^ 31 at hTileBound
    unfold tile
    omega
  have hTid : tid < 512 := by unfold tid; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨u, hu, huAt⟩ := warmPageIndexAtRound hIteration hTileBound hTid hs
  have huRun := hr.after_local_nonempty hu
    (traceAfterObservedEvent he hBefore)
  have hRow : primingLaneRow tile tid + 64 < 2 ^ 31 := by
    simp [primingLaneRow, kvCopyColumn]
    have h0 := Nat.mod_lt (tid / 8) (by decide : 0 < 8)
    have h1 := Nat.mod_lt tid (by decide : 0 < 8)
    omega
  exact ⟨hRow, pos, hBefore, u, ending, huAt, huRun, hsRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
