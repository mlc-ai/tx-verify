-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPageSeed
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyIterationCursor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- A later event or an observed shuffle ordinal forces a visit to a steady round. -/
def SteadyRoundDemand (p : Params) (l : Launch) (X : Execution)
    (g lane batch iteration j : Nat) (e : Event) : Prop :=
  (iteration < Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1 ∨
    e.pc < 1744) ∧
  (1741 ≤ e.pc ∨ primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) <
    ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl)

set_option maxRecDepth 100000 in
theorem steadySeedOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1396 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    128 * (trips - 2) + 127 < 2 ^ 31 ∧
      ∃ pos ≤ j, ∃ s ending,
        At s 1396 ([(7181, b32 9), (1091, b32 (trips - 1))] ++
          steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 640 := by
  obtain ⟨pos, hOrder, s, ending, hs, hr, hRank⟩ :=
    steadyFirstArmOfEvent hp hX hg hw hl writes hCTA hb hLo hHi hMany he (by omega) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  obtain ⟨hTile, _⟩ := assignedCoordinates_valid hp hLo hHi
  have hN := (Mma.trips_bounds hp hb hTile).2.1
  change trips ≤ (p.kLength batch + 127) / 128 at hN
  have hLen := (hp.lengths batch hb).2.2
  have hBound : 128 * (trips - 2) + 127 < 2 ^ 31 := by omega
  have hTid : tid < 512 := by unfold tid; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨u, hLocal, hu⟩ := steadyPagePrelude (g := thread) hp hb (by omega) hTid hs
  have huRun := hr.after_local_nonempty hLocal (traceAfterObservedEvent he hOrder)
  exact ⟨hBound, pos, hOrder, u, ending,
    hu.mono ⟨hu.2.2.2.2.1, holds_lookup hu.2.2.2.2 rfl, hu.2.2.2.2.2⟩, huRun, hRank⟩

set_option maxRecDepth 100000 in
/-- A real steady round carries its selected lane, page base and descending iteration. -/
theorem steadyRoundEntryOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1)
    (hMin : 9 ≤ iteration)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1396 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : SteadyRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    iteration ≤ trips - 2 ∧ 128 * (trips - 2) + 127 < 2 ^ 31 ∧
      ∃ pos ≤ j, ∃ s ending,
        At s 1396 ((7181, b32 iteration) ::
          steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) := by
  obtain ⟨hBound, pos, hOrder, s, ending, hs, hr, hsRank⟩ :=
    steadySeedOfEvent hp hX hg hw hl writes hCTA hb hLo hHi hMany he hPc hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let trips := Mma.trips p batch co.1
  let F := steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block)
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hShared : (2535, b32 l.sharedBase) ∈ F := by simp [F, steadyCacheFrame, warmStartFrame]
  have hRole : (1062, b32 (14 + warp.val)) ∈ F := by
    simp [F, steadyCacheFrame, warmStartFrame, hWarp]
  change 11 ≤ trips at hMany
  change 128 * (trips - 2) + 127 < 2 ^ 31 at hBound
  have hFit : trips - 1 < 2 ^ 31 := by omega
  have hInit : 9 < trips - 1 := by omega
  have hEq : 9 + (iteration - 9) = iteration := by omega
  have hBody (n : Nat) : ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n
        ([7181, 1091] ++ F.map Prod.fst) ins.op) = true := by kernel_rfl
  have hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    kernel_rfl
  obtain ⟨index, hBefore, u, stop, hIter, hu, huRun, huRank⟩ :=
    steadyObservedIterations (hops := iteration - 9) warp hFit hInit hShared hRole hBody hTail
      hs hr he hOrder (hEq.symm ▸ hDemand.1) hSafe
      (hDemand.2.imp_right (fun h => by rw [hsRank]; exact h))
  rw [hEq] at hIter hu
  have hIter' : iteration ≤ trips - 2 := by omega
  exact ⟨hIter', hBound, index, hBefore, u, stop,
    hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.2⟩, huRun,
    huRank.trans (congrArg (· + 64 * (iteration - 9)) hsRank)⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g lane j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {e : Event}
    (he : X.get (warpLane l g lane, j) = some e) (hPc : 1396 ≤ e.pc ∧ e.pc < 1741)
include hp hX hg hw hl writes hCTA he hPc

set_option maxRecDepth 100000 in
/-- A recorded steady event determines its selected tile, real iteration and
shuffle ordinal in that traversal. -/
theorem actualSteadyEventCheckpoint (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 ∧
      ∃ iteration, 9 ≤ iteration ∧
        iteration < Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1 ∧
        (((X.tr (warpLane l g lane)).take j).countP Execution.isShfl +
          loaderShuffleTail 1741 e.pc =
            primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) + 64) ∧
        let co := assignedCoordinates p batch (g / l.block)
        let thread := warpLane l g lane
        let trips := Mma.trips p batch co.1
        ∃ pos ≤ j, ∃ u stop,
          At u 1396 ((7181, b32 iteration) ::
            steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block)) ∧
          Run kernel Assumptions.all l thread u ((X.tr thread).drop pos) stop ∧
          ((X.tr thread).take pos).countP Execution.isShfl =
            primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) := by
  obtain ⟨batch, hb, hLo, hHi, hMany⟩ :=
    observedSteadyTrips hp hX hg hw hl writes hCTA he
      ⟨by have := hPc.1; omega, by have := hPc.2; omega⟩ hSafe
  obtain ⟨hBound, pos, hOrder, s, ending, hs, hr, hsRank⟩ :=
    steadySeedOfEvent hp hX hg hw hl writes hCTA hb hLo hHi hMany he hPc.1 hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let trips := Mma.trips p batch co.1
  let F := steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block)
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hShared : (2535, b32 l.sharedBase) ∈ F := by simp [F, steadyCacheFrame, warmStartFrame]
  have hRole : (1062, b32 (14 + warp.val)) ∈ F := by
    simp [F, steadyCacheFrame, warmStartFrame, hWarp]
  change 11 ≤ trips at hMany
  change 128 * (trips - 2) + 127 < 2 ^ 31 at hBound
  have hFit : trips - 1 < 2 ^ 31 := by omega
  have hInit : 9 < trips - 1 := by omega
  have hBody (n : Nat) : ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n
        ([7181, 1091] ++ F.map Prod.fst) ins.op) = true := by kernel_rfl
  have hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    kernel_rfl
  obtain ⟨iteration, hMin, hIter, hRank, sz, hSz, u, stop, hU, hRun, hRankStart⟩ :=
    steadyCheckpointOfObservedEvent warp hFit hInit hShared hRole hBody hTail
      hs hr he hOrder hPc.2 hSafe
  exact ⟨batch, hb, hLo, hHi, hMany, iteration, hMin, hIter,
    by simpa only [hsRank] using hRank, sz, hSz, u, stop,
    hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.2⟩, hRun,
    by simpa only [hsRank] using hRankStart⟩

/-- The shuffle ordinal of the actual steady traversal containing this observation. -/
theorem actualSteadyEventRound (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      11 ≤ Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 ∧
      ∃ iteration, 9 ≤ iteration ∧
        iteration < Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1 ∧
        ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl +
          loaderShuffleTail 1741 e.pc =
            primingSearchShuffleCount batch + 640 + 64 * (iteration - 9) + 64 := by
  obtain ⟨batch, hb, hLo, hHi, hMany, iteration, hLow, hHigh, hRank, _⟩ :=
    actualSteadyEventCheckpoint hp hX hg hw hl writes hCTA he hPc hSafe
  exact ⟨batch, hb, hLo, hHi, hMany, iteration, hLow, hHigh, hRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
