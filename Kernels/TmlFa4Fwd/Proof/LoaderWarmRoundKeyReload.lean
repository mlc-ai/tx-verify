-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeyPointers
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
import Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondReload

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
include hp hX hFrame hg hw hl hCTA hb hLo

/-- The first K reload of the named warm traversal recovers that round's real pointer. -/
theorem warmRoundFirstKeyReloadOfEvent (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hPc : 1003 < e.pc)
    (hSafe : ∀ f, e.kind ≠ .ub f) (hDemand : WarmRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let row := primingLaneRow (trips - 2 - iteration) tid
    let ptr := primingKRowPointer p batch (co.2 / 6) row
    ∃ pos, pos + 2 ≤ j ∧
      ∃ s ending,
        At s 1004 ([(1998, b32 (ptr % 2 ^ 32)), (1999, b32 (ptr / 2 ^ 32))] ++
          warmCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop (pos + 2)) ending ∧
        ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 + 64 * iteration := by
  obtain ⟨index, hBefore, s, ending, hs, hr, hRank, hSaves⟩ :=
    warmRoundKeyPointersAtReload hp hX hFrame hg hw hl hCTA hb hLo hHi he hPc hSafe hDemand
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let row := primingLaneRow (trips - 2 - iteration) tid
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by dsimp [co]; unfold Params.heads at hHead; omega
  obtain ⟨write, hOrder, hBytes, hLast⟩ := hSaves 0
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hBytes
  have demand : PrefixDemand X thread index 1003 ending := .inr ⟨j, e, hBefore, hPc, he⟩
  obtain ⟨u, hu, huRun, hLow, hHigh⟩ :=
    warmKFirstReloadObserved hp hX (row := row) hb hh hOrder le_rfl hs hr demand hBytes hLast
  have preceding {i : Nat} {read : Event} (hRead : X.get (thread, i) = some read)
      (hReadPc : read.pc = 1003) : i ≠ j := by
    intro hEq
    subst j
    have same := Option.some.inj (hRead.symm.trans he)
    rw [← same, hReadPc] at hPc
    omega
  have low := preceding hLow rfl
  have high := preceding hHigh rfl
  exact ⟨index, by omega, u, ending, hu, huRun,
    (countShuffleTakeOfNonshuffle hHigh rfl).trans
      ((countShuffleTakeOfNonshuffle hLow rfl).trans hRank)⟩

/-- The upper saved pointer and the retained lane column reach the second half
of any observed warm K traversal. -/
theorem warmRoundSecondKeyReloadOfEvent (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hPc : 1072 < e.pc)
    (hSafe : ∀ f, e.kind ≠ .ub f) (hDemand : WarmRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let row := primingLaneRow (trips - 2 - iteration) tid + 64
    let ptr := primingKRowPointer p batch (co.2 / 6) row
    ∃ pos, pos + 2 ≤ j ∧
      ∃ s ending,
        At s 1073 ([(2019, b32 (ptr % 2 ^ 32)), (2020, b32 (ptr / 2 ^ 32)),
          (7666, b64 (16 * (tid % 8)))] ++ warmCacheFrame p l batch (co.2 / 6) trips
            (warpIndex l g) tid) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop (pos + 2)) ending ∧
        ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 + 64 * iteration + 16 := by
  obtain ⟨index, hBefore, s, ending, hs, hr, hRank, hSaves⟩ :=
    warmRoundKeyPointersAtReload hp hX hFrame hg hw hl hCTA hb hLo hHi he (by omega) hSafe hDemand
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let row := primingLaneRow (trips - 2 - iteration) tid + 64
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by dsimp [co]; unfold Params.heads at hHead; omega
  obtain ⟨pos, hOrder, hOrdinal, u, stop, hu, huRun⟩ :=
    warmSecondKeyPointerReloadFromCursor hp hX (row := row) hb hh hs hr
      (by simpa only [Fin.val_one, Nat.mul_one] using hSaves 1) he hBefore hPc hSafe
  exact ⟨pos, hOrder, u, stop, hu, huRun, hOrdinal.trans (congrArg (· + 16) hRank)⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
