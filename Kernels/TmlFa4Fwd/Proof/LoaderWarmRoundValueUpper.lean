-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundValuePointers
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValueReload
import Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondValueReload

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- The upper saved pointer and the retained lane column reach the second half
of any observed warm V traversal. -/
theorem warmRoundSecondValueReloadOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1292 < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : WarmRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let row := primingLaneRow (trips - 2 - iteration) tid + 64
    let ptr := primingVRowPointer p batch (co.2 / 6) row
    ∃ pos, pos + 2 ≤ j ∧
      ∃ s ending,
        At s 1293 ([(2098, b32 (ptr % 2 ^ 32)), (2099, b32 (ptr / 2 ^ 32)),
          (7721, b64 (16 * (tid % 8)))] ++ warmCacheFrame p l batch (co.2 / 6) trips
            (warpIndex l g) tid) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop (pos + 2)) ending ∧
        ((X.tr thread).take (pos + 2)).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 + 64 * iteration + 32 + 16 := by
  obtain ⟨index, hBefore, s, ending, hs, hr, hRank, hSaves⟩ :=
    warmRoundValuePointerSavesOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi he
      (by omega) hSafe hDemand
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let row := primingLaneRow (trips - 2 - iteration) tid + 64
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by dsimp [co]; unfold Params.heads at hHead; omega
  have hTid : tid < 512 := by unfold tid; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨pos, hOrder, hOrdinal, u, stop, hu, huRun⟩ :=
    warmSecondValuePointerReloadFromCursor hp hX (row := row) hb hh hTid hs hr
      (by simpa only [Fin.val_one, Nat.mul_one] using hSaves 1) he hBefore hPc hSafe
  exact ⟨pos, hOrder, u, stop, hu, huRun, hOrdinal.trans (congrArg (· + 16) hRank)⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
