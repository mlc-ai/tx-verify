-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundPageIndex
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPageSlots
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- An observed warm round refreshes the two actual page-table cells for its
descending logical tile, with the original lane and selected request. -/
theorem warmRoundPageWordsOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 953 < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : WarmRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let tile := trips - 2 - iteration
    let row := primingLaneRow tile tid
    ∃ pos,
      let second := pos + primingScratchReads p batch row + 2
      let endPosition := second + primingScratchReads p batch (row + 64) + 2
      WarmPageWords p l X thread pos batch row 0 ∧
        WarmPageWords p l X thread second batch (row + 64) 1 ∧ endPosition ≤ j ∧
        ∃ s ending, At s 954 (warmSlotFrame p l batch (co.2 / 6) trips (warpIndex l g)
            tid tile 1 false) ∧
          Run kernel Assumptions.all l thread s ((X.tr thread).drop endPosition) ending ∧
          ((X.tr thread).take endPosition).countP Execution.isShfl =
            primingSearchShuffleCount batch + 64 + 64 * iteration := by
  obtain ⟨hRow, pos, hOrder, s, ending, hs, hr, hsRank⟩ :=
    warmRoundFirstPageIndexOfEvent hp hX hg hw hl
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hCTA hb hLo hHi he
      (by omega) hSafe hDemand
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let tile := trips - 2 - iteration
  let row := primingLaneRow tile tid
  have hTid : tid < 512 := by unfold tid; rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have hTile : 128 * tile + 127 < 2 ^ 31 := by
    change primingLaneRow tile tid + 64 < 2 ^ 31 at hRow
    unfold primingLaneRow at hRow
    omega
  have hAt : At s 929 ([(1969, b32 row), (1964, b32 (64 * (0 : Fin 2).val))] ++
      warmSlotFrame p l batch (co.2 / 6) trips (warpIndex l g) tid tile 0 true) := hs
  obtain ⟨hPage0, hPage1, hWithin, u, hu, huRun, _, huRank⟩ :=
    warmPageWordsFromIndex hp hX hFrame hb hTile hTid hRow hAt hr he hOrder hPc
  exact ⟨pos, hPage0, hPage1, hWithin, u, ending, hu, huRun, huRank.trans hsRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
