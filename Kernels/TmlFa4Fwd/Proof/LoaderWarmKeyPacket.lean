-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeyPairBroadcast
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPairSource
import Kernels.TmlFa4Fwd.Proof.GlobalWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- All warm K vectors of an observed round use the observed peer's launch-backed cache row. -/
theorem warmKeyPacketSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g src j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (pair : Fin 16) (upper : Bool) {sp : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) = some
      ⟨packetPlanePc (recurringPacketSite 0) pair upper, .copy sp⟩)
    (hFirst : ((X.tr (warpLane l g src)).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val + 2) :
    let co := assignedCoordinates p batch (g / l.block)
    let sender := warpLane l g (warmKShuffleSender src pair)
    let row := warmKInputRow (Mma.trips p batch co.1 - 2 - iteration) (sender % l.block) pair
    let tid := warpLane l g src % l.block
    sp.src.loc = p.kLayout.loc (primingScratchPage p batch row) (co.2 / 6) (row % 16)
        (kvCopyColumn tid upper) ∧
      ∀ k < sp.src.size,
        (p.kLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
        (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
        ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) := by
  obtain ⟨pos, ending, s, hBefore, hs, hr, hRank⟩ :=
    warmRoundKeyPairBroadcastOfEvent hp hX hFrame hg hw hSrc hCTA hb hLo hHi pair upper he hFirst
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g src
  let sender := warpLane l g (warmKShuffleSender src pair)
  let tid := thread % l.block
  let head := co.2 / 6
  let row := warmKInputRow (Mma.trips p batch co.1 - 2 - iteration) (sender % l.block) pair
  let page := primingScratchPage p batch row
  let ptr := primingKRowPointer p batch head row
  let col := kvCopyColumn tid upper
  let loc := p.kLayout.loc page head (row % 16) col
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : head < p.kvHeads := by dsimp [head, co]; unfold Params.heads at hHead; omega
  have hPage : page < p.pages := primingScratchPageBound hp hb
  have hRow : row % 16 < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hPtr, hFit, _⟩ := sourceScratchPayload_live hp 0 hPage hRow hh
  rw [hPtr] at hFit
  have hAddress := warmKPairSourceOfTrace (base := ptr) hFit pair upper hs hr hBefore he
    (hFirst.trans hRank.symm)
  have hRegion : p.kLayout.region p.pages p.kvHeads ∈ p.inputRegions := by
    simp [Params.inputRegions]
  have hRange := hp.ranges (p.kLayout.region p.pages p.kvHeads) (by simp [hRegion])
  have hCol := kvCopyColumn_byte_lt (lane := tid) upper (byte := 0) (by decide)
  have hLoc : (p.kLayout.region p.pages p.kvHeads).Contains loc := by
    simpa [loc, Loc.at] using (CacheLayout.loc_copy_in_region (c := p.kLayout) hPage hh hRow hCol)
  have hAddr : loc.addr < 2 ^ 64 := hLoc.2.2.2.trans_le hRange
  have hSum : ptr + 16 * (tid % 8) + packetSrcOff upper = loc.addr := by
    unfold ptr primingKRowPointer
    cases upper <;>
      simp [loc, col, page, CacheLayout.loc, kvCopyColumn, packetSrcOff, globalLoc] <;> omega
  rw [hSum, Nat.mod_eq_of_lt hAddr] at hAddress
  have hSource : sp.src.loc = loc := hAddress
  refine ⟨hSource, ?_⟩
  intro k hk
  have hShape := actualCopyShape hX (show X.Copy (thread, j) sp from ⟨_, he⟩)
  have hSize := hShape.srcSize.trans_eq hShape.widthEq
  have hByte := kvCopyColumn_byte_lt (lane := tid) upper (show k < 16 by omega)
  rw [hSource]
  have hIn := CacheLayout.loc_copy_in_region (c := p.kLayout) hPage hh hRow hByte
  have hInit : ∃ value, m (loc.at k) = some (some value) := by
    unfold loc
    rw [p.kLayout.loc_copy_byte]
    have hByte16 : k % 2 < 2 := Nat.mod_lt _ (by decide)
    exact ⟨_, (hp.kvBytes page hPage head hh (row % 16) hRow (col + k / 2) hByte).1 _
      (by simp [Value.bytes, FloatFmt.bytes]; omega)⟩
  exact ⟨hIn, hInit, fun w a data hm => hFrame.input_unwritten hp hRegion hIn hm⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
