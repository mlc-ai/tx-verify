-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundValueBroadcast
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmFirstCopyBacking
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation
import Kernels.TmlFa4Fwd.Proof.GlobalWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- The first pair of any warm V packet reads bytes initialized by the launch,
even in an unfinished prefix where its asynchronous effect has yet to run. -/
theorem warmRoundFirstValueCopyBacked {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g src j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (upper : Bool) {sp : AsyncCopy.Spec}
    (he : X.get (warpLane l g src, j) = some
      ⟨packetPlanePc (recurringPacketSite 1) 0 upper, .copy sp⟩)
    (hFirst : ((X.tr (warpLane l g src)).take j).countP Execution.isShfl =
      primingSearchShuffleCount batch + 64 + 64 * iteration + 32 + 2) :
    let co := assignedCoordinates p batch (g / l.block)
    let sender := warpLane l g (pointerBroadcastLane src)
    let row := primingLaneRow (Mma.trips p batch co.1 - 2 - iteration) (sender % l.block)
    let tid := warpLane l g src % l.block
    sp.src.loc = p.vLayout.loc (primingScratchPage p batch row) (co.2 / 6) (row % 16)
        (kvCopyColumn tid upper) ∧
      ∀ k < sp.src.size,
        (p.vLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
        (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
        ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) := by
  let target : Event := ⟨packetPlanePc (recurringPacketSite 1) 0 upper, .copy sp⟩
  have hTarget : X.get (warpLane l g src, j) = some target := he
  obtain ⟨index, ending, s, hOrder, hs, hr, hRank⟩ :=
    warmRoundValueBroadcastOfEvent hp hX hFrame hg hw hSrc hCTA hb hLo hHi upper he hFirst
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g src
  let sender := warpLane l g (pointerBroadcastLane src)
  let row := primingLaneRow (Mma.trips p batch co.1 - 2 - iteration) (sender % l.block)
  let tid := thread % l.block
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by dsimp [co]; unfold Params.heads at hHead; omega
  have hTid : tid < 512 := by
    unfold tid
    rw [hp.block]
    exact Nat.mod_lt _ (by decide)
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hr
  have hObserved : ((X.tr thread).drop (index + 2))[j - (index + 2)]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hOrder]
    exact hTarget
  have hCount : (((X.tr thread).drop (index + 2)).take (j - (index + 2))).countP
      Execution.isShfl = 0 := by
    have hTotal := hFirst
    have hSplit : j = index + 2 + (j - (index + 2)) := (Nat.add_sub_of_le hOrder).symm
    change ((X.tr thread).take j).countP Execution.isShfl = _ at hTotal
    change ((X.tr thread).take (index + 2)).countP Execution.isShfl = _ at hRank
    rw [hSplit, List.take_add, List.countP_append, hRank] at hTotal
    omega
  have hSaw : target ∈ loaderSliceEvents 1241 (copyCommitPc (recurringPacketSite 1)) visits := by
    apply loaderEventInRankedSlice (cut := 1250) (by decide) (by decide)
      (fun _ => by kernel_rfl) (by kernel_rfl) hWalk
      (by rw [hs.1]; decide) (ringShapeOfAt hs) hObserved
    rw [hs.1, hCount, show loaderShuffleTail 1250 1241 = 1 by kernel_rfl]
    decide
  have hInput : At s (recurringSourceStart 1) (recurringSourceInputs 1
      ((recurringCache p 1).loc (primingScratchPage p batch row) (co.2 / 6) (row % 16) 0).addr
      tid) := by
    apply hs.mono
    exact ⟨holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl,
      holds_lookup hs.2.2.2.2 rfl, trivial⟩
  have hShape := actualCopyShape hX (show X.Copy (thread, j) sp from ⟨_, he⟩)
  have hSize := hShape.srcSize.trans_eq hShape.widthEq
  exact recurringFirstCopyBackedByPointer hp hFrame hb hh hTid 1 upper hInput hWalk hSaw hSize

end
end PTX.Kernels.TmlFa4Fwd.Loader
