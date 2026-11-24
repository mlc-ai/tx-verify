-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPacket

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- An actual warm K vector with the selected request, visit, and pair. -/
def WarmKeyVector (p : Params) (l : Launch) (X : Execution) (i : EvId)
    (batch iteration : Nat) (pair : Fin 16) (upper : Bool) (sp : AsyncCopy.Spec) : Prop :=
  tilePrefix p batch * p.heads ≤ i.1 / l.block ∧
  i.1 / l.block < tilePrefix p (batch + 1) * p.heads ∧
  X.get i = some ⟨packetPlanePc (recurringPacketSite 0) pair upper, .copy sp⟩ ∧
  ((X.tr i.1).take i.2).countP Execution.isShfl =
    primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val + 2

theorem WarmKeyVector.copy {p : Params} {l : Launch} {X : Execution} {i : EvId}
    {batch iteration : Nat} {pair : Fin 16} {upper : Bool} {sp : AsyncCopy.Spec}
    (h : WarmKeyVector p l X i batch iteration pair upper sp) : X.Copy i sp :=
  ⟨_, h.2.2.1⟩

/-- Both physical vectors of each pair read their launch-backed K cache row. -/
theorem WarmKeyVector.source {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j batch iteration : Nat} {pair : Fin 16} {upper : Bool} {sp : AsyncCopy.Spec}
    (hb : batch < p.batch)
    (hWarp : 14 ≤ warpIndex l g) (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (h : WarmKeyVector p l X (g, j) batch iteration pair upper sp) :
    let co := assignedCoordinates p batch (g / l.block)
    let tile := Mma.trips p batch co.1 - 2 - iteration
    let tid := g % l.block
    let row := kvCopyRow tile tid pair.val
    sp.src.loc = p.kLayout.loc (primingScratchPage p batch row) (co.2 / 6) (row % 16)
        (kvCopyColumn tid upper) ∧
      ∀ k < sp.src.size,
        (p.kLayout.region p.pages p.kvHeads).Contains (sp.src.loc.at k) ∧
        (∃ byte, m (sp.src.loc.at k) = some (some byte)) ∧
        ∀ w a data, X.MemWrites w a data → ¬ a.Covers (sp.src.loc.at k) := by
  let src := laneOf l g
  let warp := warpIndex l g
  let senderLane := warmKShuffleSender src pair
  let sender := warpLane l g senderLane
  let co := assignedCoordinates p batch (g / l.block)
  let tile := Mma.trips p batch co.1 - 2 - iteration
  have hSelf : warpLane l g src = g := by
    unfold warpLane src laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hg : g < l.threads := event_thread_lt hX h.2.2.1
  have hSrc : src < 32 := Nat.mod_lt _ (by decide)
  have hSender : senderLane < 32 := by
    unfold senderLane warmKShuffleSender pointerBroadcastLane
    omega
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hWarpEq : warpIndex l sender = warp := (Step.sameWarp_lane hBlock hg hSender).1.2.symm
  have hLaneEq : laneOf l sender = senderLane := (Step.sameWarp_lane hBlock hg hSender).2
  have hSenderTid : sender % l.block = 32 * warp + senderLane := by
    unfold warpIndex at hWarpEq
    unfold laneOf at hLaneEq
    omega
  have hTid : g % l.block = 32 * warp + src := by
    unfold warp warpIndex src laneOf
    omega
  have hPair : (if pair.val < 8 then 0 else 64) = 64 * (pair.val / 8) := by
    have := pair.isLt
    split <;> omega
  have hRow : warmKInputRow tile (sender % l.block) pair =
      kvCopyRow tile (g % l.block) pair.val := by
    rw [warmKInputRow, hPair, hSenderTid, hTid]
    simpa only [senderLane, warmKShuffleSender, Nat.add_assoc] using
      kvCopyRow_of_pointerLane tile warp src pair.val
  have facts := warmKeyPacketSource hp hX hFrame hg hWarp hSrc hb h.1 h.2.1 hCTA pair upper
    (sp := sp) (j := j) (by rw [hSelf]; exact h.2.2.1) (by rw [hSelf]; exact h.2.2.2)
  change sp.src.loc = p.kLayout.loc (primingScratchPage p batch
      (warmKInputRow tile (sender % l.block) pair)) (co.2 / 6)
      (warmKInputRow tile (sender % l.block) pair % 16)
      (kvCopyColumn (warpLane l g src % l.block) upper)
    ∧ _ at facts
  rw [hRow, hSelf] at facts
  exact facts

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
