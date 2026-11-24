-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Epilogue
public import Kernels.TmlFa4Fwd.Proof.OutputSlotSource
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
public import Kernels.TmlFa4Fwd.Proof.ResultGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX Epilogue

variable {p : Params} {l : Launch} {m : Mem0}

/-- An in-bounds writeback byte determines the box and its coordinates within that box. -/
theorem writebackByteCoordinates (hp : Pre p l m) {g batch head tile x y k : Nat} {stage : Fin 2}
    {box : Fin 4} {loc : Loc} (hb : batch < p.batch) (hh : head < p.heads)
    (hWrite : TensorStore.writeLoc (writebackStoreSpec p l g batch head tile stage box) x y k =
      some loc) :
    x < 32 ∧ y < 128 ∧ k < 4 ∧ stageRow tile stage + y < p.qLength batch ∧
      loc = (p.oLoc (p.qOffset batch + stageRow tile stage + y) head (32 * box.val + x)).at k := by
  rw [writebackWriteLoc hp stage box x y k hb hh] at hWrite
  split at hWrite
  · rename_i hIn
    obtain ⟨hx, hy, hk, hr⟩ := hIn
    exact ⟨hx, hy, hk, hr, by simpa only [Nat.add_assoc] using (Option.some.inj hWrite).symm⟩
  · cases hWrite

/-- Two writes to the same packed O byte agree in their request, tile, stage, box and byte. -/
theorem sameWritebackByte (hp : Pre p l m) {g batch head tile x y k : Nat} {stage : Fin 2}
    {box : Fin 4} {g' batch' head' tile' x' y' k' : Nat} {stage' : Fin 2} {box' : Fin 4} {loc : Loc}
    (hb : batch < p.batch) (hh : head < p.heads) (hb' : batch' < p.batch) (hh' : head' < p.heads)
    (hWrite : TensorStore.writeLoc (writebackStoreSpec p l g batch head tile stage box) x y k =
      some loc)
    (hWrite' :
      TensorStore.writeLoc (writebackStoreSpec p l g' batch' head' tile' stage' box') x' y' k' =
        some loc) :
    batch = batch' ∧ head = head' ∧ tile = tile' ∧ stage = stage' ∧ box = box' ∧
      x = x' ∧ y = y' ∧ k = k' := by
  obtain ⟨hx, hy, hk, hr, hLoc⟩ := writebackByteCoordinates hp hb hh hWrite
  obtain ⟨hx', hy', hk', hr', hLoc'⟩ := writebackByteCoordinates hp hb' hh' hWrite'
  have hs := stage.isLt
  have hs' := stage'.isLt
  have hBox := box.isLt
  have hBox' := box'.isLt
  obtain ⟨hRow, hHead, hColumn, hByte⟩ := outputByte_inj hh hh' (by omega) (by omega)
    hk hk' (hLoc.symm.trans hLoc')
  rw [Nat.add_assoc, Nat.add_assoc] at hRow
  obtain ⟨hBatch, hWithin⟩ := hp.packedRow_inj hb hb' hr hr' hRow
  dsimp [stageRow] at hWithin
  exact ⟨hBatch, hHead, by omega, Fin.ext (by omega), Fin.ext (by omega),
    by omega, by omega, hByte⟩

/-- Covering TMA writes to an output byte originate in one scheduler CTA. -/
theorem sameOutputByteSameCta {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i j : EvId}
    {address address' x y k x' y' k' : Nat} {spec spec' : TensorStore.Spec} {loc : Loc}
    (hIssue : X.TensorStoreIssue i address spec) (hIssue' : X.TensorStoreIssue j address' spec')
    (hWrite : TensorStore.writeLoc spec x y k = some loc)
    (hWrite' : TensorStore.writeLoc spec' x' y' k' = some loc) :
    i.1 / l.block = j.1 / l.block := by
  obtain ⟨batch, hBatch, stage, box, hLo, hHi, rfl⟩ :=
    OutputWarp.issuedAssignment hp hX hIssue
  obtain ⟨batch', hBatch', stage', box', hLo', hHi', rfl⟩ :=
    OutputWarp.issuedAssignment hp hX hIssue'
  have hh := (assignedCoordinates_valid hp hLo hHi).2
  have hh' := (assignedCoordinates_valid hp hLo' hHi').2
  obtain ⟨rfl, hHead, hTile, _⟩ := sameWritebackByte hp hBatch hh hBatch' hh' hWrite hWrite'
  let tiles := requestTiles p batch
  let width := sectionWidth tiles p.heads
  let base := tilePrefix p batch * p.heads
  have hWidth : 0 < width := sectionWidth_pos (Nat.zero_lt_of_lt hh)
  have hi : i.1 / l.block - base < tiles * p.heads := by
    rw [tilePrefix_succ, Nat.add_mul] at hHi
    dsimp [base, tiles]
    omega
  have hj : j.1 / l.block - base < tiles * p.heads := by
    rw [tilePrefix_succ, Nat.add_mul] at hHi'
    dsimp [base, tiles]
    omega
  have hItem := (sectionItem_coords hWidth hi).2.2
  have hItem' := (sectionItem_coords hWidth hj).2.2
  change sectionItem tiles p.heads width (assignedCoordinates p batch (i.1 / l.block)).1
    (assignedCoordinates p batch (i.1 / l.block)).2 = i.1 / l.block - base at hItem
  change sectionItem tiles p.heads width (assignedCoordinates p batch (j.1 / l.block)).1
    (assignedCoordinates p batch (j.1 / l.block)).2 = j.1 / l.block - base at hItem'
  rw [hTile, hHead, hItem'] at hItem
  dsimp [base] at hItem
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
