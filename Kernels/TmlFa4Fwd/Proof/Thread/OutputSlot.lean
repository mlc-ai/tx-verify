-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadyHistory
public import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlotGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction (outputElementAccess outputStorePc rowOf)

noncomputable section

private theorem outputReadLocOfBox {p : Params} {l : Launch} {g : Nat}
    {stage : Fin 2} {box : Fin 4} {spec : TensorStore.Spec}
    (hMap : (⟨spec.outer, spec.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨3, p.oMap⟩)
    (hBase : spec.sharedBase = sharedSlot l g stage box) (x y k : Nat) :
    TensorStore.readLoc spec x y k =
      TensorStore.readLoc (writebackStoreSpec p l g 0 0 0 stage box) x y k := by
  rcases spec with ⟨⟨outer, desc, origin, base, rows⟩, reduce⟩
  simp only [Sigma.mk.injEq] at hMap
  obtain ⟨rfl, hDesc⟩ := hMap
  have hEq : desc = p.oMap := eq_of_heq hDesc
  subst desc
  change base = sharedSlot l g stage box at hBase
  subst base
  rfl

private theorem outputReadBounds {p : Params} {l : Launch} {g x y k : Nat}
    {stage : Fin 2} {box : Fin 4} {loc : Loc}
    (h : TensorStore.readLoc (writebackStoreSpec p l g 0 0 0 stage box) x y k = some loc) :
    x < 32 ∧ y < 128 ∧ k < 4 := by
  unfold TensorStore.readLoc TensorTransfer.slotAt at h
  have hx : TensorTile.count p.oMap.box 0 = 32 := by
    simp [Params.oMap, TensorTile.count, TensorTile.step]
  have hy : TensorTile.rows p.oMap.box = 128 := by
    simp [Params.oMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
  have hk : p.oMap.format.bytes = 4 := rfl
  have hBounds := Option.map_eq_some_iff.mp h
  obtain ⟨slot, hSlot, _⟩ := hBounds
  have hAt : TensorTransfer.slotAt p.oMap x y k = some slot := hSlot
  unfold TensorTransfer.slotAt at hAt
  split_ifs at hAt
  exact ⟨by simpa only [hx] using ‹x < TensorTile.count p.oMap.box 0›,
    by simpa only [hy] using ‹y < TensorTile.rows p.oMap.box›,
    by simpa only [hk] using ‹k < p.oMap.format.bytes›⟩

/-- A pending O source slot names one exact correction element and the stage the issuer acquired. -/
theorem actualReadySlot {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {address x y k : Nat} {spec : TensorStore.Spec} {loc : Loc}
    (hIssue : X.TensorStoreIssue i address spec)
    (hRead : TensorStore.readLoc spec x y k = some loc) :
    ∃ (stage : Fin 2) (box : Fin 4), ReadyAcquire l X i stage ∧
      x < 32 ∧ y < 128 ∧ k < 4 ∧
      loc = (outputElementAccess l (sourceLane l i y) stage box x y).loc.at k := by
  obtain ⟨_, hMap, stage, box, hBase, hReady⟩ := OutputWarp.readyBox hp hX hIssue
  have hSame := outputReadLocOfBox hMap hBase x y k
  rw [hSame] at hRead
  obtain ⟨hx, hy, hk⟩ := outputReadBounds hRead
  have hOwner : sourceLane l i y / l.block = i.1 / l.block := by
    unfold sourceLane
    rw [hp.block]
    omega
  exact ⟨stage, box, hReady, hx, hy, hk,
    Option.some.inj (hRead.symm.trans
      (Correction.writebackSourceAddress hp hOwner stage box hx hy hk))⟩

private theorem actualStagingWriter {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {data : List Byte} (h : Correction.StagingWrite X (.thread i) a data) :
    ∃ (stage : Fin 2) (box : Fin 4) (x : Nat), x < 32 ∧
      a = outputElementAccess l i.1 stage box x (rowOf l i.1) ∧
      StageStagingWrite X i stage a data ∧ 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
  obtain ⟨stage, box, chunk, he⟩ := h.decoded
  obtain ⟨elem, hAccess⟩ := Correction.stagingWriteElement hp hX stage box chunk he
  have hBounds : 8492 ≤ outputStorePc stage box chunk ∧ outputStorePc stage box chunk < 9201 :=
    (by decide : ∀ (s : Fin 2) (b : Fin 4) (c : Fin 8),
      8492 ≤ outputStorePc s b c ∧ outputStorePc s b c < 9201) stage box chunk
  have hHint : outputStorePc stage box chunk ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he
    (show 173 < outputStorePc stage box chunk from by omega) hHint
  change roleBodyPc (warpIndex l i.1) (outputStorePc stage box chunk) at hRole
  have hWarp : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hRange
    · omega
    · split_ifs at hRange <;> omega
  have hc := chunk.isLt
  have helem := elem.isLt
  exact ⟨stage, box, _, by omega, hAccess, StageStagingWrite.ofEvent box chunk he, hWarp⟩

/-- A staging write covering the output byte belongs to its exact lane and element. -/
theorem stagingWriterOfSlot {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue writer : EvId} {stage : Fin 2} {box : Fin 4} {x y k : Nat} {loc : Loc}
    {a : Acc} {data : List Byte} (hx : x < 32) (hy : y < 128) (hk : k < 4)
    (hLoc : loc = (outputElementAccess l (sourceLane l issue y) stage box x y).loc.at k)
    (hWrite : Correction.StagingWrite X (.thread writer) a data) (hCover : a.Covers loc) :
    writer.1 = sourceLane l issue y ∧ a = outputElementAccess l writer.1 stage box x y ∧
      StageStagingWrite X writer stage a data := by
  obtain ⟨writeStage, writeBox, col, hCol, rfl, hStage, hLower, hUpper⟩ :=
    actualStagingWriter hp hX hWrite
  have hDst : (outputElementAccess l (sourceLane l issue y) stage box x y).Covers loc :=
    hLoc.symm ▸ Acc.covers_at hk
  obtain ⟨hSame, hStages, hBoxes, hRow, hColumn⟩ := sameNormalizedElementOfCover hx hCol hy
    (Nat.mod_lt _ (by decide)) hDst hCover
  subst writeStage
  have hOwner : sourceLane l issue y / l.block = issue.1 / l.block := by
    unfold sourceLane
    rw [hp.block]
    omega
  have hG : sourceLane l issue y = writer.1 := by
    have hCta := hOwner.symm.trans hSame
    have hParts := Nat.div_add_mod writer.1 l.block
    unfold sourceLane rowOf warpIndex at *
    rw [hp.block] at *
    omega
  subst writeBox col
  change y = rowOf l writer.1 at hRow
  exact ⟨hG.symm, by rw [hRow], hStage⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Output
