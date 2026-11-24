-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSource
public import Kernels.TmlFa4Fwd.Proof.InputCopies
public import Lemmas.Tensor.BoxWrite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Epilogue Correction

/-- The Q box writes every shared byte of its 16 KiB allocation, including padded rows. -/
theorem queryBoxWriteLoc {p : Params} {s : TensorCopy.Spec} {offset : Nat}
    (hMap : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩)
    (hOffset : offset < 16384) :
    ∃ x y k, TensorCopy.writeLoc s x y k = some (s.sharedBase.at offset) := by
  rcases s with ⟨⟨outer, descriptor, origin, base, rows⟩, barrier, cluster, group⟩
  change (⟨outer, descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩ at hMap
  cases hMap
  obtain ⟨x, y, k, hx, hy, hk, hOff⟩ :=
    TensorCopy.box_writeLoc_surj (R := 128) (base := base.addr) (by omega : offset < 128 * 128)
  refine ⟨x, y, k, ?_⟩
  have hWidth : TensorTile.count p.qMap.box 0 = 64 := by
    norm_num [Params.qMap, TensorTile.count, TensorTile.step]
  have hRows : TensorTile.rows p.qMap.box = 128 := by
    norm_num [Params.qMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
  have hPitch : TensorTile.rowBytes p.qMap.box 2 .b128 = 128 := by
    simp [TensorTile.rowBytes, hWidth, TensorTile.swizzleWidth]
  let s : TensorCopy.Spec := ⟨⟨2, p.qMap, origin, base, rows⟩, barrier, cluster, group⟩
  let slot : TensorTransfer.Slot s.descriptor :=
    ⟨⟨x, hWidth.symm ▸ hx⟩, ⟨y, hRows.symm ▸ hy⟩, ⟨k, hk⟩⟩
  change TensorCopy.writeLoc s x y k = _
  have hSlot : TensorTransfer.slotAt s.descriptor x y k = some slot :=
    TensorCopy.slotAt_self slot
  rw [TensorCopy.writeLoc, hSlot, Option.map_some]
  congr 1
  change base.at (TensorSwizzle.offset .b128 base.addr
    (TensorTile.linearByte p.qMap.box 2 .b128 x y k)) = base.at offset
  unfold TensorTile.linearByte
  rw [hPitch, show y * 128 + x * 2 + k = 128 * y + 2 * x + k by omega, hOff]

/-- The stage-zero output element overlaps the query copy when both use the same subbox. -/
theorem queryBoxConflictsWithOutputElement {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {input writer : EvId}
    {address x y : Nat} {s : TensorCopy.Spec} {box : Fin 4} {data : List Byte}
    (hx : x < 32) (hy : y < 128) (hIssue : X.TensorIssue input address s)
    (hMap : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩)
    (hBase : s.sharedBase = sharedSlot l writer.1 0 box)
    (hWrite : X.Writes writer (outputElementAccess l writer.1 0 box x y) data) :
    ∃ qx qy k a loc, Conflict X (.async input (.write (.load qx qy k))) (.thread writer) a
        (outputElementAccess l writer.1 0 box x y) ∧
      ¬ a.SameFootprint (outputElementAccess l writer.1 0 box x y) ∧ a.Covers loc ∧
      (outputElementAccess l writer.1 0 box x y).Covers loc ∧
      TensorCopy.writeLoc s qx qy k = some loc := by
  let src := sharedSlot l writer.1 0 box
  let dst := outputElementAccess l writer.1 0 box x y
  let outBox := writebackStoreSpec p l writer.1 0 0 0 0 box
  have hByte : TensorStore.readLoc outBox x y 0 = some (dst.loc.at 0) :=
    writebackSourceAddress hp (issuer := writer.1) (writer := writer.1) rfl 0 box hx hy (by decide)
  obtain ⟨slot, _, hAt⟩ := Option.map_eq_some_iff.mp hByte
  obtain ⟨offset, hOffset, hLoc⟩ := writebackSlotSource p l writer.1 0 0 0 0 box slot
  have hEq : src.at offset = dst.loc.at 0 := hLoc.symm.trans hAt
  obtain ⟨qx, qy, k, hQuery⟩ := queryBoxWriteLoc hMap hOffset
  rw [hBase, hEq] at hQuery
  let a : Acc := {loc := dst.loc.at 0, size := 1}
  let part := AsyncCopy.Part.write (.load qx qy k)
  have hInput : X.Intent (.async input part) a true := ⟨rfl, _, address, hIssue, hQuery, rfl⟩
  have hOutput : X.Intent (.thread writer) dst true := .inr (.inl ⟨data, hWrite, rfl⟩)
  have ha : a.Covers (dst.loc.at 0) := ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩
  have hd : dst.Covers (dst.loc.at 0) := Acc.covers_at (show (0 : Nat) < 4 by decide)
  have hSize : ¬ a.SameFootprint dst := by
    intro h
    cases h.2
  exact ⟨qx, qy, k, a, dst.loc.at 0,
    ⟨(by intro h; cases h), true, true, hInput, hOutput, .inl rfl, _, ha, hd⟩,
    hSize, ha, hd, hQuery⟩

end PTX.Kernels.TmlFa4Fwd.Safety
