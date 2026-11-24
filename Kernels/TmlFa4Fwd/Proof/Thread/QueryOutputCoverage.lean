-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQueryCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits
import Lemmas.Tensor.BoxWrite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Mma

/-- The two decodes select a plane within the stage, then the fragment within that plane. -/
def correctionQueryPlane (subbox : Fin 4) : Fin 2 := ⟨subbox.val % 2, Nat.mod_lt _ (by decide)⟩

/-- This bank records actual earlier fragment issues and their query acquire for a commit.
Each fragment carries only the descriptor fields needed for its physical A footprint. -/
def QueryBankBeforeOutput (l : Launch) (X : Execution) (commit : EvId) (stage : Fin 2) : Prop :=
  ∃ wait e, X.get wait = some e ∧
    e.kind = .wait (Output.queryObject l (wait.1 / l.block) stage) 0 true true .cta ∧
    ∀ step : Fin 8, ∃ mma d op accum mask, X.MmaIssue mma d op accum mask ∧
      mma.1 = commit.1 ∧ mma.2 < commit.2 ∧ TraceBefore X wait mma ∧
      QueryOperandFragment l mma.1 stage step op

private theorem queryWriteInBox {p : Params} {s : TensorCopy.Spec} {x y byte : Nat}
    {loc : Loc}
    (hMap : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩)
    (hByte : TensorCopy.writeLoc s x y byte = some loc) : s.sharedBase.InRange 16384 loc := by
  rcases s with ⟨⟨outer, descriptor, origin, base, rows⟩, barrier, cluster, group⟩
  change (⟨outer, descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩ at hMap
  cases hMap
  let box : TensorCopy.Spec := ⟨⟨2, p.qMap, origin, base, rows⟩, barrier, cluster, group⟩
  have hWidth : TensorTile.count p.qMap.box 0 = 64 := by
    norm_num [Params.qMap, TensorTile.count, TensorTile.step]
  have hHeight : TensorTile.rows p.qMap.box = 128 := by
    norm_num [Params.qMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
  obtain ⟨hx, hy, hb⟩ := TensorCopy.writeLoc_bounds hByte
  change x < TensorTile.count p.qMap.box 0 at hx
  change y < TensorTile.rows p.qMap.box at hy
  change byte < 2 at hb
  rw [hWidth] at hx
  rw [hHeight] at hy
  let slot : TensorTransfer.Slot box.descriptor :=
    ⟨⟨x, hWidth.symm ▸ hx⟩, ⟨y, hHeight.symm ▸ hy⟩, ⟨byte, hb⟩⟩
  have hs : TensorTransfer.slotAt box.descriptor x y byte = some slot :=
    TensorCopy.slotAt_self slot
  change TensorCopy.writeLoc box x y byte = some loc at hByte
  rw [TensorCopy.writeLoc, hs, Option.map_some] at hByte
  obtain rfl := Option.some.inj hByte.symm
  have hBound := TensorCopy.box_offset_lt (base := base.addr) hx hy hb
  have hOffset : (box.sharedLoc slot).addr =
      base.addr + TensorSwizzle.offset .b128 base.addr (128 * y + 2 * x + byte) := by
    have hPitch : TensorTile.rowBytes p.qMap.box 2 .b128 = 128 := by
      simp [TensorTile.rowBytes, hWidth, TensorTile.swizzleWidth]
    change base.addr + TensorSwizzle.offset .b128 base.addr
      (TensorTile.linearByte p.qMap.box 2 .b128 x y byte) = _
    simp only [TensorTile.linearByte, hPitch]
    congr 2
    omega
  change base.InRange 16384 (box.sharedLoc slot)
  exact ⟨rfl, rfl, by rw [hOffset]; omega, by rw [hOffset]; omega⟩

private theorem outputByteInBox {l : Launch} {writer x row k : Nat} {stage : Fin 2}
    {subbox : Fin 4} (hx : x < 32) (hy : row < 128) (hk : k < 4) :
    (sharedSlot l writer stage subbox).InRange 16384
      ((outputElementAccess l writer stage subbox x row).loc.at k) := by
  have hXor : x / 4 ^^^ (row % 8) < 2 ^ 3 := Nat.xor_lt_two_pow (by omega) (by omega)
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [outputElementAccess, outputChunkLoc, Loc.at] <;> omega

/-- An overlapping pending Q byte and ordinary correction footprint must use the same physical
plane in the same CTA. Stage-one correction boxes cannot overlap either input Q bank. -/
theorem querySubboxOfCorrectionOverlap {p : Params} {l : Launch} {X : Execution}
    {input : EvId} {writer qx qy qbyte x row : Nat} {spec : TensorCopy.Spec} {loc : Loc}
    {qStage correctionStage plane : Fin 2} {subbox : Fin 4}
    (hBox : Loader.QuerySubbox p l X input qStage plane spec)
    (hQuery : TensorCopy.writeLoc spec qx qy qbyte = some loc)
    (hx : x < 32) (hy : row < 128)
    (hCover : (outputElementAccess l writer correctionStage subbox x row).Covers loc) :
    correctionStage = 0 ∧ qStage = correctionQueryStage subbox ∧
      plane = correctionQueryPlane subbox ∧ input.1 / l.block = writer / l.block ∧
      ∃ k < 4, loc = (outputElementAccess l writer correctionStage subbox x row).loc.at k := by
  let dst := outputElementAccess l writer correctionStage subbox x row
  change dst.Covers loc at hCover
  let k := loc.addr - dst.loc.addr
  have hk : k < 4 := by
    have hLo := hCover.2.2.1
    have hHi := hCover.2.2.2
    change loc.addr < dst.loc.addr + 4 at hHi
    dsimp [k]
    omega
  have hLoc : loc = dst.loc.at k := by
    have hAddr : loc.addr = dst.loc.addr + k := by
      have := hCover.2.2.1
      dsimp [k]
      omega
    have hSpace := hCover.1
    have hOwner := hCover.2.1
    rcases loc with ⟨space, owner, addr⟩
    cases hDst : dst.loc
    simp only [hDst, Loc.at, Loc.mk.injEq] at hSpace hOwner hAddr ⊢
    exact ⟨hSpace, hOwner, hAddr⟩
  have hQ := queryWriteInBox hBox.2.2.2.1 hQuery
  rw [hBox.2.2.1] at hQ
  have hOut := outputByteInBox (l := l) (writer := writer) (stage := correctionStage)
    (subbox := subbox) hx hy hk
  change (sharedSlot l writer correctionStage subbox).InRange 16384 (dst.loc.at k) at hOut
  rw [← hLoc] at hOut
  have hCta := hQ.2.1.symm.trans hOut.2.1
  have hQlo := hQ.2.2.1
  have hQhi := hQ.2.2.2
  change l.sharedBase + 3072 + 32768 * qStage.val + 16384 * plane.val ≤ loc.addr at hQlo
  change loc.addr < l.sharedBase + 3072 + 32768 * qStage.val + 16384 * plane.val + 16384 at hQhi
  have hOlo := hOut.2.2.1
  have hOhi := hOut.2.2.2
  change l.sharedBase + (3072 + 65536 * correctionStage.val + 16384 * subbox.val) ≤ loc.addr at hOlo
  change loc.addr < l.sharedBase + (3072 + 65536 * correctionStage.val + 16384 * subbox.val) +
    16384 at hOhi
  have hs := qStage.isLt
  have hc := correctionStage.isLt
  have hPlane := plane.isLt
  have hSub := subbox.isLt
  have hIndex : 4 * correctionStage.val + subbox.val = 2 * qStage.val + plane.val := by omega
  refine ⟨Fin.ext (by omega), Fin.ext ?_, Fin.ext ?_, hCta, k, hk, hLoc⟩
  · change qStage.val = subbox.val / 2
    omega
  · change plane.val = subbox.val % 2
    omega

end PTX.Kernels.TmlFa4Fwd.Thread
