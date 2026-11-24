-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness
import Kernels.TmlFa4Fwd.Proof.LoaderInputDescriptors
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCoverage
import Lemmas.Tensor.BoxWrite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader (actualInputIssuePc actualInputBoxAt inputSite loaderTensorOffset
  inputBarrierBase)

private theorem queryBoxByte {p : Params} {s : TensorCopy.Spec} {loc : Loc} {x y byte : Nat}
    (hMap : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩)
    (hWrite : TensorCopy.writeLoc s x y byte = some loc) :
    x < 64 ∧ y < 128 ∧ byte < 2 ∧
      loc = s.sharedBase.at
        (TensorSwizzle.offset .b128 s.sharedBase.addr (128 * y + 2 * x + byte)) := by
  rcases s with ⟨⟨outer, descriptor, origin, base, rows⟩, mbar, cluster, group⟩
  change (⟨outer, descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩ at hMap
  cases hMap
  let s : TensorCopy.Spec := ⟨⟨2, p.qMap, origin, base, rows⟩, mbar, cluster, group⟩
  change TensorCopy.writeLoc s x y byte = some loc at hWrite
  have hWidth : TensorTile.count p.qMap.box 0 = 64 := by
    norm_num [Params.qMap, TensorTile.count, TensorTile.step]
  have hRows : TensorTile.rows p.qMap.box = 128 := by
    norm_num [Params.qMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
  obtain ⟨hx, hy, hb⟩ := TensorCopy.writeLoc_bounds hWrite
  change x < TensorTile.count p.qMap.box 0 at hx
  change y < TensorTile.rows p.qMap.box at hy
  rw [hWidth] at hx
  rw [hRows] at hy
  have hByte : byte < 2 := hb
  let slot : TensorTransfer.Slot s.descriptor :=
    ⟨⟨x, hWidth.symm ▸ hx⟩, ⟨y, hRows.symm ▸ hy⟩, ⟨byte, hb⟩⟩
  rw [TensorCopy.writeLoc, TensorCopy.slotAt_self slot, Option.map_some] at hWrite
  obtain rfl := Option.some.inj hWrite.symm
  refine ⟨hx, hy, hByte, ?_⟩
  have hPitch : TensorTile.rowBytes p.qMap.box 2 .b128 = 128 := by
    simp [TensorTile.rowBytes, hWidth, TensorTile.swizzleWidth]
  change base.at (TensorSwizzle.offset .b128 base.addr
    (TensorTile.linearByte p.qMap.box 2 .b128 x y byte)) = _
  unfold TensorTile.linearByte
  rw [hPitch, show y * 128 + x * 2 + byte = 128 * y + 2 * x + byte by omega]

/-- The selected query byte belongs to one physical 16 KiB plane and its issuing CTA. -/
theorem querySubboxWriteRange {p : Params} {l : Launch} {X : Execution}
    {source : EvId} {stage plane : Fin 2} {s : TensorCopy.Spec}
    (hBox : QuerySubbox p l X source stage plane s)
    {x y byte : Nat} {loc : Loc} (hWrite : TensorCopy.writeLoc s x y byte = some loc) :
    loc.space = .shared ∧ loc.cta = source.1 / l.block ∧
      l.sharedBase + 3072 + 32768 * stage.val + 16384 * plane.val ≤ loc.addr ∧
      loc.addr < l.sharedBase + 3072 + 32768 * stage.val + 16384 * plane.val + 16384 := by
  obtain ⟨hx, hy, hb, hLoc⟩ := queryBoxByte hBox.2.2.2.1 hWrite
  rw [hBox.2.2.1] at hLoc
  rw [hLoc]
  have hOffset := TensorCopy.box_offset_lt (base := Mma.qStart l stage + 16384 * plane.val)
    hx hy hb
  unfold Mma.qStart at hOffset
  simp only [Loc.at, Mma.qStart]
  exact ⟨trivial, trivial, by omega, by omega⟩

private theorem querySubboxOfWriteBelowRing {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {source : EvId} {addr x y byte : Nat} {s : TensorCopy.Spec} {loc : Loc}
    (hIssue : X.TensorIssue source addr s) (hWrite : TensorCopy.writeLoc s x y byte = some loc)
    (hUpper : loc.addr < l.sharedBase + 68608) : ∃ stage plane,
      QuerySubbox p l X source stage plane s := by
  obtain ⟨_, he⟩ := hIssue
  obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
  have hBase := (actualInputBoxAt hp hX site he).2.2.2.1
  obtain ⟨slot, _, hAt⟩ := Option.map_eq_some_iff.mp hWrite
  have hLo : s.sharedBase.addr ≤ loc.addr := by
    rw [← hAt]
    exact Nat.le_add_right _ _
  rw [hBase] at hLo
  change l.sharedBase + (inputSite site).sharedOffset ≤ loc.addr at hLo
  have hCases : (∃ stage : Fin 2,
      inputBarrierBase site + (inputSite site).barrierOffset = 8 * stage.val) ∨
      166912 ≤ (inputSite site).sharedOffset := by
    fin_cases site <;> first | exact .inl ⟨0, rfl⟩ | exact .inl ⟨1, rfl⟩ | exact .inr (by decide)
  obtain ⟨stage, hOffset⟩ := hCases.resolve_right (by omega)
  have hObject := loaderTensorOffset hp hX site he
  rw [hOffset] at hObject
  obtain ⟨_, plane, hBox⟩ := querySubboxOfBarrier hp hX stage ⟨_, he⟩ hObject
  exact ⟨stage, plane, hBox⟩

/-- The same physical query byte can have only one tensor load writer and one slot. -/
theorem queryTensorWriterUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {source other : EvId} {stage plane : Fin 2} {s t : TensorCopy.Spec}
    (hBox : QuerySubbox p l X source stage plane s)
    {x y byte ox oy oby addr : Nat} {loc : Loc}
    (hWrite : TensorCopy.writeLoc s x y byte = some loc)
    (hOther : X.TensorIssue other addr t)
    (hOtherAt : TensorCopy.writeLoc t ox oy oby = some loc) :
    other = source ∧ ox = x ∧ oy = y ∧ oby = byte := by
  obtain ⟨_, hCta, hLo, hHi⟩ := querySubboxWriteRange hBox hWrite
  have hStage := stage.isLt
  have hPlane := plane.isLt
  obtain ⟨otherStage, otherPlane, hOtherBox⟩ :=
    querySubboxOfWriteBelowRing hp hX hOther hOtherAt (by omega)
  obtain ⟨_, hOtherCta, hOtherLo, hOtherHi⟩ := querySubboxWriteRange hOtherBox hOtherAt
  have hStage' := otherStage.isLt
  have hPlane' := otherPlane.isLt
  have hStages : otherStage = stage := Fin.ext (by omega)
  have hPlanes : otherPlane = plane := Fin.ext (by omega)
  subst otherStage otherPlane
  have hIssue := querySubboxUnique hp hX (hOtherCta.symm.trans hCta) hOtherBox hBox
  subst other
  obtain ⟨_, he⟩ := hOtherBox.1
  obtain ⟨_, he'⟩ := hBox.1
  have hs := (Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj (he.symm.trans he')))).2
  subst t
  obtain ⟨hx, _, hb, hLoc⟩ := queryBoxByte hBox.2.2.2.1 hWrite
  obtain ⟨hox, _, hob, hOtherLoc⟩ := queryBoxByte hBox.2.2.2.1 hOtherAt
  have hOffset := congrArg Loc.addr (hOtherLoc.symm.trans hLoc)
  change s.sharedBase.addr + TensorSwizzle.offset .b128 s.sharedBase.addr
      (128 * oy + 2 * ox + oby) =
    s.sharedBase.addr + TensorSwizzle.offset .b128 s.sharedBase.addr
      (128 * y + 2 * x + byte) at hOffset
  exact ⟨rfl, TensorCopy.box_offset_inj hox hob hx hb (Nat.add_left_cancel hOffset)⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
