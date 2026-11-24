-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.InputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Lemmas.Tensor.LoadWritten
public import Lemmas.Tensor.TensorCompleteConsistentRead
public import Lemmas.Step.TensorDrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX

noncomputable section

/-- A notified input tile has written each byte, including the descriptor fill at an
out-of-bounds coordinate. A backed byte comes from the immutable launch input. -/
private theorem notifiedInputByte {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l Decoded.kernel A m X)
    {i : EvId} {o : TensorCopy.Observation} (ho : X.tensor i = some o)
    (hNotify : o.effects.notified = true) (slot : TensorTransfer.Slot o.spec.descriptor)
    {value : Byte}
    (hBacked : ∀ address, o.spec.globalAddress slot = some address →
      m (globalLoc address) = some (some value) ∧
      ∀ w a bs, X.MemWrites w a bs → ¬ a.Covers (globalLoc address))
    (hFill : o.spec.globalAddress slot = none →
      (TensorCopy.Content.filled o.spec.descriptor.fill o.spec.descriptor.format slot.2.2.val).byte
        = some value) :
    X.MemWrites (.async i (.write (.load slot.1.val slot.2.1.val slot.2.2.val)))
      {loc := o.spec.sharedLoc slot, size := 1} [value] := by
  obtain ⟨⟨addr, hIssue⟩, hok, _⟩ := hX.tensor i o ho
  have hSlot := TensorCopy.slotAt_self slot
  have hLoc : TensorCopy.writeLoc o.spec slot.1.val slot.2.1.val slot.2.2.val =
      some (o.spec.sharedLoc slot) := by simp [TensorCopy.writeLoc, hSlot]
  have hWrite : TensorCopy.writeByte o slot.1.val slot.2.1.val slot.2.2.val = some value := by
    cases hAddr : o.spec.globalAddress slot with
    | none =>
      obtain ⟨content, hContent⟩ := hok.complete hNotify slot
      have hf := hok.writes slot content hContent
      simp only [TensorCopy.source, hAddr] at hf
      rw [TensorCopy.writeByte, hSlot, Option.bind_some, hContent, Option.bind_some, hf]
      exact hFill hAddr
    | some address =>
      have hRead : TensorCopy.readLoc o.spec slot.1.val slot.2.1.val slot.2.2.val =
          some (globalLoc address) := by
        rw [TensorCopy.readLoc_source, hSlot]
        simp [TensorCopy.source, hAddr, globalLoc]
      obtain ⟨byte, hb⟩ := writeByte_of_notified hX ho hNotify hRead
      obtain ⟨hm, hUnwritten⟩ := hBacked address hAddr
      rw [tensor_writeByte_of_initial hX ho hIssue hRead hb hm hUnwritten] at hb
      exact hb
  exact ⟨o, addr, value, ho, hIssue, hLoc, hWrite, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A packed BF16 element byte lies within the allocation for its rows, heads and columns. -/
theorem packedBf16Byte {base cols rows heads row head col byte : Nat}
    (hr : row < rows) (hh : head < heads) (hc : col < cols) (hk : byte < 2) :
    Region.Contains ⟨base, 2 * (rows * heads * cols)⟩
      ((globalLoc (base + 2 * ((row * heads + head) * cols + col))).at byte) := by
  have hrow := Nat.mul_le_mul_right heads (show row + 1 ≤ rows by omega)
  rw [Nat.add_mul, Nat.one_mul] at hrow
  have hcol := Nat.mul_le_mul_right cols
    (show row * heads + head + 1 ≤ rows * heads by omega)
  rw [Nat.add_mul, Nat.one_mul] at hcol
  exact ⟨rfl, rfl, by simp only [globalLoc, Loc.at]; omega,
    by simp only [globalLoc, Loc.at]; omega⟩

/-- The load operand on Q uses the packed rank-three descriptor and logical row origin. -/
def qInputSpec (p : Params) (col row head : Nat) (shared barrier : Loc)
    (clusterAddress : Bool) : TensorCopy.Spec :=
  ⟨⟨2, p.qMap, inputCoordinate col row head, shared, none⟩, barrier, clusterAddress, .one⟩

/-- The load operand on bias uses its physically padded rank-three descriptor. -/
def biasInputSpec (p : Params) (col row head : Nat) (shared barrier : Loc)
    (clusterAddress : Bool) : TensorCopy.Spec :=
  ⟨⟨2, p.biasMap, inputCoordinate col row head, shared, none⟩, barrier, clusterAddress, .one⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

/-- A loaded Q tile covers its backed rows and then the BF16 zero fill. -/
theorem qInputSlotWritten (hp : Pre p l m) (hX : Consistent l Decoded.kernel A m X)
    (writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {i : EvId} {o : TensorCopy.Observation}
    (ho : X.tensor i = some o) (hNotify : o.effects.notified = true) {col row head : Nat}
    {shared barrier : Loc} {clusterAddress : Bool}
    (hSpec : o.spec = qInputSpec p col row head shared barrier clusterAddress)
    (slot : TensorTransfer.Slot o.spec.descriptor) (hc : col + slot.1.val < 128)
    (hh : head < p.heads) :
    let absRow := row + slot.2.1.val
    let absCol := col + slot.1.val
    let value : Value := .float .bf16 (if absRow < p.totalQ then p.q absRow head absCol else 0)
    X.MemWrites (.async i (.write (.load slot.1.val slot.2.1.val slot.2.2.val)))
      {loc := o.spec.sharedLoc slot, size := 1} [value.byteAt slot.2.2.val] := by
  rcases o with ⟨spec, effects⟩
  dsimp only at hSpec
  subst spec
  have hAddr := qSlotAddress p (row := row) slot hc hh
  apply notifiedInputByte hX ho hNotify slot
  · intro address ha
    change TensorTransfer.globalAddress p.qMap (inputCoordinate col row head) none slot =
      some address at ha
    rw [hAddr] at ha
    by_cases hr : row + slot.2.1.val < p.totalQ
    · rw [ite_eq_left hr, Option.some.injEq] at ha
      have hGlobal : globalLoc address =
          (p.qLoc (row + slot.2.1.val) head (col + slot.1.val)).at slot.2.2.val := by
        rw [← ha]
        rfl
      rw [hGlobal, ite_eq_left hr]
      have hk : slot.2.2.val < 2 := slot.2.2.isLt
      refine ⟨hp.qBytes _ hr _ hh _ hc _ hk, fun w a bs hw => ?_⟩
      have hRegion := packedBf16Byte (base := p.qBase) hr hh hc hk
      rw [show 2 * (p.totalQ * p.heads * 128) = 256 * p.heads * p.totalQ by ring] at hRegion
      exact hp.inputByte_unwritten writes (by simp [Params.inputRegions]) hRegion hw
    · simp [hr] at ha
  · intro ha
    change TensorTransfer.globalAddress p.qMap (inputCoordinate col row head) none slot =
      none at ha
    rw [hAddr] at ha
    by_cases hr : row + slot.2.1.val < p.totalQ
    · simp [hr] at ha
    · rw [ite_eq_right hr]
      rfl

/-- Both performed bytes of a Q element are from one finite launch value or the same
BF16 zero fill, independently of the signed coordinates of the actual issue. -/
theorem qInputWordWritten (hp : Pre p l m) (hX : Consistent l Decoded.kernel A m X)
    (hFrame : OutputFootprint p X) {i : EvId} {o : TensorCopy.Observation}
    (ho : X.tensor i = some o) (hNotify : o.effects.notified = true) {origin : Fin 3 → Int}
    {shared barrier : Loc} (hSpec : o.spec = ⟨⟨2,p.qMap,origin,shared,none⟩,barrier,false,.one⟩)
    (x : Fin (TensorTile.count p.qMap.box 0)) (y : Fin (TensorTile.rows p.qMap.box)) :
    ∃ value : ℝ, ∀ byte : Fin 2,
      let slot : TensorTransfer.Slot p.qMap := ⟨x,y,byte⟩
      let spec : TensorCopy.Spec := ⟨⟨2,p.qMap,origin,shared,none⟩,barrier,false,.one⟩
      X.MemWrites (.async i (.write (.load x.val y.val byte.val)))
        {loc := spec.sharedLoc slot, size := 1} [(.float .bf16 value : Value).byteAt byte.val] := by
  rcases o with ⟨spec,effects⟩
  dsimp only at hSpec
  subst spec
  let spec : TensorCopy.Spec := ⟨⟨2,p.qMap,origin,shared,none⟩,barrier,false,.one⟩
  let coordinate := TensorTransfer.coord p.qMap origin none ⟨x,y,(0 : Fin 2)⟩
  have hAddr (byte : Fin 2) : spec.globalAddress ⟨x,y,byte⟩ =
      TensorAddress.lookup (TensorDescriptor.geometry p.qMap) coordinate byte.val := rfl
  by_cases hBounds : TensorAddress.InBounds (TensorDescriptor.geometry p.qMap) coordinate
  · let col := (coordinate 0).toNat
    let row := (coordinate 1).toNat
    let head := (coordinate 2).toNat
    have hC : coordinate = inputCoordinate col row head := by
      funext axis
      fin_cases axis
      · exact (Int.toNat_of_nonneg (hBounds 0).1).symm
      · exact (Int.toNat_of_nonneg (hBounds 1).1).symm
      · exact (Int.toNat_of_nonneg (hBounds 2).1).symm
    have hDom :
        (col < 128 ∧ row < p.totalQ ∧ head < p.heads) := by
      have h0 := (hBounds 0).2
      have h1 := (hBounds 1).2
      have h2 := (hBounds 2).2
      rw [hC] at h0 h1 h2
      change (col : Int) < 128 at h0
      change (row : Int) < p.totalQ at h1
      change (head : Int) < p.heads at h2
      exact ⟨by exact_mod_cast h0,by exact_mod_cast h1,by exact_mod_cast h2⟩
    refine ⟨p.q row head col,fun byte => ?_⟩
    dsimp only
    have hGlobal := (hAddr byte).trans (hC.symm ▸ qLookup p hDom.1 hDom.2.1 hDom.2.2 byte.isLt)
    apply notifiedInputByte hX ho hNotify ⟨x,y,byte⟩
    · intro address ha
      have hEq := Option.some.inj (ha.symm.trans hGlobal)
      subst address
      have hRegion := packedBf16Byte (base := p.qBase) hDom.2.1 hDom.2.2 hDom.1 byte.isLt
      rw [show 2 * (p.totalQ * p.heads * 128) = 256 * p.heads * p.totalQ by ring] at hRegion
      exact ⟨hp.qBytes _ hDom.2.1 _ hDom.2.2 _ hDom.1 _ byte.isLt,
        fun w a bs hw => hFrame.input_unwritten hp (by simp [Params.inputRegions]) hRegion hw⟩
    · intro ha
      have hNo := ha.symm.trans hGlobal
      cases hNo
  · refine ⟨0,fun byte => ?_⟩
    dsimp only
    have hFill : spec.globalAddress ⟨x,y,byte⟩ = none := by
      rw [hAddr,TensorAddress.lookup,ite_eq_right]
      exact fun h => hBounds h.1
    apply notifiedInputByte hX ho hNotify ⟨x,y,byte⟩
    · intro a ha
      cases (ha.symm.trans hFill)
    · intro _
      rfl

/-- A loaded bias tile preserves the explicit physical padding before switching to
descriptor zero fill. Within that region, masked bias remains a BF16 negative infinity. -/
theorem biasInputSlotWritten (hp : Pre p l m) (hX : Consistent l Decoded.kernel A m X)
    (writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {i : EvId} {o : TensorCopy.Observation}
    (ho : X.tensor i = some o) (hNotify : o.effects.notified = true) {col row head : Nat}
    {shared barrier : Loc} {clusterAddress : Bool}
    (hSpec : o.spec = biasInputSpec p col row head shared barrier clusterAddress)
    (slot : TensorTransfer.Slot o.spec.descriptor) (hc : col + slot.1.val < 1280)
    (hh : head < p.heads) :
    let absRow := row + slot.2.1.val
    let absCol := col + slot.1.val
    let value := if absRow < p.totalQ + 128 then biasValue (p.bias absRow head absCol)
      else .float .bf16 0
    X.MemWrites (.async i (.write (.load slot.1.val slot.2.1.val slot.2.2.val)))
      {loc := o.spec.sharedLoc slot, size := 1} [value.byteAt slot.2.2.val] := by
  rcases o with ⟨spec, effects⟩
  dsimp only at hSpec
  subst spec
  have hAddr := biasSlotAddress p (row := row) slot hc hh
  apply notifiedInputByte hX ho hNotify slot
  · intro address ha
    change TensorTransfer.globalAddress p.biasMap (inputCoordinate col row head) none slot =
      some address at ha
    rw [hAddr] at ha
    by_cases hr : row + slot.2.1.val < p.totalQ + 128
    · rw [ite_eq_left hr, Option.some.injEq] at ha
      have hGlobal : globalLoc address =
          (p.biasLoc (row + slot.2.1.val) head (col + slot.1.val)).at slot.2.2.val := by
        rw [← ha]
        rfl
      rw [hGlobal, ite_eq_left hr]
      have hk : slot.2.2.val < 2 := slot.2.2.isLt
      refine ⟨hp.biasBytes _ hr _ hh _ hc _ ?_, fun w a bs hw => ?_⟩
      · cases p.bias (row + slot.2.1.val) head (col + slot.1.val) <;>
          simpa [biasValue, Value.bytes, FloatFmt.bytes] using hk
      · have hRegion := packedBf16Byte (base := p.biasBase) hr hh hc hk
        rw [show 2 * ((p.totalQ + 128) * p.heads * 1280) = 2560 * p.heads * (p.totalQ + 128)
          by ring] at hRegion
        exact hp.inputByte_unwritten writes (by simp [Params.inputRegions]) hRegion hw
    · simp [hr] at ha
  · intro ha
    change TensorTransfer.globalAddress p.biasMap (inputCoordinate col row head) none slot =
      none at ha
    rw [hAddr] at ha
    by_cases hr : row + slot.2.1.val < p.totalQ + 128
    · simp [hr] at ha
    · rw [ite_eq_right hr]
      rfl
end

end
end PTX.Kernels.TmlFa4Fwd
