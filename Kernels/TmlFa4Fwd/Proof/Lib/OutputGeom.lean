-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Assign
public import Lemmas.Tensor.TensorSwizzle
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The output arrays' bytes

The packed O bytes and the LSE words lie in their regions (`outputByte_in`, `lseByte_in`), the
regions are fixed by the launch (`outputs_pinned`), and an output box's byte slots are the packed
output bytes of its request's rows (`writebackWriteLoc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow TensorDescriptor PTX.Kernels.TmlFa4Fwd.Epilogue

noncomputable section

/-- A valid row in a request is in the packed query allocation. -/
theorem packedRow_lt {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b row : Nat} (hb : b < p.batch) (hr : row < p.qLength b) :
    p.qOffset b + row < p.totalQ := by
  have h := hp.qOffset_le_total (b := b + 1) (by omega)
  unfold Params.qLength at hr
  omega

variable {p : Params}

/-- Every valid O byte lies in the packed output region. -/
theorem outputByte_in {q h d k : Nat} (hq : q < p.totalQ) (hh : h < p.heads) (hd : d < 128)
    (hk : k < 4) :
    p.oRegion.Contains ((p.oLoc q h d).at k) := by
  have hrow : q * p.heads + h < p.totalQ * p.heads := by
    have hmul := Nat.mul_le_mul_right p.heads (show q + 1 ≤ p.totalQ by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  change Space.global = Space.global ∧ 0 = 0 ∧
    p.oBase ≤ p.oBase + 4 * ((q * p.heads + h) * 128 + d) + k ∧
    p.oBase + 4 * ((q * p.heads + h) * 128 + d) + k <
      p.oBase + 512 * p.heads * p.totalQ
  rw [show 512 * p.heads * p.totalQ = 512 * (p.totalQ * p.heads) by ring]
  exact ⟨rfl, rfl, by omega, by omega⟩

/-- The LSE stride may include padding. Only the first `totalQ` rows of each head are outputs. -/
theorem lseByte_in {q h k : Nat} (hq : q < p.totalQ) (hh : h < p.heads) (hk : k < 4) :
    p.lseRegion.Contains ((p.lseLoc q h).at k) := by
  have hmul := Nat.mul_le_mul_right p.lseStride (show h ≤ p.heads - 1 by omega)
  exact ⟨rfl, rfl, by simp only [Params.lseRegion, Params.lseLoc, globalLoc, Loc.at]; omega,
    by simp only [Params.lseRegion, Params.lseLoc, globalLoc, Loc.at]; omega⟩

/-- Equal little-endian bytes of two values below `256 ^ n` give equal values. -/
theorem leByte_inj {n x y : Nat} (hx : x < 256 ^ n) (hy : y < 256 ^ n)
    (h : ∀ k < n, leByte x k = leByte y k) : x = y := by
  have key : ∀ j ≤ n, x % 256 ^ j = y % 256 ^ j := by
    intro j
    induction j with
    | zero => intro _; simp only [pow_zero, Nat.mod_one]
    | succ j ih =>
      intro hj
      have hk := congrArg BitVec.toNat (h j (by omega))
      simp only [leByte, BitVec.toNat_ofNat] at hk
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (by omega), hk]
  have := key n le_rfl
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

private theorem ofNat64_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : BitVec.ofNat 64 x = BitVec.ofNat 64 y) : x = y := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

private theorem scalar_eq {p P : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (hP : Pre P l m) {i : Nat} {f : Params → Nat} (hpi : (i, f p) ∈ p.scalarWords)
    (hPi : (i, f P) ∈ P.scalarWords) : f P = f p := by
  obtain ⟨hlt, hv⟩ := hp.values _ hpi
  obtain ⟨hLt, hV⟩ := hP.values _ hPi
  exact ofNat64_inj (by omega) (by omega) (Option.some.inj (hV.symm.trans hv))

private theorem object_eq {p P : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (hP : Pre P l m) {i off bytes : Nat} {f : Params → Nat}
    (hpi : (i, off, bytes, f p) ∈ p.objectWords) (hPi : (i, off, bytes, f P) ∈ P.objectWords) :
    f P = f p := by
  obtain ⟨hlt, hv⟩ := hp.objectBytes _ _ _ _ hpi
  obtain ⟨hLt, hV⟩ := hP.objectBytes _ _ _ _ hPi
  exact leByte_inj hLt hlt fun k hk =>
    Option.some.inj ((hV k hk).symm.trans (hv k hk))

private theorem map_eq {p P : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (hP : Pre P l m) {i outer : Nat} {f : Params → Nat} {d : Params → Descriptor outer}
    (hpi : (i, f p, (⟨outer, d p⟩ : (outer : Nat) × Descriptor outer)) ∈
      [(9, p.qMapAddress, ⟨2, p.qMap⟩), (10, p.oMapAddress, ⟨3, p.oMap⟩),
        (11, p.biasMapAddress, ⟨2, p.biasMap⟩)])
    (hPi : (i, f P, (⟨outer, d P⟩ : (outer : Nat) × Descriptor outer)) ∈
      [(9, P.qMapAddress, ⟨2, P.qMap⟩), (10, P.oMapAddress, ⟨3, P.oMap⟩),
        (11, P.biasMapAddress, ⟨2, P.biasMap⟩)]) :
    d P = d p := by
  obtain ⟨hpo, -, -, hpt, -⟩ := hp.maps _ _ _ hpi
  obtain ⟨hPo, -, -, hPt, -⟩ := hP.maps _ _ _ hPi
  have hAddr : f P = f p := by
    have := hPo.symm.trans hpo
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.2
  rw [hAddr] at hPt
  have hSig := Option.some.inj (hPt.symm.trans hpt)
  exact eq_of_heq (Sigma.mk.inj hSig).2

/-- **The O and LSE regions are fixed by the launch.** -/
theorem outputs_pinned {p P : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (hP : Pre P l m) : P.oRegion = p.oRegion ∧ P.lseRegion = p.lseRegion := by
  have hHeads : P.heads = p.heads :=
    scalar_eq (i := 17) (f := Params.heads) hp hP (by simp [Params.scalarWords])
      (by simp [Params.scalarWords])
  have hQ : P.qMap = p.qMap :=
    map_eq (i := 9) (f := Params.qMapAddress) (d := Params.qMap) hp hP (by simp) (by simp)
  have hO : P.oMap = p.oMap :=
    map_eq (i := 10) (f := Params.oMapAddress) (d := Params.oMap) hp hP (by simp) (by simp)
  have hTotal : P.totalQ = p.totalQ := congrArg (fun d : Descriptor 2 => d.extent 1) hQ
  have hBase : P.oBase = p.oBase := by
    have h := congrArg Descriptor.base hO
    simp only [Params.oMap] at h
    have := hp.raggedBase
    have := hP.raggedBase
    rw [hHeads] at h
    omega
  have hLse : P.lseBase = p.lseBase :=
    object_eq (i := 4) (off := 0) (bytes := 8) (f := Params.lseBase) hp hP
      (by simp [Params.objectWords]) (by simp [Params.objectWords])
  have hStride : P.lseStride = p.lseStride :=
    object_eq (i := 4) (off := 16) (bytes := 8) (f := Params.lseStride) hp hP
      (by simp [Params.objectWords]) (by simp [Params.objectWords])
  simp only [Params.oRegion, Params.lseRegion, hHeads, hTotal, hBase, hLse, hStride, and_self]

private def outputTile : TensorTile.Box 4 :=
  ⟨![32, 128, 1, 1], ![1, 1, 1, 1]⟩

theorem outputBoxWidthShared (p : Params) : TensorTile.count p.oMap.box 0 = 32 := by
  simp [TensorTile.count, TensorTile.step, Params.oMap]

theorem outputBoxRowsShared (p : Params) : TensorTile.rows p.oMap.box = 128 := by
  simp [TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step, Params.oMap]

private theorem outputTileIndex (x y : Nat) (hy : y < 128) :
    TensorTile.indexOf outputTile x y = ![x, y, 0, 0] := by
  have hd : y / 128 = 0 := Nat.div_eq_of_lt hy
  funext axis
  fin_cases axis <;>
    simp [TensorTile.indexOf, TensorTile.unflatten, TensorTile.count, TensorTile.step,
      outputTile, Nat.mod_eq_of_lt hy, hd] <;> rfl

private theorem outputTileCoordinate (p : Params) (batch row head col : Nat)
    (slot : TensorTransfer.Slot p.oMap) :
    TensorTransfer.coord p.oMap (oCoordinate p batch head row col) none slot =
      oCoordinate p batch head (row + slot.2.1.val) (col + slot.1.val) := by
  have hy : slot.2.1.val < 128 := outputBoxRowsShared p ▸ slot.2.1.isLt
  change TensorTile.coord outputTile (oCoordinate p batch head row col)
    (TensorTile.indexOf outputTile slot.1.val slot.2.1.val) = _
  rw [outputTileIndex _ _ hy]
  funext axis
  fin_cases axis <;> simp [TensorTile.coord, TensorTile.step, outputTile, oCoordinate,
    Int.add_assoc]

/-- A byte slot of a writeback subbox targets the packed output exactly when its query row
belongs to the selected request. The shifted TMA coordinate clips the tail of that request. -/
theorem writebackSlotDestination {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch head tile : Nat} (stage : Fin 2) (subbox : Fin 4)
    (slot : TensorTransfer.Slot p.oMap) (hb : batch < p.batch) (hh : head < p.heads) :
    let row := stageRow tile stage + slot.2.1.val
    let col := 32 * subbox.val + slot.1.val
    TensorStore.destination (writebackStoreSpec p l g batch head tile stage subbox) slot =
      if row < p.qLength batch then
        some ((p.oLoc (p.qOffset batch + row) head col).at slot.2.2.val)
      else none := by
  dsimp only
  have hx : slot.1.val < 32 := outputBoxWidthShared p ▸ slot.1.isLt
  have hk : slot.2.2.val < 4 := slot.2.2.isLt
  have hs := subbox.isLt
  let row := stageRow tile stage + slot.2.1.val
  let col := 32 * subbox.val + slot.1.val
  have hcol : col < 128 := by dsimp [col]; omega
  change (TensorTransfer.globalAddress p.oMap (oCoordinate p batch head (stageRow tile stage)
    (32 * subbox.val)) none slot).map (fun addr => globalLoc addr) =
      if row < p.qLength batch then some ((p.oLoc (p.qOffset batch + row) head col).at
        slot.2.2.val) else none
  unfold TensorTransfer.globalAddress
  rw [outputTileCoordinate]
  change (TensorAddress.lookup (geometry p.oMap)
    (oCoordinate p batch head row col) slot.2.2.val).map globalLoc = _
  by_cases hr : row < p.qLength batch
  · rw [outputLookup_of_pre hp hb hh hr hcol hk, ite_eq_left hr]
    rfl
  · rw [outputTailLookup_of_pre hp hb (Nat.le_of_not_lt hr), ite_eq_right hr]
    rfl

/-- Concrete coordinates outside a 32 × 128 subbox, or beyond one four-byte FP32 element,
do not denote a write effect. The other coordinates use the packed output address. -/
theorem writebackWriteLoc {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch head tile : Nat} (stage : Fin 2) (subbox : Fin 4) (x y k : Nat)
    (hb : batch < p.batch) (hh : head < p.heads) :
    let row := stageRow tile stage + y
    let col := 32 * subbox.val + x
    TensorStore.writeLoc (writebackStoreSpec p l g batch head tile stage subbox) x y k =
      if x < 32 ∧ y < 128 ∧ k < 4 ∧ row < p.qLength batch then
        some ((p.oLoc (p.qOffset batch + row) head col).at k)
      else none := by
  dsimp only
  let target (slot : TensorTransfer.Slot p.oMap) : Option Loc :=
    TensorStore.destination (writebackStoreSpec p l g batch head tile stage subbox) slot
  change (TensorTransfer.slotAt p.oMap x y k).bind target = _
  by_cases h : x < 32 ∧ y < 128 ∧ k < 4
  · obtain ⟨hx, hy, hk⟩ := h
    have hcx : x < TensorTile.count p.oMap.box 0 := (outputBoxWidthShared p).symm ▸ hx
    have hry : y < TensorTile.rows p.oMap.box := (outputBoxRowsShared p).symm ▸ hy
    let slot : TensorTransfer.Slot p.oMap := ⟨⟨x, hcx⟩, ⟨y, hry⟩, ⟨k, hk⟩⟩
    have hSlot : TensorTransfer.slotAt p.oMap x y k = some slot := by
      unfold TensorTransfer.slotAt
      have hck : k < p.oMap.format.bytes := hk
      rw [dite_eq_left hcx, dite_eq_left hry, dite_eq_left hck]
    rw [hSlot, Option.bind_some]
    simp only [hx, hy, hk, true_and]
    exact writebackSlotDestination hp stage subbox (g := g) (tile := tile) slot hb hh
  · have hSlot : TensorTransfer.slotAt p.oMap x y k = none := by
      unfold TensorTransfer.slotAt
      split
      · split
        · split
          · rename_i hcx hry hck
            exact (h ⟨outputBoxWidthShared p ▸ hcx, outputBoxRowsShared p ▸ hry, hck⟩).elim
          · rfl
        · rfl
      · rfl
    rw [hSlot, Option.bind_none]
    rw [ite_eq_right (fun hw => h ⟨hw.1, hw.2.1, hw.2.2.1⟩)]

end
end PTX.Kernels.TmlFa4Fwd.Proof
