-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Kernels.FlashAttn4Fwd.Proof.Protocol.Schedule
public import Lemmas.Tensor.TensorCopy
public import Lemmas.Tensor.TensorAddress

@[expose] public section

/-! # Which input element a ring copy loads

A ring copy (`copySpec`) loads a box of the Q, K or V map (`inputBase`, `inputRows`) at the
coordinates `{d, row, head, batch}` of its use and box (`copyOrigin`: `copyCol`, `copyRow`,
`copyHead`, `copyBatch`, `copyOrigin_eq`). Slot `(x, y)`, byte `z` of the box reads byte `z` of
the input's element `(copyBatch, copyHead, copyRow + y, copyCol + x)`,
which is inside the input when the copy's item exists (`copy_readLoc`): the coordinates of an
existing item are in range (`Schedule.coords_eq`, `Schedule.coords_lt`), `seqlen_q` is a multiple
of 512 and `seqlen_k` of 128. Byte `z` of that element at launch is byte `z` of its FP16 value
(`input_byte`, `Pre.inputQ`, `Pre.inputK`, `Pre.inputV`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof TensorDescriptor

noncomputable section

namespace SmemElements

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The base address of the input a full barrier's copies load: Q for a Q stage, K for an even
KV slot, V for an odd one. -/
def inputBase (P : Params) : FBar → Nat
  | .kvFull s => if s.val % 2 = 0 then P.kBase else P.vBase
  | _ => P.qBase

/-- The rows of the input a full barrier's copies load: `seqlen_q` for Q, `seqlen_k` for K and
V. -/
def inputRows (P : Params) : FBar → Nat
  | .kvFull _ => P.sk
  | _ => P.sq

/-- The value of element `(batch, head, row, d)` of the input a full barrier's copies load. -/
def inputValue (P : Params) (b : FBar) (batch head row d : Nat) : ℝ :=
  match b with
  | .kvFull s => if s.val % 2 = 0 then P.k batch head row d else P.v batch head row d
  | _ => P.q batch head row d

/-- The work item's coordinates of the use of the copy by thread `g` on full barrier `b` with
`cnt` earlier ones there: (batch, head, query block). -/
def copyCoords (P : Params) (L : Launch) (g : Nat) (b : FBar) (cnt : Nat) : Nat × Nat × Nat :=
  coordsOf L (workOf L g (useItem P b (cnt / b.copies)))

/-- The batch of that copy's box. -/
def copyBatch (P : Params) (L : Launch) (g : Nat) (b : FBar) (cnt : Nat) : Nat :=
  (copyCoords P L g b cnt).1

/-- The head of that copy's box. -/
def copyHead (P : Params) (L : Launch) (g : Nat) (b : FBar) (cnt : Nat) : Nat :=
  (copyCoords P L g b cnt).2.1

/-- The first row of that copy's box: Q rows `512 m + 256 st + 128 r`, K rows
`128 blk + 64 r`, V rows `128 blk` (`r` the CTA's rank in its pair). -/
def copyRow (P : Params) (L : Launch) (g : Nat) (b : FBar) (cnt : Nat) : Nat :=
  match b with
  | .qFull st => 512 * (copyCoords P L g b cnt).2.2 + 256 * st.val + 128 * (ctaOf L g % 2)
  | .kvFull s =>
    if s.val % 2 = 0 then 128 * useBlock P b (cnt / b.copies) + 64 * (ctaOf L g % 2)
    else 128 * useBlock P b (cnt / b.copies)
  | _ => 0

/-- The first head-dimension column of that copy's box: `64 j` for copy `j` of a Q or K use,
`64 r` for a V use. -/
def copyCol (L : Launch) (g : Nat) (b : FBar) (cnt : Nat) : Nat :=
  match b with
  | .kvFull s => if s.val % 2 = 0 then 64 * (cnt % b.copies) else 64 * (ctaOf L g % 2)
  | _ => 64 * (cnt % b.copies)

/-- The origin of a ring copy's box, coordinate by coordinate. -/
theorem copyOrigin_eq {g : Nat} {b : FBar} (hb : b.isFull) (cnt : Nat) :
    copyOrigin P L g b (cnt / b.copies) (cnt % b.copies) =
      ![((copyCol L g b cnt : Nat) : Int), ((copyRow P L g b cnt : Nat) : Int),
        ((copyHead P L g b cnt : Nat) : Int), ((copyBatch P L g b cnt : Nat) : Int)] := by
  cases b with
  | qFull st => rfl
  | kvFull s =>
    by_cases hs : s.val % 2 = 0
    · simp only [copyOrigin, copyCol, copyRow, hs, ↓reduceIte]
      rfl
    · simp only [copyOrigin, copyCol, copyRow, hs, ↓reduceIte]
      rfl
  | _ => cases hb

/-- **Two copies of one use and box by the same CTA load one box**: the same coordinates. -/
theorem copy_congr {g g' : Nat} {b : FBar} {cnt cnt' : Nat} (hc : ctaOf L g = ctaOf L g')
    (hu : cnt / b.copies = cnt' / b.copies) (hj : cnt % b.copies = cnt' % b.copies) :
    copyBatch P L g b cnt = copyBatch P L g' b cnt' ∧
      copyHead P L g b cnt = copyHead P L g' b cnt' ∧
      copyRow P L g b cnt = copyRow P L g' b cnt' ∧ copyCol L g b cnt = copyCol L g' b cnt' := by
  have hw : copyCoords P L g b cnt = copyCoords P L g' b cnt' := by
    simp only [copyCoords, workOf, clusterOf, hc, hu]
  refine ⟨by simp only [copyBatch, hw], by simp only [copyHead, hw], ?_, ?_⟩
  · cases b <;> simp only [copyRow, hw, hc, hu]
  · cases b <;> simp only [copyCol, hc, hj]

/-- The element indices of column `x` of row `y` of a kernel map's box. -/
theorem tiled_indexOf {base rows boxRows : Nat} {fill : Fill} {cls : AllocationClass} {x y : Nat}
    (hy : y < boxRows) :
    TensorTile.indexOf (FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls).box x y =
      ![x, y, 0, 0] := by
  funext a
  have : y / boxRows = 0 := Nat.div_eq_of_lt hy
  fin_cases a <;> simp [TensorTile.indexOf, TensorTile.unflatten, TensorTile.count,
    TensorTile.step, FlashAttn4Fwd.encodeTiled, Nat.mod_eq_of_lt hy, this] <;> rfl

/-- The kernel map's address of byte `z` of element `(bt, hd, row, d)` in range. -/
theorem tiled_lookup {base rows boxRows : Nat} {fill : Fill} {cls : AllocationClass}
    {bt hd row d z : Nat} (hb : bt < P.b) (hh : hd < P.h) (hr : row < rows) (hd' : d < 128)
    (hz : z < 2) :
    TensorAddress.lookup (geometry (FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls))
      ![((d : Nat) : Int), ((row : Nat) : Int), ((hd : Nat) : Int), ((bt : Nat) : Int)] z =
      some ((elementLoc P base rows bt hd row d).at z).addr := by
  apply (TensorAddress.lookup_some_iff _ _ _ _).mpr
  refine ⟨fun axis => ?_, by simpa [geometry, FlashAttn4Fwd.encodeTiled, Format.bytes] using hz,
    ?_⟩
  · fin_cases axis <;> simp [geometry, FlashAttn4Fwd.encodeTiled] <;> omega
  · unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_four]
    show _ = base + ((d : Int).toNat * 2 + (row : Int).toNat * (256 * P.h) +
      (hd : Int).toNat * 256 + (bt : Int).toNat * (256 * P.h * rows)) + z
    simp only [Int.toNat_natCast, elementLoc, Loc.at]
    ring

/-- **The global byte a slot of a kernel map's box reads**: byte `z` of the element at the
box's origin plus `(x, y)`, when it is in range. -/
theorem tiled_readLoc {base rows boxRows : Nat} {fill : Fill} {cls : AllocationClass}
    {sb mb : Loc} {ca : Bool} {grp : CtaGroup} {d0 r0 hd bt x y z : Nat} (hx : x < 64)
    (hy : y < boxRows) (hz : z < 2) (hd' : d0 + x < 128) (hr : r0 + y < rows) (hh : hd < P.h)
    (hb : bt < P.b) :
    TensorCopy.readLoc ⟨⟨3, FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls,
        ![((d0 : Nat) : Int), ((r0 : Nat) : Int), ((hd : Nat) : Int), ((bt : Nat) : Int)], sb,
        none⟩, mb, ca, grp⟩ x y z =
      some ((elementLoc P base rows bt hd (r0 + y) (d0 + x)).at z) := by
  have hc : x < TensorTile.count
      (FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls).box 0 := by
    simpa [FlashAttn4Fwd.encodeTiled, TensorTile.count, TensorTile.step] using hx
  have hrw : y < TensorTile.rows
      (FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls).box := by
    simpa [FlashAttn4Fwd.encodeTiled, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step] using hy
  have hzb : z < (FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls).format.bytes := by
    simpa [FlashAttn4Fwd.encodeTiled, Format.bytes] using hz
  have hslot : TensorTransfer.slotAt (FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls)
      x y z = some ⟨⟨x, hc⟩, ⟨y, hrw⟩, ⟨z, hzb⟩⟩ := by
    unfold TensorTransfer.slotAt
    simp only [hc, hrw, hzb, dite_true]
  have hcoord : TensorTile.coord (FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls).box
      ![((d0 : Nat) : Int), ((r0 : Nat) : Int), ((hd : Nat) : Int), ((bt : Nat) : Int)]
      (TensorTile.indexOf (FlashAttn4Fwd.encodeTiled base rows P.h P.b boxRows fill cls).box x y) =
      ![((d0 + x : Nat) : Int), ((r0 + y : Nat) : Int), ((hd : Nat) : Int),
        ((bt : Nat) : Int)] := by
    rw [tiled_indexOf hy]
    funext a
    fin_cases a <;> simp [TensorTile.coord, TensorTile.step, FlashAttn4Fwd.encodeTiled]
  rw [TensorCopy.readLoc_source, hslot]
  simp only [Option.bind_some, TensorCopy.source, TensorBox.globalAddress,
    TensorTransfer.globalAddress, TensorTransfer.coord, TensorTransfer.index]
  erw [hcoord, tiled_lookup hb hh hr hd' hz]
  rfl

/-- The coordinates of an existing item are in range. -/
theorem coords_in (hpre : Pre P L mem0) {w : Nat} (hw : w < totOf L) :
    (coordsOf L w).1 < P.b ∧ (coordsOf L w).2.1 < P.h ∧ (coordsOf L w).2.2 < P.blocks := by
  have h1 := Schedule.totOf_items hpre
  have h2 := totOf_lt hpre
  rw [Schedule.coords_eq hpre (by omega)]
  exact Schedule.coords_lt hpre (by omega)

/-- **The input byte a ring copy's slot reads.** Slot `(x, y)`, byte `z` of a copy of an existing
item reads byte `z` of the input's element `(copyBatch, copyHead, copyRow + y, copyCol + x)`,
which is in range. -/
theorem copy_readLoc (hpre : Pre P L mem0) {g : Nat} {b : FBar} (hb : b.isFull) (cnt : Nat)
    (hw : workOf L g (useItem P b (cnt / b.copies)) < totOf L) {x y z : Nat} (hx : x < 64)
    (hy : y < b.copyBytes / 128) (hz : z < 2) :
    copyBatch P L g b cnt < P.b ∧ copyHead P L g b cnt < P.h ∧
      copyRow P L g b cnt + y < inputRows P b ∧ copyCol L g b cnt + x < 128 ∧
      TensorCopy.readLoc (copySpec P L g b cnt) x y z = some ((elementLoc P (inputBase P b)
        (inputRows P b) (copyBatch P L g b cnt) (copyHead P L g b cnt)
        (copyRow P L g b cnt + y) (copyCol L g b cnt + x)).at z) := by
  obtain ⟨h1, h2, h3⟩ := coords_in hpre hw
  have hr : ctaOf L g % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsk : 128 * kvBlocks P = P.sk := by
    have := hpre.skDiv128
    unfold kvBlocks
    omega
  have hsq : 512 * P.blocks = P.sq := by
    have := hpre.sqDiv512
    unfold Params.blocks
    omega
  have hskp := hpre.skPos
  have hsp : copySpec P L g b cnt = ⟨⟨3, copyMap P b,
      ![((copyCol L g b cnt : Nat) : Int), ((copyRow P L g b cnt : Nat) : Int),
        ((copyHead P L g b cnt : Nat) : Int), ((copyBatch P L g b cnt : Nat) : Int)],
      ⟨.shared, ctaOf L g, L.sharedBase + b.regionOff + cnt % b.copies * b.copyBytes⟩, none⟩,
      b.loc L (pairBase L g), true, .two⟩ := by
    rw [← copyOrigin_eq hb]
    rfl
  rw [hsp]
  have hb1 : copyBatch P L g b cnt < P.b := h1
  have hh1 : copyHead P L g b cnt < P.h := h2
  cases b with
  | qFull st =>
    have hst := st.isLt
    have hy' : y < 128 := by simpa [FBar.copyBytes] using hy
    have hrow : copyRow P L g (.qFull st) cnt + y < P.sq := by
      simp only [copyRow, copyCoords]
      omega
    have hcol : copyCol L g (.qFull st) cnt + x < 128 := by
      simp only [copyCol, FBar.copies]
      omega
    exact ⟨hb1, hh1, hrow, hcol, tiled_readLoc hx hy' hz hcol hrow hh1 hb1⟩
  | kvFull s =>
    have hcp : cnt % (FBar.kvFull s).copies < 2 := by
      simp only [FBar.copies]
      split_ifs <;> omega
    have hblk : useBlock P (.kvFull s) (cnt / (FBar.kvFull s).copies) < kvBlocks P := by
      simp only [useBlock]
      omega
    by_cases hs : s.val % 2 = 0
    · have hy' : y < 64 := by simpa [FBar.copyBytes, hs] using hy
      have hrow : copyRow P L g (.kvFull s) cnt + y < P.sk := by
        simp only [copyRow, hs, ↓reduceIte]
        omega
      have hcol : copyCol L g (.kvFull s) cnt + x < 128 := by
        simp only [copyCol, hs, ↓reduceIte]
        omega
      have hm : copyMap P (.kvFull s) =
          FlashAttn4Fwd.encodeTiled P.kBase P.sk P.h P.b 64 P.kFill P.kClass := by
        simp only [copyMap, hs, ↓reduceIte]
        rfl
      simp only [inputBase, inputRows, hs, ↓reduceIte]
      rw [hm]
      exact ⟨hb1, hh1, hrow, hcol, tiled_readLoc hx hy' hz hcol hrow hh1 hb1⟩
    · have hy' : y < 128 := by simpa [FBar.copyBytes, hs] using hy
      have hrow : copyRow P L g (.kvFull s) cnt + y < P.sk := by
        simp only [copyRow, hs, ↓reduceIte]
        omega
      have hcol : copyCol L g (.kvFull s) cnt + x < 128 := by
        simp only [copyCol, hs, ↓reduceIte]
        omega
      have hm : copyMap P (.kvFull s) =
          FlashAttn4Fwd.encodeTiled P.vBase P.sk P.h P.b 128 P.vFill P.vClass := by
        simp only [copyMap, hs, ↓reduceIte]
        rfl
      simp only [inputBase, inputRows, hs, ↓reduceIte]
      rw [hm]
      exact ⟨hb1, hh1, hrow, hcol, tiled_readLoc hx hy' hz hcol hrow hh1 hb1⟩
  | _ => cases hb

/-- **An input byte at launch** is the byte of its element's FP16 value. -/
theorem input_byte (hpre : Pre P L mem0) {b : FBar} (hb : b.isFull) {bt hd row d z : Nat}
    (hbt : bt < P.b) (hhd : hd < P.h) (hr : row < inputRows P b) (hd' : d < 128) (hz : z < 2) :
    mem0 ((elementLoc P (inputBase P b) (inputRows P b) bt hd row d).at z) =
      some (some ((Value.float .f16 (inputValue P b bt hd row d)).byteAt z)) := by
  cases b with
  | qFull st => exact hpre.inputQ bt hbt hd hhd row hr d hd' z hz
  | kvFull s =>
    by_cases hs : s.val % 2 = 0
    · simp only [inputBase, inputRows, inputValue, hs, ↓reduceIte] at hr ⊢
      exact hpre.inputK bt hbt hd hhd row hr d hd' z hz
    · simp only [inputBase, inputRows, inputValue, hs, ↓reduceIte] at hr ⊢
      exact hpre.inputV bt hbt hd hhd row hr d hd' z hz
  | _ => cases hb

/-- An input byte is outside O. -/
theorem input_outside (hpre : Pre P L mem0) {b : FBar} (hb : b.isFull) {bt hd row d z : Nat}
    (hbt : bt < P.b) (hhd : hd < P.h) (hr : row < inputRows P b) (hd' : d < 128) (hz : z < 2) :
    ¬ (((elementLoc P (inputBase P b) (inputRows P b) bt hd row d).at z).cta = 0 ∧
      P.oBase ≤ ((elementLoc P (inputBase P b) (inputRows P b) bt hd row d).at z).addr ∧
      ((elementLoc P (inputBase P b) (inputRows P b) bt hd row d).at z).addr <
        P.oBase + tensorBytes P P.sq) := by
  have key : ∀ base rows, rows = inputRows P b →
      (base + tensorBytes P rows ≤ P.oBase ∨ P.oBase + tensorBytes P P.sq ≤ base) →
      ¬ (((elementLoc P base rows bt hd row d).at z).cta = 0 ∧
        P.oBase ≤ ((elementLoc P base rows bt hd row d).at z).addr ∧
        ((elementLoc P base rows bt hd row d).at z).addr < P.oBase + tensorBytes P P.sq) := by
    rintro base rows hrows hap ⟨-, h1, h2⟩
    rw [← hrows] at hr
    have hlt : ((bt * rows + row) * P.h + hd) * 128 + d < P.b * rows * P.h * 128 := by
      have e1 : bt * rows + row < P.b * rows := by
        calc bt * rows + row < bt * rows + rows := by omega
          _ = (bt + 1) * rows := by ring
          _ ≤ P.b * rows := Nat.mul_le_mul_right _ hbt
      have e2 : (bt * rows + row) * P.h + hd < P.b * rows * P.h := by
        calc (bt * rows + row) * P.h + hd < (bt * rows + row) * P.h + P.h := by omega
          _ = (bt * rows + row + 1) * P.h := by ring
          _ ≤ P.b * rows * P.h := Nat.mul_le_mul_right _ e1
      omega
    have e3 : tensorBytes P rows = P.b * rows * P.h * 128 * 2 := by
      simp only [tensorBytes]
      ring
    simp only [elementLoc, Loc.at] at h1 h2
    omega
  cases b with
  | qFull st => exact key _ _ rfl hpre.outputApartQ
  | kvFull s =>
    by_cases hs : s.val % 2 = 0
    · have := key P.kBase P.sk rfl hpre.outputApartK
      simpa only [inputBase, inputRows, hs, ↓reduceIte] using this
    · have := key P.vBase P.sk rfl hpre.outputApartV
      simpa only [inputBase, inputRows, hs, ↓reduceIte] using this
  | _ => cases hb

end SmemElements

end
end PTX.Kernels.FlashAttn4Fwd.Proof
