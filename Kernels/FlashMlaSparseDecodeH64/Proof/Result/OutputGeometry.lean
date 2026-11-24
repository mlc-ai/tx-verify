-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # Output tile coordinates and byte addresses -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Proof Wg0

noncomputable section

theorem outputColumn_lt (j : Fin 4) {w x : Nat} (hw : w < 2) (hx : x < 64) :
    tmaX j.val w + x < 512 := by
  interval_cases w <;> fin_cases j <;> norm_num [tmaX, planeAdd] <;> omega

private theorem foldedTile_inverse (j : Fin 4) (w : Fin 2) :
    stageGroup (planeAdd j.val + 2 * w.val) = j.val ∧
      stageHalf (planeAdd j.val + 2 * w.val) = w.val := by
  fin_cases j <;> fin_cases w <;> decide

/-- The logical output column of a group, issuer warp and within-tile column. -/
def outputColumn (s : Fin 4 × Fin 2 × Fin 64) : Fin 512 :=
  ⟨tmaX s.1.val s.2.1.val + s.2.2.val, outputColumn_lt s.1 s.2.1.isLt s.2.2.isLt⟩

/-- The four groups and two issuer warps partition all 512 output columns. -/
theorem outputColumn_bijective : Function.Bijective outputColumn := by
  constructor
  · rintro ⟨j, w, x⟩ ⟨j', w', x'⟩ h
    have hcol := congrArg Fin.val h
    change tmaX j.val w.val + x.val = tmaX j'.val w'.val + x'.val at hcol
    simp only [tmaX] at hcol
    have hx := x.isLt
    have hx' := x'.isLt
    have heq : planeAdd j.val + 2 * w.val = planeAdd j'.val + 2 * w'.val := by omega
    have hj : j = j' := Fin.ext ((foldedTile_inverse j w).1.symm.trans
      ((congrArg stageGroup heq).trans (foldedTile_inverse j' w').1))
    have hw : w = w' := Fin.ext ((foldedTile_inverse j w).2.symm.trans
      ((congrArg stageHalf heq).trans (foldedTile_inverse j' w').2))
    have hr : x = x' := Fin.ext (by omega)
    rw [hj, hw, hr]
  · intro d
    let tile := d.val / 64
    let j : Fin 4 := ⟨stageGroup tile, by have := d.isLt; unfold stageGroup tile; omega⟩
    let w : Fin 2 := ⟨stageHalf tile, Nat.mod_lt _ (by decide)⟩
    let x : Fin 64 := ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
    refine ⟨(j, w, x), Fin.ext ?_⟩
    have ht : tile < 8 := by have := d.isLt; unfold tile; omega
    change 64 * (planeAdd (stageGroup tile) + 2 * stageHalf tile) + d.val % 64 = d.val
    rw [stageTile_inverse tile ht]
    dsimp only [tile]
    omega

/-- A byte in the 64-column, 64-row output box. -/
abbrev OutputSlot := Fin 64 × Fin 64 × Fin 2

/-- Every output descriptor has a 64 by 64 box with two bytes per slot element. -/
theorem outputShape (P : Params) (L : Launch) (g : Nat) (j : Fin 4) :
    TensorTile.count (outputSpec P L g j).descriptor.box 0 = 64 ∧
      TensorTile.rows (outputSpec P L g j).descriptor.box = 64 ∧
      (outputSpec P L g j).descriptor.format.bytes = 2 := by
  unfold outputSpec
  dsimp only
  norm_num [mapO, encodeTiled, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, Fin.cases, TensorDescriptor.Format.bytes]

/-- The logical slot type of each output descriptor is a fixed-size box. -/
def tensorOutputSlot (P : Params) (L : Launch) (g : Nat) (j : Fin 4) (s : OutputSlot) :
    TensorTransfer.Slot (outputSpec P L g j).descriptor :=
  ⟨⟨s.1.val, by rw [(outputShape P L g j).1]; exact s.1.isLt⟩,
    ⟨s.2.1.val, by rw [(outputShape P L g j).2.1]; exact s.2.1.isLt⟩,
    ⟨s.2.2.val, by rw [(outputShape P L g j).2.2]; exact s.2.2.isLt⟩⟩

/-- Every descriptor slot has those coordinates, with no duplicate representation. -/
theorem tensorOutputSlot_bijective (P : Params) (L : Launch) (g : Nat) (j : Fin 4) :
    Function.Bijective (tensorOutputSlot P L g j) := by
  constructor
  · intro s t heq
    exact Prod.ext (Fin.ext (congrArg (fun x => x.1.val) heq))
      (Prod.ext (Fin.ext (congrArg (fun x => x.2.1.val) heq))
        (Fin.ext (congrArg (fun x => x.2.2.val) heq)))
  · intro t
    obtain ⟨h0, h1, h2⟩ := outputShape P L g j
    let s : OutputSlot := (⟨t.1.val, h0 ▸ t.1.isLt⟩, ⟨t.2.1.val, h1 ▸ t.2.1.isLt⟩,
      ⟨t.2.2.val, h2 ▸ t.2.2.isLt⟩)
    exact ⟨s, Prod.ext (Fin.ext rfl) (Prod.ext (Fin.ext rfl) (Fin.ext rfl))⟩

private theorem outputSlot_coords (P : Params) (L : Launch) (g : Nat) (j : Fin 4)
    (s : OutputSlot) :
    let spec := outputSpec P L g j
    TensorTransfer.coord spec.descriptor spec.origin spec.rows (tensorOutputSlot P L g j s) =
      ![(↑(tmaX j.val (warpOf L g) + s.1.val) : Int), ↑s.2.1.val, ↑(qOf L g), ↑(eOf L g)] := by
  dsimp only [outputSpec]
  have h := s.2.1.isLt
  have hmod : s.2.1.val % 64 = s.2.1.val := Nat.mod_eq_of_lt h
  have hdiv : s.2.1.val / 64 = 0 := Nat.div_eq_of_lt h
  funext i
  fin_cases i <;>
    simp [TensorTransfer.coord, TensorTransfer.index, tensorOutputSlot, TensorTile.coord,
      TensorTile.indexOf, TensorTile.unflatten, TensorTile.count, TensorTile.step, mapO,
      encodeTiled, outputOrigin, Fin.cases, hmod, hdiv]
  all_goals rfl

/-- The selected byte of an output box has its contiguous logical output address. -/
theorem outputSlot_global (P : Params) (L : Launch) (g : Nat) (j : Fin 4) (s : OutputSlot)
    (hw : warpOf L g < 2) (hq : qOf L g < P.s_q) (he : eOf L g < P.b) :
    (outputSpec P L g j).toTensorBox.globalAddress (tensorOutputSlot P L g j s) =
      some ((oLoc P (eOf L g) (qOf L g) s.2.1.val
        (tmaX j.val (warpOf L g) + s.1.val)).addr + s.2.2.val) := by
  rw [TensorBox.globalAddress, TensorTransfer.globalAddress]
  rw [outputSlot_coords]
  let c := tmaX j.val (warpOf L g) + s.1.val
  have hc : c < 512 := outputColumn_lt j hw s.1.isLt
  have hh := s.2.1.isLt
  have hb := s.2.2.isLt
  let geom := TensorDescriptor.geometry
    (mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass)
  let coord : Fin 4 → Int := ![↑c, ↑s.2.1.val, ↑(qOf L g), ↑(eOf L g)]
  have hin : TensorAddress.InBounds geom coord := by
    intro i
    fin_cases i <;> simp [geom, coord, TensorDescriptor.geometry, mapO, encodeTiled, hc, hh, hq, he]
  have hbyte : s.2.2.val < geom.elementBytes := hb
  change TensorAddress.lookup geom coord s.2.2.val = _
  unfold TensorAddress.lookup
  rw [ite_eq_left ⟨hin, hbyte⟩]
  congr 1
  simp [TensorAddress.byteAddress, TensorDescriptor.geometry, geom, coord, mapO, encodeTiled,
    Fin.sum_univ_succ, Fin.cases, TensorDescriptor.Format.bytes, oLoc_eq]
  unfold c
  ring

private theorem output_swizzle {base h x byte : Nat} (hbase : base % 1024 = 0)
    (hx : x < 64) (hb : byte < 2) :
    TensorSwizzle.offset .b128 base (128 * h + 2 * x + byte) =
      128 * h + 16 * ((x / 8) ^^^ (h % 8)) + 2 * (x % 8) + byte := by
  have hrow : (128 * h + 2 * x + byte) / 128 = h := by omega
  have hchunk : (128 * h + 2 * x + byte) / 16 % 8 = x / 8 := by omega
  have hmask : (base / 128 + h) % 8 = h % 8 := by omega
  have hbyte : (128 * h + 2 * x + byte) % 16 = 2 * (x % 8) + byte := by omega
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask, TensorSwizzle.sectors,
    BitVec.toNat_xor, hrow, BitVec.toNat_ofNat, hchunk, hmask, Nat.mod_mod, hbyte]
  omega

/-- The byte that supplies a selected output element is its SW128 staging byte. -/
theorem outputSlot_shared {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (j : Fin 4) (s : OutputSlot) (hw : warpOf L g < 2) :
    (outputSpec P L g j).toTensorBox.sharedLoc (tensorOutputSlot P L g j s) =
      shLoc L g (stageOff s.2.1.val (tmaX j.val (warpOf L g) + s.1.val) + s.2.2.val) := by
  let w : Fin 2 := ⟨warpOf L g, hw⟩
  let x := s.1.val
  let h := s.2.1.val
  let byte := s.2.2.val
  let c := tmaX j.val w.val + x
  let base := L.sharedBase + tmaSrc j.val w.val
  have hx : x < 64 := s.1.isLt
  have hc : c < 512 := outputColumn_lt j hw hx
  have ha : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
  have hbase : base % 1024 = 0 := by
    unfold base tmaSrc stageBase groupOff stageTileBytes
    omega
  have htile : c / 64 = planeAdd j.val + 2 * w.val := by unfold c tmaX; omega
  have hrem : c % 64 = x := by unfold c tmaX; omega
  have hrem' : c % 8 = x % 8 := by unfold c tmaX; omega
  have hstage := stageOff_eq h c hc
  rw [htile, (foldedTile_inverse j w).1, (foldedTile_inverse j w).2, hrem, hrem'] at hstage
  have hPitch : TensorTile.rowBytes (outputSpec P L g j).descriptor.box
      (outputSpec P L g j).descriptor.format.bytes (outputSpec P L g j).descriptor.swizzle =
        128 := by
    rw [TensorTile.rowBytes, (outputShape P L g j).1, (outputShape P L g j).2.2]
    rfl
  unfold TensorBox.sharedLoc TensorTile.sharedByte TensorTile.linearByte
  rw [hPitch]
  simp only [tensorOutputSlot]
  change ⟨.shared, ctaOf L g,
      base + TensorSwizzle.offset .b128 base (h * 128 + x * 2 + byte)⟩ =
    shLoc L g (stageOff h c + byte)
  rw [Nat.mul_comm h 128, Nat.mul_comm x 2, output_swizzle hbase hx s.2.2.isLt, hstage]
  simp only [shLoc, base, byte, Nat.add_assoc]

/-- The destination byte of a TMA slot is the corresponding location in the output tensor. -/
theorem outputSlot_destination (P : Params) (L : Launch) (g : Nat) (j : Fin 4) (s : OutputSlot)
    (hw : warpOf L g < 2) (hq : qOf L g < P.s_q) (he : eOf L g < P.b) :
    TensorStore.destination (outputSpec P L g j) (tensorOutputSlot P L g j s) =
      some ((oLoc P (eOf L g) (qOf L g) s.2.1.val
        (tmaX j.val (warpOf L g) + s.1.val)).at s.2.2.val) := by
  rw [TensorStore.destination, outputSlot_global P L g j s hw hq he]
  rfl

/-- Two coordinates of the output tensor address the same byte only when they coincide. -/
theorem outputByte_injective {P : Params} {e e' q q' h h' d d' b b' : Nat}
    (hq : q < P.s_q) (hq' : q' < P.s_q) (hh : h < 64) (hh' : h' < 64)
    (hd : d < 512) (hd' : d' < 512) (hb : b < 2) (hb' : b' < 2)
    (hl : (oLoc P e q h d).at b = (oLoc P e' q' h' d').at b') :
    e = e' ∧ q = q' ∧ h = h' ∧ d = d' ∧ b = b' := by
  have haddr := congrArg Loc.addr hl
  simp only [Loc.at, oLoc_eq] at haddr
  have hr : e * P.s_q + q = e' * P.s_q + q' := by omega
  have hpos : 0 < P.s_q := by omega
  have hquot (e q : Nat) (hq : q < P.s_q) : (e * P.s_q + q) / P.s_q = e := by
    rw [Nat.mul_comm e, Nat.mul_add_div hpos, Nat.div_eq_of_lt hq, Nat.add_zero]
  have he := congrArg (· / P.s_q) hr
  rw [hquot e q hq, hquot e' q' hq'] at he
  subst e'
  exact ⟨rfl, by omega, by omega, by omega, by omega⟩

private def stageRow (h d b : Nat) : Nat :=
  128 * h + 16 * ((d % 64) / 8 ^^^ h % 8) + 2 * (d % 8) + b

private theorem stageRow_eq (h d b : Nat) (hb : b < 2) :
    stageRow h d b = TensorSwizzle.offset .b128 0 (128 * h + 2 * (d % 64) + b) := by
  rw [output_swizzle (by decide) (Nat.mod_lt d (by decide)) hb]
  unfold stageRow
  rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 64)]

private theorem stageRow_lt {h d b : Nat} (hh : h < 64) (hb : b < 2) :
    stageRow h d b < stageTileBytes := by
  rw [stageRow_eq h d b hb]
  have h := TensorSwizzle.offset_row .b128 0 (128 * h + 2 * (d % 64) + b)
  unfold stageTileBytes
  omega

private theorem stageOff_byte (h d b : Nat) :
    stageOff h d + b = stageBase + stageTileBytes * (d / 64) + stageRow h d b := by
  simp only [stageOff, stageRel, stageRow]
  omega

/-- The staged rows and columns assign only one output byte to each shared offset. -/
theorem stageByte_injective {h h' d d' b b' : Nat}
    (hh : h < 64) (hh' : h' < 64) (hb : b < 2) (hb' : b' < 2)
    (heq : stageOff h d + b = stageOff h' d' + b') :
    h = h' ∧ d = d' ∧ b = b' := by
  rw [stageOff_byte, stageOff_byte] at heq
  have hr0 := stageRow_lt (d := d) hh hb
  have hr1 := stageRow_lt (d := d') hh' hb'
  have htile : d / 64 = d' / 64 := by unfold stageTileBytes at *; omega
  have hr : stageRow h d b = stageRow h' d' b' := by rw [htile] at heq; omega
  rw [stageRow_eq h d b hb, stageRow_eq h' d' b' hb'] at hr
  have hlin := TensorSwizzle.offset_injective .b128 0 hr
  exact ⟨by omega, by omega, by omega⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
