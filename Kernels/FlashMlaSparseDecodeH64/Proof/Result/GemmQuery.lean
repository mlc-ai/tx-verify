-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
import Lemmas.Tensor.TensorSwizzle
import Lemmas.Tensor.TensorReadSources

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open MmaDataTrace Wg1Mma

noncomputable section

/-- The query descriptor copies a 64-feature tile of all 64 heads. -/
theorem queryTile_shape (P : Params) (L : Launch) (g : Nat) (tile : Fin 8) :
    let d := (queryTmaSpec P L g tile).descriptor
    TensorTile.count d.box 0 = 64 ∧ TensorTile.rows d.box = 64 ∧ d.format.bytes = 2 := by
  unfold queryTmaSpec
  dsimp only
  norm_num [mapQ, encodeTiled, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, Fin.cases, TensorDescriptor.Format.bytes]

/-- The slot of a query tile at a feature within the tile, head and byte. -/
def queryTileSlot (P : Params) (L : Launch) (g : Nat) (tile : Fin 8)
    (x h : Fin 64) (byte : Fin 2) : TensorTransfer.Slot (queryTmaSpec P L g tile).descriptor :=
  ⟨⟨x.val, by rw [(queryTile_shape P L g tile).1]; exact x.isLt⟩,
    ⟨h.val, by rw [(queryTile_shape P L g tile).2.1]; exact h.isLt⟩,
    ⟨byte.val, by rw [(queryTile_shape P L g tile).2.2]; exact byte.isLt⟩⟩

private theorem querySlot_coords (P : Params) (L : Launch) (g : Nat) (tile : Fin 8)
    (x h : Fin 64) (byte : Fin 2) :
    let s := queryTmaSpec P L g tile
    TensorTransfer.coord s.descriptor s.origin s.rows (queryTileSlot P L g tile x h byte) =
      ![(↑(qCoord tile + x.val) : Int), ↑h.val, ↑(queryOf L g), ↑(batchOf L g)] := by
  dsimp only [queryTmaSpec]
  have hmod : h.val % 64 = h.val := Nat.mod_eq_of_lt h.isLt
  have hdiv : h.val / 64 = 0 := Nat.div_eq_of_lt h.isLt
  funext i
  fin_cases i <;>
    simp [TensorTransfer.coord, TensorTransfer.index, queryTileSlot, TensorTile.coord,
      TensorTile.indexOf, TensorTile.unflatten, TensorTile.count, TensorTile.step, mapQ,
      encodeTiled, Fin.cases, hmod, hdiv]
  all_goals rfl

/-- The source byte of a query tile is in the contiguous launch Q tensor. -/
theorem queryTile_global {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (hg : g < L.threads) (tile : Fin 8) (x h : Fin 64) (byte : Fin 2) :
    let s := queryTmaSpec P L g tile
    s.toTensorBox.globalAddress (queryTileSlot P L g tile x h byte) =
      some (P.qBase + 2 * (((batchOf L g * P.s_q + queryOf L g) * 64 + h.val) * 512
        + qCoord tile + x.val) + byte.val) := by
  dsimp only
  rw [TensorBox.globalAddress, TensorTransfer.globalAddress, querySlot_coords]
  let c := qCoord tile + x.val
  have hc : c < 512 := by dsimp [c, qCoord]; omega
  have hh := h.isLt
  let geom := TensorDescriptor.geometry
    (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass)
  let coord : Fin 4 → Int := ![↑c, ↑h.val, ↑(queryOf L g), ↑(batchOf L g)]
  have hq := queryOf_lt hpre hg
  have he := batchOf_lt hpre hg
  have hin : TensorAddress.InBounds geom coord := by
    intro i
    fin_cases i <;> simp [geom, coord, TensorDescriptor.geometry, mapQ, encodeTiled, hc, hh, hq, he]
  have hbyte : byte.val < geom.elementBytes := byte.isLt
  change TensorAddress.lookup geom coord byte.val = _
  unfold TensorAddress.lookup
  rw [ite_eq_left ⟨hin, hbyte⟩]
  congr 1
  simp [TensorAddress.byteAddress, TensorDescriptor.geometry, geom, coord, mapQ, encodeTiled,
    Fin.sum_univ_succ, Fin.cases, TensorDescriptor.Format.bytes]
  unfold c
  ring

/-- The input byte read by a TMA slot has the value fixed by the logical query. -/
theorem queryTile_initial {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (hg : g < L.threads) (tile : Fin 8) (x h : Fin 64) (byte : Fin 2) :
    let s := queryTmaSpec P L g tile
    ∃ address, TensorCopy.source s (queryTileSlot P L g tile x h byte) = .global address ∧
      mem0 ⟨.global, 0, address⟩ = some (some (.float .bf16
        (P.q (batchOf L g) (queryOf L g) h.val (qCoord tile + x.val)), byte.val)) := by
  dsimp only
  have hsrc := queryTile_global hpre hg tile x h byte
  have hlim : qCoord tile + x.val < 512 := by dsimp [qCoord]; omega
  have hmem := hpre.qInput _ (batchOf_lt hpre hg) _ (queryOf_lt hpre hg)
    _ h.isLt _ hlim _ byte.isLt
  refine ⟨P.qBase + 2 * (((batchOf L g * P.s_q + queryOf L g) * 64 + h.val) * 512
    + qCoord tile + x.val) + byte.val, ?_, ?_⟩
  · rw [TensorCopy.source, hsrc]
  · simpa only [Loc.at, Value.byteAt, Nat.add_assoc] using hmem

/-- The query TMA slot's destination is the exact SW128 byte addressed by MMA geometry. -/
theorem queryTile_shared {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (g : Nat) (tile : Fin 8) (x h : Fin 64) (byte : Fin 2) :
    let s := queryTmaSpec P L g tile
    s.toTensorBox.sharedLoc (queryTileSlot P L g tile x h byte) =
      ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
        (kvLinearByte L 0 h.val (qCoord tile + x.val) byte.val)⟩ := by
  let base := L.sharedBase + qDstOff tile
  let n := h.val * 128 + x.val * 2 + byte.val
  have ha : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
  have hb : base % 128 = 0 := by unfold base qDstOff; omega
  have hx : (qCoord tile + x.val) / 64 = tile.val := by unfold qCoord; omega
  have hr : (qCoord tile + x.val) % 64 = x.val := by unfold qCoord; omega
  have hp : TensorTile.rowBytes (queryTmaSpec P L g tile).descriptor.box
      (queryTmaSpec P L g tile).descriptor.format.bytes (queryTmaSpec P L g tile).descriptor.swizzle
      = 128 := by
    rw [TensorTile.rowBytes, (queryTile_shape P L g tile).1, (queryTile_shape P L g tile).2.2]
    rfl
  dsimp only
  unfold TensorBox.sharedLoc TensorTile.sharedByte TensorTile.linearByte
  rw [hp]
  change (Loc.mk .shared (ctaOf L g) (base + TensorSwizzle.offset .b128 base n)) =
    Loc.mk .shared (ctaOf L g) (TensorSwizzle.offset .b128 0
      (kvLinearByte L 0 h.val (qCoord tile + x.val) byte.val))
  rw [← TensorSwizzle.offset_add_base .b128 base n hb]
  congr 2
  unfold kvLinearByte
  rw [hx, hr]
  dsimp [kvBase, base, n, qDstOff]
  omega

/-- The query A copy reads a byte supplied by the corresponding query TMA slot. -/
theorem queryCopy_tmaSlot {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (g : Nat) (issue : Fin 16) (row : Fin 128) (k : Fin 16) (b : Fin 2) :
    ∃ (tile : Fin 8) (x h : Fin 64), qCoord tile + x.val = qkFeature issue row k ∧
      h.val = row.val % 64 ∧
      let cp := queryCopySpec L g issue
      let tma := queryTmaSpec P L g tile
      TcCopy.byteLoc cp.shape cp.src (ctaOf L g) (2 * (row.val * 16 + k.val) + b.val) =
        some (tma.toTensorBox.sharedLoc (queryTileSlot P L g tile x h b)) := by
  let feat := qkFeature issue row k
  have hlim : feat < 512 := by dsimp [feat, qkFeature]; omega
  let tile : Fin 8 := ⟨feat / 64, by omega⟩
  let x : Fin 64 := ⟨feat % 64, Nat.mod_lt _ (by decide)⟩
  let h : Fin 64 := ⟨row.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : qCoord tile + x.val = feat := by dsimp [qCoord, tile, x]; omega
  refine ⟨tile, x, h, he, rfl, ?_⟩
  dsimp only
  rw [queryCopyByteLoc, queryTile_shared hpre, he]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
