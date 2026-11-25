-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Shapes
public import Kernels.FlashKdaFwd.Proof.Ref.Swizzle

@[expose] public section

/-! # Epilogue phase: the bytes of the sixteen tensor stores of the final state

The `i`-th tensor store of the store leader of a block (`finalSpec P L g i`, `Inv.lean`) copies
a box of 8 key columns by the 128 value rows of the block's plane of the final-state array
(tensor map 9, FP32 elements, 4096 bytes) out of the shared state buffer. A *slot* `(x, y, k)`
of the store is byte `k < 4` of the element in column `x < 8` of row `y < 128` of the box.

* `final_slot_lt`: a slot that the store reads or writes is in these ranges.
* `final_writeLoc`: **the global byte a slot writes**: byte `k` of the entry `(row y, column
  8 i + x)` of the final state of the block's sequence and head, `Params.stateLoc` (this is the
  write-location closed form for map 9, the counterpart of `Ref/TensorStore.lean:
  storeOut_writeLoc`).
* `final_readLoc`: **the shared byte a slot reads**: the swizzle of the byte's logical address
  `S + 32768 + 4096 i + 32 y + 4 x + k` in the block's window (`Ref/Swizzle.lean: swzAbs_base`:
  the model's 32-byte tile swizzle of map 9 is the kernel's address swizzle `swzN`, for both
  parities of `S / 128`).
* `final_read_owner`: the compute thread that wrote that shared byte in the epilogue
  (`finalOwner`) is thread `32 (y / 32) + 4 x + y / 2 % 4` of the block.
* `final_read_in`: every byte the store reads is in the FP32 buffer of the block's window.
* `final_noOob`: the store selects no out-of-bounds element.
* `final_cover`: every byte of every entry of the block's plane is the write location of a slot
  of one of the sixteen stores.

`S` is `P.sharedBase`; `swzN_eq_swzAbs` identifies this phase's `swzN` with the shared
`Ref.swzAbs`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence TensorDescriptor

noncomputable section
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- This phase's swizzle is the reference layer's `swzAbs`. -/
theorem swzN_eq_swzAbs (a : Nat) : swzN a = swzAbs a := (swzAbs_eq_ite a).symm

/-! ### A store through the map of the final state -/

section Map9
variable {c x0 x2 src x y k : Nat}

theorem storeFinal_count :
    TensorTile.count (storeSpec P c 9 [x0, 0, x2] src).descriptor.box 0 = 8 := by
  simp [storeSpec, preMap, mapFinalState, stateMap, TensorTile.count, TensorTile.step]

theorem storeFinal_rows :
    TensorTile.rows (storeSpec P c 9 [x0, 0, x2] src).descriptor.box = 128 := by
  simp [storeSpec, preMap, mapFinalState, stateMap, TensorTile.count, TensorTile.step,
    TensorTile.rows, TensorTile.rowsOf]

theorem storeFinal_bytes : (storeSpec P c 9 [x0, 0, x2] src).descriptor.format.bytes = 4 := by
  simp [storeSpec, preMap, mapFinalState, stateMap, Format.bytes]

/-- The slot `(x, y, k)` of a store through map 9 exists exactly for `x < 8`, `y < 128`,
`k < 4`. -/
theorem storeFinal_slot (hx : x < 8) (hy : y < 128) (hk : k < 4) :
    TensorTransfer.slotAt (storeSpec P c 9 [x0, 0, x2] src).descriptor x y k =
      some ⟨⟨x, storeFinal_count ▸ hx⟩, ⟨y, storeFinal_rows ▸ hy⟩, ⟨k, storeFinal_bytes ▸ hk⟩⟩ := by
  simp only [TensorTransfer.slotAt]
  rw [dite_eq_left (storeFinal_count (P := P) ▸ hx), dite_eq_left (storeFinal_rows (P := P) ▸ hy),
    dite_eq_left (storeFinal_bytes (P := P) ▸ hk)]

theorem storeFinal_slot_lt
    (h : (TensorTransfer.slotAt (storeSpec P c 9 [x0, 0, x2] src).descriptor x y k).isSome) :
    x < 8 ∧ y < 128 ∧ k < 4 := by
  simp only [TensorTransfer.slotAt] at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      split at h
      · rename_i h3
        exact ⟨storeFinal_count (P := P) ▸ h1, storeFinal_rows (P := P) ▸ h2,
          storeFinal_bytes (P := P) ▸ h3⟩
      · cases h
    · cases h
  · cases h

/-- **The global byte a store through map 9 writes** for column `x`, row `y` and byte `k` of
its box: byte `k` of the entry `(row y, column x0 + x)` of plane `x2`. -/
theorem storeFinal_writeLoc (hx : x < 8) (hy : y < 128) (hk : k < 4) (h0 : x0 + 8 ≤ 128)
    (h2 : x2 < P.sequences * P.heads) :
    TensorStore.writeLoc (storeSpec P c 9 [x0, 0, x2] src) x y k =
      some ⟨.global, 0, P.finalBase + 65536 * x2 + 512 * y + 4 * (x0 + x) + k⟩ := by
  simp only [TensorStore.writeLoc, storeFinal_slot hx hy hk, Option.bind_some,
    TensorStore.destination, TensorBox.globalAddress, TensorTransfer.globalAddress]
  simp [storeSpec, preMap, mapFinalState, stateMap, TensorAddress.lookup,
    TensorAddress.byteAddress, geometry, TensorTransfer.coord, TensorTile.coord,
    TensorTransfer.index, TensorTile.indexOf, TensorTile.unflatten, TensorTile.count,
    TensorTile.step, Format.bytes]
  have hy1 : y % 128 = y := Nat.mod_eq_of_lt hy
  have hy2 : y / 128 = 0 := Nat.div_eq_of_lt hy
  have e : ∀ a b : Nat, ((a : Int) + (b : Int)).toNat = a + b := fun a b => by omega
  simp [Fin.forall_fin_succ, hy1, hy2, e]
  refine ⟨⟨⟨by omega, by omega, by exact_mod_cast h2⟩, by omega⟩, ?_⟩
  erw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ]
  simp
  ring

/-- **The shared byte a store through map 9 reads** for column `x`, row `y` and byte `k` of its
box, from a source address that is a multiple of 128: the swizzle of the logical address
`src + 32 y + 4 x + k`. -/
theorem storeFinal_readLoc (hx : x < 8) (hy : y < 128) (hk : k < 4) (hs : src % 128 = 0) :
    TensorStore.readLoc (storeSpec P c 9 [x0, 0, x2] src) x y k =
      some ⟨.shared, c, swzN (src + (32 * y + 4 * x + k))⟩ := by
  rw [swzN_eq_swzAbs, swzAbs_base _ _ hs]
  simp only [TensorStore.readLoc, storeFinal_slot hx hy hk, Option.map_some]
  simp [storeSpec, preMap, mapFinalState, stateMap, TensorBox.sharedLoc,
    TensorTile.sharedByte, TensorTile.linearByte, TensorTile.rowBytes, TensorTile.swizzleWidth,
    TensorTile.count, TensorTile.step, Format.bytes]
  congr 1
  omega

end Map9

/-! ### The sixteen stores of the final state -/

variable {x y k : Nat}

/-- A slot that a final-state store reads is in range. -/
theorem final_read_lt {i : Nat} {l : Loc}
    (h : TensorStore.readLoc (finalSpec P L g i) x y k = some l) : x < 8 ∧ y < 128 ∧ k < 4 := by
  rw [finalSpec_eq] at h
  simp only [TensorStore.readLoc, Option.map_eq_some_iff] at h
  obtain ⟨slot, hs, -⟩ := h
  exact storeFinal_slot_lt (by rw [hs]; rfl)

/-- A slot that a final-state store writes is in range. -/
theorem final_write_lt {i : Nat} {l : Loc}
    (h : TensorStore.writeLoc (finalSpec P L g i) x y k = some l) : x < 8 ∧ y < 128 ∧ k < 4 := by
  rw [finalSpec_eq] at h
  simp only [TensorStore.writeLoc, Option.bind_eq_some_iff] at h
  obtain ⟨slot, hs, -⟩ := h
  exact storeFinal_slot_lt (by rw [hs]; rfl)

/-- **The global byte that slot `(x, y, k)` of the `i`-th final-state store writes**: byte `k`
of the entry of value row `y` and key column `8 i + x` of the final state of the block's
sequence and head. -/
theorem final_writeLoc (hpre : Pre P L mem0) (hg : g < L.threads) (i : Fin 16) (hx : x < 8)
    (hy : y < 128) (hk : k < 4) :
    TensorStore.writeLoc (finalSpec P L g i.val) x y k =
      some ((P.stateLoc (seqOf P g) (headOf P g) ⟨y, hy⟩
        ⟨8 * i.val + x, by have := i.isLt; omega⟩).at k) := by
  have hi := i.isLt
  rw [finalSpec_eq, storeFinal_writeLoc hx hy hk (by omega) (plane_lt hpre hg)]
  simp only [Params.stateLoc, Loc.at, Nat.mul_comm P.heads]

/-- **The shared byte that slot `(x, y, k)` of the `i`-th final-state store reads**: the
swizzle of the logical address of the byte in the FP32 buffer of the block's window. -/
theorem final_readLoc (hpre : Pre P L mem0) (i : Fin 16) (hx : x < 8) (hy : y < 128)
    (hk : k < 4) :
    TensorStore.readLoc (finalSpec P L g i.val) x y k =
      some ⟨.shared, g / L.block,
        swzN (P.sharedBase + 32768 + 4096 * i.val + 32 * y + 4 * x + k)⟩ := by
  have ha := hpre.sharedAlignment
  rw [finalSpec_eq, storeFinal_readLoc hx hy hk (by omega)]
  congr 3
  omega

/-- **The compute thread that wrote the shared byte of a slot** of a final-state store. -/
theorem final_read_owner (i : Fin 16) (hx : x < 8) (hy : y < 128) (hk : k < 4) (c : Nat) :
    finalOwner P ⟨.shared, c, swzN (P.sharedBase + 32768 + 4096 * i.val + 32 * y + 4 * x + k)⟩ =
      32 * (y / 32) + 4 * x + y / 2 % 4 := by
  have hi := i.isLt
  unfold finalOwner
  rw [swzN_swzN]
  have e : P.sharedBase + 32768 + 4096 * i.val + 32 * y + 4 * x + k - P.sharedBase - 32768 =
      4096 * i.val + 32 * y + 4 * x + k := by omega
  rw [e]
  have d1 : (4096 * i.val + 32 * y + 4 * x + k) / 1024 = 4 * i.val + y / 32 := by omega
  have d2 : (4096 * i.val + 32 * y + 4 * x + k) / 4 = 8 * (128 * i.val + y) + x := by omega
  have d3 : (4096 * i.val + 32 * y + 4 * x + k) / 64 = 64 * i.val + y / 2 := by omega
  rw [d1, d2, d3]
  omega

/-- **Every byte a final-state store reads is in the FP32 buffer** of the issuer's block. -/
theorem final_read_in (i : Fin 16) {l : Loc}
    (h : TensorStore.readLoc (finalSpec P L g i.val) x y k = some l) :
    l.space = .shared ∧ l.cta = g / L.block ∧ P.sharedBase + 32768 ≤ l.addr ∧
      l.addr < P.sharedBase + 98304 := by
  have hi := i.isLt
  rw [finalSpec_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := readLoc_range h
  simp only [mapBytes] at h4
  exact ⟨h1, h2, by omega, by omega⟩

/-- **A final-state store selects no out-of-bounds element.** -/
theorem final_noOob (hpre : Pre P L mem0) (hg : g < L.threads) (i : Fin 16) :
    ¬ TensorHasOob (finalSpec P L g i.val).descriptor (finalSpec P L g i.val).origin
      (finalSpec P L g i.val).rows := by
  have hi := i.isLt
  rw [finalSpec_eq]
  exact storeFinal_noOob (by omega) rfl (plane_lt hpre hg)

/-- **The sixteen stores cover the plane**: every byte of every entry of the final state of the
block's sequence and head is the write location of a slot of one of them. -/
theorem final_cover (hpre : Pre P L mem0) (hg : g < L.threads) (v kk : Fin 128) {b : Nat}
    (hb : b < 4) : ∃ i : Fin 16, ∃ x,
      TensorStore.writeLoc (finalSpec P L g i.val) x v.val b =
        some ((P.stateLoc (seqOf P g) (headOf P g) v kk).at b) := by
  have hk := kk.isLt
  refine ⟨⟨kk.val / 8, by omega⟩, kk.val % 8, ?_⟩
  rw [final_writeLoc hpre hg ⟨kk.val / 8, by omega⟩ (Nat.mod_lt _ (by decide)) v.isLt hb]
  congr 3
  exact Fin.ext (by simp only; omega)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
