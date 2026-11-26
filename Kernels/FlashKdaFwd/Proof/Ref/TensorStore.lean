-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.TensorLoad
public import Lemmas.Flow.TensorStoreOrigin
public import Lemmas.Flow.TensorStoreOk

@[expose] public section

/-! # The event of a tensor store, in closed form

The kernel issues tensor stores (`cp.async.bulk.tensor.3d.global.shared::cta.bulk_group`) at two
places: the sixteen stores of a full output tile (tensor map `tma_store_out`, parameter object
10) and the sixteen stores of the final state (`tma_store_final_state`, parameter object 9).
Every one has the same operands: the tensor-map operand is a register that holds the generic
pointer to a by-value parameter object, three coordinate registers, and a 32-bit register with
the shared source address.

This file is the counterpart of `Ref/TensorLoad.lean` for stores and has its statement shape; it
takes the maps of the launch (`preMap`, `pre_object`, `pre_map`, `preMap_valid`, `objName`,
`mapBytes`) and the operand lemmas (`mapAddress`, `coords_read`, `coords_origin`,
`sharedByte_range`) from there. It is independent of the phase that uses it:

* `storeSpec P c i vs src`: the store through the map of parameter object `i` at the coordinates
  `vs`, from byte `src` of the shared window of block `c` (a tile store, no reduction);
* `tensorStore_tmpl`, `tensorStore_event`: the template of the instruction is the issue of
  `storeSpec` (so it is not undefined behaviour), and a firing store is exactly that event,
  from the values of its registers; there is no premise "the event is not undefined behaviour";
* `readLoc_range`: every shared byte the store reads is one of the `mapBytes i` bytes from
  `src` on, in block `c` (256 bytes for the output map, 4096 for the final-state map, whose
  32-byte swizzle permutes bytes only inside a 128-byte row);
* `noOob3_last`: a rank-3 box whose last selected element on every axis is inside the tensor
  selects no out-of-bounds element; `storeOut_noOob` and `storeFinal_noOob` are the two
  instances, in the form of the safety contract's `storeBounds`;
* `storeOut_writeLoc`, `storeOut_readLoc`: the global byte that the store of an output tile
  writes, and the shared byte it reads, for column `x`, row `y` and byte `k` of its box;
  `storeOut_slot`, `storeOut_writeLoc_lt`, `storeOut_readLoc_lt`: such a byte has `x < 8`,
  `y < 16`, `k < 2`.

The bulk group a store joins is the issuing thread's open group: the event carries no group
operand, and the group commit and wait events of the same thread delimit it. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence TensorDescriptor

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- **The specification of a tensor store** through map `i` at the coordinates `vs`, from byte
`src` of the shared window of block `c`: a tile store without reduction. -/
def storeSpec (P : Params) (c : Nat) (i : Fin 11) (vs : List Nat) (src : Nat) :
    TensorStore.Spec :=
  ⟨⟨(preMap P i).1, (preMap P i).2, fun axis => ((vs.getD axis.val 0 : Nat) : Int),
    ⟨.shared, c, src⟩, none⟩, none⟩

@[simp] theorem storeSpec_src (P : Params) (c : Nat) (i : Fin 11) (vs : List Nat) (src : Nat) :
    (storeSpec P c i vs src).sharedBase = ⟨.shared, c, src⟩ := rfl

/-- **The template of a tensor store of the kernel** is the issue of `storeSpec`, from the
values of its registers: `rm` holds the generic pointer to parameter object `i`, `rs` are the
coordinate registers and `vs` their values, `a` is the shared address in the source register. -/
theorem tensorStore_tmpl (hpre : Pre P L mem0) {A : List Assumption} {i : Fin 11}
    (hname : paramName i.val = param (objName i)) {src rm a : Nat} {rs vs : List Nat}
    (hrm : t.regs rm = some (.ptr 64 true (.param (paramName i.val)) 0))
    (hsrc : t.regs src = some (b32 a)) (ha : a < 2 ^ 32) (ha128 : a % 128 = 0)
    (hcs : List.Forall₂ (fun r v => t.regs r = some (b32 v) ∧ v < 2 ^ 31) rs vs)
    (hlen : rs.length = (preMap P i).1 + 1)
    (hbox : vs.getD 0 0 * (preMap P i).2.format.bytes % 16 = 0) :
    eventTmpl A L g t (.cpTensorStore (.reg rm) (rs.map Opnd.reg) src 0 none .tile none) =
      .tensorStore (P.objectBase i) (storeSpec P (g / L.block) i vs a) (next t) := by
  have hobj := hpre.objectAlign i
  have hmap : tensorMap L g t (.reg rm) (rs.map Opnd.reg) .tile =
      .ok (P.objectBase i, ⟨(preMap P i).1, (preMap P i).2⟩) := by
    simp only [tensorMap, mapAddress hpre hname hrm, bind, Except.bind, pure, Except.pure,
      pre_map hpre i, List.length_map, hlen, TensorMode.coordinates, preMap_valid hpre i,
      show P.objectBase i % 64 = 0 by omega, ↓reduceIte, true_or]
  have horigin : (fun axis : Fin ((preMap P i).1 + 1) =>
      (BitVec.ofNat 32 ((vs.map (BitVec.ofNat 64)).getD axis.val 0).toNat).toInt) =
      fun axis => ((vs.getD axis.val 0 : Nat) : Int) :=
    funext fun axis => coords_origin hcs axis.val
  have hpos : ∀ axis : Fin ((preMap P i).1 + 1),
      0 ≤ (BitVec.ofNat 32 ((vs.map (BitVec.ofNat 64)).getD axis.val 0).toNat).toInt := by
    intro axis
    rw [coords_origin hcs axis.val]
    exact Int.natCast_nonneg _
  have hbox' : requireBoxAligned (preMap P i).2
      (fun axis => ((vs.getD axis.val 0 : Nat) : Int)) = .ok () := by
    refine (requireBoxAligned_eq_ok _ _).2 ?_
    show ((vs.getD 0 0 : Nat) : Int) * ((preMap P i).2.format.bytes : Int) % 16 = 0
    exact_mod_cast hbox
  have hspec : tensorStoreSpec L g t (.reg rm) (rs.map Opnd.reg) src 0 none .tile none =
      .ok (P.objectBase i, storeSpec P (g / L.block) i vs a) := by
    simp only [tensorStoreSpec, bind, Except.bind, pure, Except.pure, hmap,
      sharedEffAddr_b32 hsrc ha, coords_read hcs, horigin, hpos, hbox', ha128, Option.all,
      cachePolicyRead, TensorMode.transfer, TensorMode.rowCoordinates, ↓reduceIte, storeSpec,
      implies_true, true_or]
  simp only [eventTmpl, tensorStoreTmpl, hspec, bind, Except.bind, pure, Except.pure, ofExec]

/-- **A tensor store of the kernel fires exactly its issue event**, and the thread continues. -/
theorem tensorStore_event (hpre : Pre P L mem0) {A : List Assumption} {i : Fin 11}
    (hname : paramName i.val = param (objName i)) {pc src rm a : Nat} {rs vs : List Nat}
    {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t
      (.cpTensorStore (.reg rm) (rs.map Opnd.reg) src 0 none .tile none)) e o)
    (hrm : t.regs rm = some (.ptr 64 true (.param (paramName i.val)) 0))
    (hsrc : t.regs src = some (b32 a)) (ha : a < 2 ^ 32) (ha128 : a % 128 = 0)
    (hcs : List.Forall₂ (fun r v => t.regs r = some (b32 v) ∧ v < 2 ^ 31) rs vs)
    (hlen : rs.length = (preMap P i).1 + 1)
    (hbox : vs.getD 0 0 * (preMap P i).2.format.bytes % 16 = 0) :
    e = ⟨pc, .tensorStore (P.objectBase i) (storeSpec P (g / L.block) i vs a)⟩ ∧
      o = some (next t) := by
  rw [tensorStore_tmpl hpre hname hrm hsrc ha ha128 hcs hlen hbox] at hf
  exact hf

/-! ### The shared bytes a store reads -/

/-- **The read footprint of a store**: every byte it reads is one of the `mapBytes i` bytes
from `src` on in the shared window of block `c`. -/
theorem readLoc_range {c : Nat} {i : Fin 11} {vs : List Nat} {src x y k : Nat} {l : Loc}
    (h : TensorStore.readLoc (storeSpec P c i vs src) x y k = some l) :
    l.space = .shared ∧ l.cta = c ∧ src ≤ l.addr ∧ l.addr < src + mapBytes i := by
  simp only [TensorStore.readLoc, Option.map_eq_some_iff] at h
  obtain ⟨⟨⟨x', hx⟩, ⟨y', hy⟩, ⟨k', hk⟩⟩, -, rfl⟩ := h
  refine ⟨rfl, rfl, ?_⟩
  refine sharedByte_range _ _ _ src x' y' k' (mapBytes i) ?_ ?_
  · revert hx hy hk
    fin_cases i <;>
      simp [storeSpec, preMap, mapBytes, TensorTile.linearByte, TensorTile.rowBytes,
        TensorTile.swizzleWidth, TensorTile.count, TensorTile.rows, TensorTile.rowsOf,
        TensorTile.step, mapV, mapBeta, mapKDecayed, mapQDecayed, mapKRestored, mapGTotal, mapInv,
        mapMqk, mapInitialState, mapFinalState, mapOut, tokenMap, logitMap, tileRowsMap,
        totalDecayMap, tileSquareMap, stateMap, Format.bytes] <;> omega
  · fin_cases i <;> simp [storeSpec, preMap_swizzle, mapBytes]

/-! ### No out-of-bounds element -/

/-- **A rank-3 box inside the tensor selects no out-of-bounds element**: on every axis the
origin is nonnegative and the last selected element is below the extent. -/
theorem noOob3_last {d : Descriptor 2} {origin : Fin 3 → Int}
    (h : ∀ axis, 0 ≤ origin axis ∧ origin axis +
      ((TensorTile.count d.box axis - 1) * TensorTile.step d.box axis : Nat) <
        (d.extent axis : Int))
    (h1 : 0 < TensorTile.count d.box 1) : ¬ TensorHasOob d origin none := by
  rintro ⟨⟨⟨col, hcol⟩, ⟨row, hrow⟩, byte⟩, hns⟩
  apply hns
  have hr : row < TensorTile.count d.box 1 * TensorTile.count d.box 2 := hrow
  have h2 : row / TensorTile.count d.box 1 < TensorTile.count d.box 2 :=
    Nat.div_lt_of_lt_mul hr
  have h3 : row % TensorTile.count d.box 1 < TensorTile.count d.box 1 := Nat.mod_lt _ h1
  have key : ∀ (axis : Fin 3) (i : Nat), i < TensorTile.count d.box axis →
      0 ≤ origin axis + ((i * TensorTile.step d.box axis : Nat) : Int) ∧
      origin axis + ((i * TensorTile.step d.box axis : Nat) : Int) < (d.extent axis : Int) := by
    intro axis i hi
    have hle : i * TensorTile.step d.box axis ≤
        (TensorTile.count d.box axis - 1) * TensorTile.step d.box axis :=
      Nat.mul_le_mul_right _ (by omega)
    have := h axis
    omega
  intro axis
  simp only [TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, TensorTile.indexOf,
    TensorTile.unflatten, geometry]
  fin_cases axis
  · exact key 0 col hcol
  · exact key 1 _ h3
  · exact key 2 _ h2

/-! ### The two store maps of the kernel -/

/-- **A store of an output tile is in bounds**: 8 features from `x0`, 16 tokens from `x1`, head
`x2` of the `[T_total, H, 128]` output array. -/
theorem storeOut_noOob {c x0 x1 x2 src : Nat} (h0 : x0 + 8 ≤ 128) (h1 : x1 + 16 ≤ P.total)
    (h2 : x2 < P.heads) :
    ¬ TensorHasOob (storeSpec P c 10 [x0, x1, x2] src).descriptor
      (storeSpec P c 10 [x0, x1, x2] src).origin (storeSpec P c 10 [x0, x1, x2] src).rows := by
  refine noOob3_last (d := tokenMap P.outputBase P.total P.heads (P.allocation 10))
    (fun axis => ?_) (by simp [tokenMap, TensorTile.count, TensorTile.step])
  fin_cases axis <;>
    simp [storeSpec, tokenMap, TensorTile.count, TensorTile.step] <;> omega

/-- **A store of the final state is in bounds**: 8 key columns from `x0`, the 128 rows (`x1`
is 0) of plane `x2` of the `[N * H, 128, 128]` final-state array. -/
theorem storeFinal_noOob {c x0 x1 x2 src : Nat} (h0 : x0 + 8 ≤ 128) (h1 : x1 = 0)
    (h2 : x2 < P.sequences * P.heads) :
    ¬ TensorHasOob (storeSpec P c 9 [x0, x1, x2] src).descriptor
      (storeSpec P c 9 [x0, x1, x2] src).origin (storeSpec P c 9 [x0, x1, x2] src).rows := by
  refine noOob3_last (d := stateMap P.finalBase (P.sequences * P.heads) (P.allocation 9))
    (fun axis => ?_) (by simp [stateMap, TensorTile.count, TensorTile.step])
  fin_cases axis <;>
    simp [storeSpec, stateMap, TensorTile.count, TensorTile.step] <;> omega

/-- **The global byte a store of an output tile writes** for column `x`, row `y` and byte `k`
of its box: byte `k` of feature `x0 + x` of token `x1 + y`, head `x2`, in the layout of
`Params.outLoc`. -/
theorem storeOut_writeLoc {c x0 x1 x2 src x y k : Nat} (hx : x < 8) (hy : y < 16) (hk : k < 2)
    (h0 : x0 + 8 ≤ 128) (h1 : x1 + 16 ≤ P.total) (h2 : x2 < P.heads) :
    TensorStore.writeLoc (storeSpec P c 10 [x0, x1, x2] src) x y k =
      some ⟨.global, 0, P.outputBase + 256 * ((x1 + y) * P.heads + x2) + 2 * (x0 + x) + k⟩ := by
  have hc : TensorTile.count (storeSpec P c 10 [x0, x1, x2] src).descriptor.box 0 = 8 := by
    simp [storeSpec, preMap, mapOut, tokenMap, TensorTile.count, TensorTile.step]
  have hr : TensorTile.rows (storeSpec P c 10 [x0, x1, x2] src).descriptor.box = 16 := by
    simp [storeSpec, preMap, mapOut, tokenMap, TensorTile.count, TensorTile.step,
      TensorTile.rows, TensorTile.rowsOf]
  have hb : (storeSpec P c 10 [x0, x1, x2] src).descriptor.format.bytes = 2 := by
    simp [storeSpec, preMap, mapOut, tokenMap, Format.bytes]
  have hslot : TensorTransfer.slotAt (storeSpec P c 10 [x0, x1, x2] src).descriptor x y k =
      some ⟨⟨x, hc ▸ hx⟩, ⟨y, hr ▸ hy⟩, ⟨k, hb ▸ hk⟩⟩ := by
    simp only [TensorTransfer.slotAt]
    rw [dite_eq_left (hc ▸ hx), dite_eq_left (hr ▸ hy), dite_eq_left (hb ▸ hk)]
  simp only [TensorStore.writeLoc, hslot, Option.bind_some, TensorStore.destination,
    TensorBox.globalAddress, TensorTransfer.globalAddress]
  simp [storeSpec, preMap, mapOut, tokenMap, TensorAddress.lookup, TensorAddress.byteAddress,
    geometry, TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, TensorTile.indexOf,
    TensorTile.unflatten, TensorTile.count, TensorTile.step, Format.bytes]
  have hy1 : y % 16 = y := Nat.mod_eq_of_lt hy
  have hy2 : y / 16 = 0 := Nat.div_eq_of_lt hy
  have e : ∀ a b : Nat, ((a : Int) + (b : Int)).toNat = a + b := fun a b => by omega
  simp [Fin.forall_fin_succ, hy1, hy2, e]
  refine ⟨⟨⟨by omega, by omega, h2⟩, by omega⟩, ?_⟩
  erw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ]
  simp
  ring

/-- **The shared byte a store of an output tile reads** for column `x`, row `y` and byte `k` of
its box: the box is not swizzled, its rows are 16 bytes (8 bf16 features) apart. -/
theorem storeOut_readLoc {c x0 x1 x2 src x y k : Nat} (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorStore.readLoc (storeSpec P c 10 [x0, x1, x2] src) x y k =
      some ⟨.shared, c, src + 16 * y + 2 * x + k⟩ := by
  have hc : TensorTile.count (storeSpec P c 10 [x0, x1, x2] src).descriptor.box 0 = 8 := by
    simp [storeSpec, preMap, mapOut, tokenMap, TensorTile.count, TensorTile.step]
  have hr : TensorTile.rows (storeSpec P c 10 [x0, x1, x2] src).descriptor.box = 16 := by
    simp [storeSpec, preMap, mapOut, tokenMap, TensorTile.count, TensorTile.step,
      TensorTile.rows, TensorTile.rowsOf]
  have hb : (storeSpec P c 10 [x0, x1, x2] src).descriptor.format.bytes = 2 := by
    simp [storeSpec, preMap, mapOut, tokenMap, Format.bytes]
  have hslot : TensorTransfer.slotAt (storeSpec P c 10 [x0, x1, x2] src).descriptor x y k =
      some ⟨⟨x, hc ▸ hx⟩, ⟨y, hr ▸ hy⟩, ⟨k, hb ▸ hk⟩⟩ := by
    simp only [TensorTransfer.slotAt]
    rw [dite_eq_left (hc ▸ hx), dite_eq_left (hr ▸ hy), dite_eq_left (hb ▸ hk)]
  simp only [TensorStore.readLoc, hslot, Option.map_some, TensorBox.sharedLoc]
  simp [storeSpec, preMap, mapOut, tokenMap, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, TensorTile.swizzleWidth, TensorTile.count, TensorTile.step,
    Format.bytes, TensorSwizzle.offset_none]
  omega

/-- **A slot of a store of an output tile**: its column is below 8, its row below 16 and its
byte below 2 (8 bf16 features of 16 tokens). -/
theorem storeOut_slot {c x0 x1 x2 src x y k : Nat}
    (h : (TensorTransfer.slotAt (storeSpec P c 10 [x0, x1, x2] src).descriptor x y k).isSome) :
    x < 8 ∧ y < 16 ∧ k < 2 := by
  have hc : TensorTile.count (storeSpec P c 10 [x0, x1, x2] src).descriptor.box 0 = 8 := by
    simp [storeSpec, preMap, mapOut, tokenMap, TensorTile.count, TensorTile.step]
  have hr : TensorTile.rows (storeSpec P c 10 [x0, x1, x2] src).descriptor.box = 16 := by
    simp [storeSpec, preMap, mapOut, tokenMap, TensorTile.count, TensorTile.step,
      TensorTile.rows, TensorTile.rowsOf]
  have hb : (storeSpec P c 10 [x0, x1, x2] src).descriptor.format.bytes = 2 := by
    simp [storeSpec, preMap, mapOut, tokenMap, Format.bytes]
  unfold TensorTransfer.slotAt at h
  split_ifs at h with h1 h2 h3
  · exact ⟨hc ▸ h1, hr ▸ h2, hb ▸ h3⟩
  all_goals simp at h

/-- A byte that a store of an output tile writes belongs to a slot of its box. -/
theorem storeOut_writeLoc_lt {c x0 x1 x2 src x y k : Nat} {l : Loc}
    (h : TensorStore.writeLoc (storeSpec P c 10 [x0, x1, x2] src) x y k = some l) :
    x < 8 ∧ y < 16 ∧ k < 2 := by
  refine storeOut_slot (P := P) (c := c) (x0 := x0) (x1 := x1) (x2 := x2) (src := src) ?_
  unfold TensorStore.writeLoc at h
  cases hs : TensorTransfer.slotAt (storeSpec P c 10 [x0, x1, x2] src).descriptor x y k with
  | none => simp [hs] at h
  | some slot => rfl

/-- A byte that a store of an output tile reads belongs to a slot of its box. -/
theorem storeOut_readLoc_lt {c x0 x1 x2 src x y k : Nat} {l : Loc}
    (h : TensorStore.readLoc (storeSpec P c 10 [x0, x1, x2] src) x y k = some l) :
    x < 8 ∧ y < 16 ∧ k < 2 := by
  refine storeOut_slot (P := P) (c := c) (x0 := x0) (x1 := x1) (x2 := x2) (src := src) ?_
  unfold TensorStore.readLoc at h
  cases hs : TensorTransfer.slotAt (storeSpec P c 10 [x0, x1, x2] src).descriptor x y k with
  | none => simp [hs] at h
  | some slot => rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref
