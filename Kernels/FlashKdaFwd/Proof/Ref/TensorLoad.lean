-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Lib
public import Lemmas.Flow.TensorLoadFacts
public import Lemmas.Flow.TmplOkSync
public import Lemmas.Tensor.BoxWrite
public import Lemmas.Tensor.BoxRead

@[expose] public section

/-! # A tensor load of the kernel, in closed form

Every tensor load of the kernel (16 of the initial state in the startup phase, 70 per tile in
the Producer phase) is one instruction form:

    cp.async.bulk.tensor.{1d,2d,3d}.shared::cluster.global.mbarrier::complete_tx::bytes
        .L2::cache_hint [dst], [map, {coordinates}], [mbar], policy

with a 32-bit register `dst` for the shared destination, a register `map` that holds the generic
address of a by-value parameter object (the destination of a `cvta.param.u64`; the thread machine
gives such a register the kind `gparamPtr i`, whose value is `.ptr 64 true (.param (paramName i))
0`), one 32-bit register per coordinate, a 32-bit register `mbar` for the completion mbarrier and
a 64-bit register for the cache policy.

This file states once what such an instruction does when its registers hold given numbers:

* `preMap P i`: the tensor map that the precondition gives parameter object `i` (its rank minus
  one and its descriptor, `Data/TensorMaps.lean`), with `pre_object`, `pre_map`,
  `preMap_valid`;
* `loadSpec P c i vs dst mb`: the copy of a load through map `i` at the coordinates `vs`, to
  byte `dst` of the shared window of block `c`, completing on the mbarrier at byte `mb` of that
  window;
* `reg_g`: the value of the map register at a concrete state of the thread machine;
* **`tensorLoad_event`**: the event of the instruction is exactly `.tensorIssue (P.objectBase i)
  (loadSpec …)`. In particular it is not undefined behaviour: the conclusion is an equation, and
  the lemma needs no hypothesis "the event is not undefined behaviour". Its premises are the
  register values, the alignment of the destination (128 bytes), of the mbarrier (8 bytes) and
  of the box (the first coordinate times the element size is a multiple of 16), coordinates
  below `2 ^ 31`, and the name equation `paramName i = param (objName i)` of the map's object
  (`Ref/ParamBridge.lean` and `Thread/ParamBridge.lean` prove these; each is a heavy kernel
  evaluation, so they are hypotheses here and this file stays cheap to import);
* what every user needs of the copy: its byte count (`preMap_bytes`: 256, 64, 512 or 4096 by
  map), its fill (`preMap_fill`: zero), its element format (`preMap_format`), its allocation
  class (`preMap_class`), its swizzle (`preMap_swizzle`: none, except the two state maps), and
  its **destination footprint** (`writeLoc_range`: every byte it writes is in
  `[dst, dst + bytes)` of the shared window of block `c`);
* the **source side**: the tensor coordinates of a slot of a box with unit traversal
  (`coord1`, `coord2`, `coord3`: the origin plus the column, and for rank 3 plus the row), and
  that a box that lies inside its tensor selects no element outside it (`noOob2`, `noOob3`).

Words: a *slot* `(x, y, k)` of a copy is byte `k` of the element in column `x` (the innermost
dimension) of row `y` of its box. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence TensorDescriptor

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-! ### The tensor maps of the launch -/

/-- The index of parameter object `i` as the specification writes it. -/
def objName (i : Fin 11) : String :=
  match i with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9" | 10 => "10"

/-- **The tensor map of parameter object `i`** under the precondition: its rank minus one and
its descriptor. -/
def preMap (P : Params) (i : Fin 11) : (outer : Nat) × Descriptor outer :=
  match i with
  | 0 => ⟨2, mapV P.valuesBase P.heads P.total (P.allocation 0)⟩
  | 1 => ⟨0, mapBeta P.logitsBase P.heads P.total (P.allocation 1)⟩
  | 2 => ⟨2, mapKDecayed P.workspaceBase P.heads P.totalTiles (P.allocation 2)⟩
  | 3 => ⟨2, mapQDecayed P.workspaceBase P.heads P.totalTiles (P.allocation 3)⟩
  | 4 => ⟨2, mapKRestored P.workspaceBase P.heads P.totalTiles (P.allocation 4)⟩
  | 5 => ⟨1, mapGTotal P.workspaceBase P.heads P.totalTiles (P.allocation 5)⟩
  | 6 => ⟨2, mapInv P.workspaceBase P.heads P.totalTiles (P.allocation 6)⟩
  | 7 => ⟨2, mapMqk P.workspaceBase P.heads P.totalTiles (P.allocation 7)⟩
  | 8 => ⟨2, mapInitialState P.initialBase P.sequences P.heads (P.allocation 8)⟩
  | 9 => ⟨2, mapFinalState P.finalBase P.sequences P.heads (P.allocation 9)⟩
  | 10 => ⟨2, mapOut P.outputBase P.heads P.total (P.allocation 10)⟩

/-- The launch binds parameter object `i` at `P.objectBase i`. -/
theorem pre_object (hpre : Pre P L mem0) (i : Fin 11) :
    L.paramObjects (param (objName i)) = some (mapObject (objName i), P.objectBase i) := by
  fin_cases i
  · exact hpre.object0
  · exact hpre.object1
  · exact hpre.object2
  · exact hpre.object3
  · exact hpre.object4
  · exact hpre.object5
  · exact hpre.object6
  · exact hpre.object7
  · exact hpre.object8
  · exact hpre.object9
  · exact hpre.object10

/-- The launch publishes the tensor map of object `i` at the object's address. -/
theorem pre_map (hpre : Pre P L mem0) (i : Fin 11) :
    L.tensorMaps (P.objectBase i) = some (preMap P i) := by
  fin_cases i
  · exact hpre.map0
  · exact hpre.map1
  · exact hpre.map2
  · exact hpre.map3
  · exact hpre.map4
  · exact hpre.map5
  · exact hpre.map6
  · exact hpre.map7
  · exact hpre.map8
  · exact hpre.map9
  · exact hpre.map10

/-- The eleven maps satisfy the limits of the host interface. -/
theorem preMap_valid (hpre : Pre P L mem0) (i : Fin 11) : Valid (preMap P i).2 := by
  fin_cases i
  · exact hpre.mapVValid
  · exact hpre.mapBetaValid
  · exact hpre.mapKDecayedValid
  · exact hpre.mapQDecayedValid
  · exact hpre.mapKRestoredValid
  · exact hpre.mapGTotalValid
  · exact hpre.mapInvValid
  · exact hpre.mapMqkValid
  · exact hpre.mapInitialStateValid
  · exact hpre.mapFinalStateValid
  · exact hpre.mapOutValid

/-- The bytes one copy through map `i` moves: 8 elements of 16 rows of a bf16 array (256), the
32 gate logits of a box of `beta` (64), the 128 FP32 entries of `g_total` (512), 8 columns of
the 128 rows of an FP32 state plane (4096). -/
def mapBytes (i : Fin 11) : Nat :=
  match i with
  | 1 => 64
  | 5 => 512
  | 8 | 9 => 4096
  | _ => 256

/-- A map's fields that do not depend on the launch. -/
theorem preMap_fill (P : Params) (i : Fin 11) : (preMap P i).2.fill = .zero := by
  fin_cases i <;> rfl

theorem preMap_format (P : Params) (i : Fin 11) :
    (preMap P i).2.format = if i = 5 ∨ i = 8 ∨ i = 9 then .f32 else .bf16 := by
  fin_cases i <;> rfl

theorem preMap_format_ne (P : Params) (i : Fin 11) : (preMap P i).2.format ≠ .f64 := by
  fin_cases i <;> (intro h; cases h)

theorem preMap_class (P : Params) (i : Fin 11) :
    (preMap P i).2.allocationClass = P.allocation i := by
  fin_cases i <;> rfl

theorem preMap_bytes (P : Params) (i : Fin 11) :
    TensorTransfer.bytes (preMap P i).2 = mapBytes i := by
  fin_cases i <;>
    simp [preMap, mapBytes, TensorTransfer.bytes, TensorTile.count, TensorTile.rows,
      TensorTile.rowsOf, TensorTile.step, mapV, mapBeta, mapKDecayed, mapQDecayed, mapKRestored,
      mapGTotal, mapInv, mapMqk, mapInitialState, mapFinalState, mapOut, tokenMap, logitMap,
      tileRowsMap, totalDecayMap, tileSquareMap, stateMap, Format.bytes]

/-! ### The copy of a load -/

/-- **The copy of a tensor load** through map `i` at the coordinates `vs`, to byte `dst` of the
shared window of block `c`, completing on the mbarrier at byte `mb` of that window: a tile
copy (no row coordinates) through cluster addresses of CTA group one. -/
def loadSpec (P : Params) (c : Nat) (i : Fin 11) (vs : List Nat) (dst mb : Nat) :
    TensorCopy.Spec :=
  ⟨⟨(preMap P i).1, (preMap P i).2, fun axis => ((vs.getD axis.val 0 : Nat) : Int),
    ⟨.shared, c, dst⟩, none⟩, ⟨.shared, c, mb⟩, true, .one⟩

@[simp] theorem loadSpec_mbar (P : Params) (c : Nat) (i : Fin 11) (vs : List Nat) (dst mb : Nat) :
    (loadSpec P c i vs dst mb).mbar = ⟨.shared, c, mb⟩ := rfl

@[simp] theorem loadSpec_dst (P : Params) (c : Nat) (i : Fin 11) (vs : List Nat) (dst mb : Nat) :
    (loadSpec P c i vs dst mb).sharedBase = ⟨.shared, c, dst⟩ := rfl

theorem loadSpec_bytes (P : Params) (c : Nat) (i : Fin 11) (vs : List Nat) (dst mb : Nat) :
    TensorTransfer.bytes (loadSpec P c i vs dst mb).descriptor = mapBytes i :=
  preMap_bytes P i

theorem loadSpec_fill (P : Params) (c : Nat) (i : Fin 11) (vs : List Nat) (dst mb : Nat) :
    (loadSpec P c i vs dst mb).descriptor.fill = .zero ∧
      (loadSpec P c i vs dst mb).descriptor.format ≠ .f64 :=
  ⟨preMap_fill P i, preMap_format_ne P i⟩

theorem preMap_swizzle (P : Params) (i : Fin 11) :
    (preMap P i).2.swizzle = if i = 8 ∨ i = 9 then .b32 else .none := by
  fin_cases i <;> rfl

/-! ### The destination footprint -/

/-- A byte of a tile whose offset before swizzling is below `n` lies in the first `n` bytes of
the tile, when the tile has no swizzle or `n` is a whole number of 128-byte rows (the swizzle
permutes bytes inside a 128-byte row). -/
theorem sharedByte_range {outer : Nat} (b : TensorTile.Box (outer + 1)) (eb : Nat)
    (mode : TensorSwizzle.Mode) (base x y k n : Nat)
    (hlin : TensorTile.linearByte b eb mode x y k < n) (hn : mode = .none ∨ n % 128 = 0) :
    base ≤ TensorTile.sharedByte b eb mode base x y k ∧
      TensorTile.sharedByte b eb mode base x y k < base + n := by
  unfold TensorTile.sharedByte
  rcases hn with rfl | hn
  · rw [TensorSwizzle.offset_none]
    omega
  · have h := TensorSwizzle.offset_row mode base (TensorTile.linearByte b eb mode x y k)
    omega

/-- **The destination footprint of a load**: every byte it writes is one of the
`mapBytes i` bytes from `dst` on in the shared window of block `c`. -/
theorem writeLoc_range {c : Nat} {i : Fin 11} {vs : List Nat} {dst mb x y k : Nat} {l : Loc}
    (h : TensorCopy.writeLoc (loadSpec P c i vs dst mb) x y k = some l) :
    l.space = .shared ∧ l.cta = c ∧ dst ≤ l.addr ∧ l.addr < dst + mapBytes i := by
  obtain ⟨hx, hy, hk⟩ := TensorCopy.writeLoc_bounds h
  unfold TensorCopy.writeLoc TensorTransfer.slotAt at h
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hk, Option.map_some] at h
  obtain rfl := Option.some.inj h
  refine ⟨rfl, rfl, ?_⟩
  refine sharedByte_range _ _ _ dst x y k (mapBytes i) ?_ ?_
  · revert hx hy hk
    fin_cases i <;>
      simp [loadSpec, preMap, mapBytes, TensorTile.linearByte, TensorTile.rowBytes,
        TensorTile.swizzleWidth, TensorTile.count, TensorTile.rows, TensorTile.rowsOf,
        TensorTile.step, mapV, mapBeta, mapKDecayed, mapQDecayed, mapKRestored, mapGTotal, mapInv,
        mapMqk, mapInitialState, mapFinalState, mapOut, tokenMap, logitMap, tileRowsMap,
        totalDecayMap, tileSquareMap, stateMap, Format.bytes] <;> omega
  · fin_cases i <;> simp [loadSpec, preMap_swizzle, mapBytes]

/-! ### The source: coordinates of a slot, and boxes inside their tensor -/

/-- The coordinates of a slot of a rank-3 box with unit traversal and one plane. -/
theorem coord3 {d : Descriptor 2} (ht : ∀ a, d.box.traversal a = 1) (h2 : d.box.size 2 = 1)
    (origin : Fin 3 → Int) (slot : TensorTransfer.Slot d) :
    TensorTransfer.coord d origin none slot 0 = origin 0 + slot.1.val ∧
    TensorTransfer.coord d origin none slot 1 = origin 1 + slot.2.1.val ∧
    TensorTransfer.coord d origin none slot 2 = origin 2 := by
  have hc1 : TensorTile.count d.box 1 = d.box.size 1 := by
    simp [TensorTile.count, TensorTile.step, ht]
  have hc2 : TensorTile.count d.box 2 = 1 := by
    simp [TensorTile.count, TensorTile.step, ht, h2]
  have hrows : TensorTile.rows d.box = d.box.size 1 := by
    show TensorTile.count d.box 1 * TensorTile.count d.box 2 = _
    rw [hc1, hc2, Nat.mul_one]
  have hy : slot.2.1.val < d.box.size 1 := lt_of_lt_of_eq slot.2.1.isLt hrows
  refine ⟨?_, ?_, ?_⟩
  · simp [TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, TensorTile.indexOf,
      TensorTile.step]
  · have : slot.2.1.val % TensorTile.count d.box 1 = slot.2.1.val := by
      rw [hc1]; exact Nat.mod_eq_of_lt hy
    simp [TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, TensorTile.indexOf,
      TensorTile.unflatten, TensorTile.step, ht, this]
    rfl
  · have : slot.2.1.val / TensorTile.count d.box 1 = 0 := by
      rw [hc1]; exact Nat.div_eq_of_lt hy
    simp [TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, TensorTile.indexOf,
      TensorTile.unflatten, TensorTile.step, ht, this]
    rfl

/-- The coordinates of a slot of a rank-2 box with unit traversal and one row. -/
theorem coord2 {d : Descriptor 1} (ht : ∀ a, d.box.traversal a = 1) (h1 : d.box.size 1 = 1)
    (origin : Fin 2 → Int) (slot : TensorTransfer.Slot d) :
    TensorTransfer.coord d origin none slot 0 = origin 0 + slot.1.val ∧
    TensorTransfer.coord d origin none slot 1 = origin 1 := by
  have hrows : TensorTile.rows d.box = 1 := by
    show TensorTile.count d.box 1 = _
    simp [TensorTile.count, TensorTile.step, ht, h1]
  have hy : slot.2.1.val = 0 := by
    have := lt_of_lt_of_eq slot.2.1.isLt hrows
    omega
  refine ⟨?_, ?_⟩
  · simp [TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, TensorTile.indexOf,
      TensorTile.step]
  · simp [TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, TensorTile.indexOf,
      TensorTile.unflatten, TensorTile.step, ht, hy]
    rfl

/-- The coordinate of a slot of a rank-1 box. -/
theorem coord1 {d : Descriptor 0} (origin : Fin 1 → Int) (slot : TensorTransfer.Slot d) :
    TensorTransfer.coord d origin none slot 0 = origin 0 + slot.1.val := by
  simp [TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, TensorTile.indexOf,
    TensorTile.step]

/-- The columns of a box: its innermost size. -/
theorem count0 {outer : Nat} (d : Descriptor outer) : TensorTile.count d.box 0 = d.box.size 0 := by
  simp [TensorTile.count, TensorTile.step]

/-- The rows of a rank-3 box with unit traversal and one plane: its middle size. -/
theorem rows3 {d : Descriptor 2} (ht : ∀ a, d.box.traversal a = 1) (h2 : d.box.size 2 = 1) :
    TensorTile.rows d.box = d.box.size 1 := by
  have hc1 : TensorTile.count d.box 1 = d.box.size 1 := by
    simp [TensorTile.count, TensorTile.step, ht]
  have hc2 : TensorTile.count d.box 2 = 1 := by
    simp [TensorTile.count, TensorTile.step, ht, h2]
  show TensorTile.count d.box 1 * TensorTile.count d.box 2 = _
  rw [hc1, hc2, Nat.mul_one]

/-- **A rank-3 box inside its tensor selects no element outside it.** -/
theorem noOob3 {d : Descriptor 2} (ht : ∀ a, d.box.traversal a = 1) (h2 : d.box.size 2 = 1)
    {origin : Fin 3 → Int} {v0 v1 v2 : Nat} (ho0 : origin 0 = v0) (ho1 : origin 1 = v1)
    (ho2 : origin 2 = v2) (h0 : v0 + d.box.size 0 ≤ d.extent 0)
    (h1 : v1 + d.box.size 1 ≤ d.extent 1) (h2' : v2 < d.extent 2) :
    ¬ TensorHasOob d origin none := by
  rintro ⟨slot, hs⟩
  apply hs
  obtain ⟨c0, c1, c2⟩ := coord3 ht h2 origin slot
  have hx : slot.1.val < d.box.size 0 := lt_of_lt_of_eq slot.1.isLt (count0 d)
  have hy : slot.2.1.val < d.box.size 1 := lt_of_lt_of_eq slot.2.1.isLt (rows3 ht h2)
  intro axis
  fin_cases axis
  · show 0 ≤ TensorTransfer.coord d origin none slot 0 ∧
      TensorTransfer.coord d origin none slot 0 < ((d.extent 0 : Nat) : Int)
    rw [c0, ho0]
    omega
  · show 0 ≤ TensorTransfer.coord d origin none slot 1 ∧
      TensorTransfer.coord d origin none slot 1 < ((d.extent 1 : Nat) : Int)
    rw [c1, ho1]
    omega
  · show 0 ≤ TensorTransfer.coord d origin none slot 2 ∧
      TensorTransfer.coord d origin none slot 2 < ((d.extent 2 : Nat) : Int)
    rw [c2, ho2]
    omega

/-- **A rank-2 box inside its tensor selects no element outside it.** -/
theorem noOob2 {d : Descriptor 1} (ht : ∀ a, d.box.traversal a = 1) (h1 : d.box.size 1 = 1)
    {origin : Fin 2 → Int} {v0 v1 : Nat} (ho0 : origin 0 = v0) (ho1 : origin 1 = v1)
    (h0 : v0 + d.box.size 0 ≤ d.extent 0) (h1' : v1 < d.extent 1) :
    ¬ TensorHasOob d origin none := by
  rintro ⟨slot, hs⟩
  apply hs
  obtain ⟨c0, c1⟩ := coord2 ht h1 origin slot
  have hx : slot.1.val < d.box.size 0 := lt_of_lt_of_eq slot.1.isLt (count0 d)
  intro axis
  fin_cases axis
  · show 0 ≤ TensorTransfer.coord d origin none slot 0 ∧
      TensorTransfer.coord d origin none slot 0 < ((d.extent 0 : Nat) : Int)
    rw [c0, ho0]
    omega
  · show 0 ≤ TensorTransfer.coord d origin none slot 1 ∧
      TensorTransfer.coord d origin none slot 1 < ((d.extent 1 : Nat) : Int)
    rw [c1, ho1]
    omega

/-! ### The operands -/

/-- A register of kind `gparamPtr i` (the destination of a `cvta.param.u64` of parameter
object `i`) that is live at a state's site holds the generic address of the object. -/
theorem reg_g {d : D} (hat : (code L g).AtD d t) {r : Nat} (hr : r ∈ Flow.live d.site.pc)
    {i : Nat} (hk : kind r = .gparamPtr i) :
    t.regs r = some (.ptr 64 true (.param (paramName i)) 0) := by
  have h := regs_of_factsFrom hat.2.2.2.2 hr
  rw [h]
  simp only [valueOf, hk]

/-- The map operand: a register that holds the generic address of parameter object `i`
resolves to the object's address. -/
theorem mapAddress (hpre : Pre P L mem0) {i : Fin 11}
    (hname : paramName i.val = param (objName i)) {rm : Nat}
    (hr : t.regs rm = some (.ptr 64 true (.param (paramName i.val)) 0)) :
    tensorMapAddress L g t (.reg rm) = .ok (P.objectBase i) := by
  have ho := pre_object hpre i
  have ha := hpre.objectAlign i
  have hr' := hpre.objectRange i
  rw [← hname] at ho
  have hb : (mapObject (objName i)).bytes = 256 := by simp [mapObject, ParamObjectDecl.bytes]
  have hal : (mapObject (objName i)).alignment = 128 := rfl
  have hn : (mapObject (objName i)).name = paramName i.val := hname.symm
  simp only [tensorMapAddress, readValue, readReg, hr, bind, Except.bind, pure, Except.pure, ho,
    hb, hal, hn, ha, and_self, ↓reduceIte, show (128 : Nat) ≤ 256 by decide,
    show (0 : Nat) < 128 by decide, show P.objectBase i + 256 ≤ 2 ^ 64 from hr']

/-- A shared address held in a 32-bit register, read as a cluster address: the byte of the
thread's own block. -/
theorem sharedDst {r a : Nat} (hr : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) :
    sharedEffAddr L g t true r 0 = .ok ⟨.shared, g / L.block, a⟩ := by
  have hv : (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) + BitVec.ofInt 64 0)).toNat = a := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.ofInt_ofNat, BitVec.add_zero]
    omega
  simp only [sharedEffAddr, readReg, hr, b32, readBits, bind, Except.bind, pure, Except.pure, hv]

/-- The coordinate registers hold the coordinates. -/
theorem coords_read {rs vs : List Nat}
    (h : List.Forall₂ (fun r v => t.regs r = some (b32 v) ∧ v < 2 ^ 31) rs vs) :
    (rs.map Opnd.reg).mapM (readBits L g t 32) = .ok (vs.map (BitVec.ofNat 64)) := by
  induction h with
  | nil => rfl
  | cons hrv _ ih =>
    simp only [List.map_cons, List.mapM_cons, readBits_b32 hrv.1 (by omega), ih, bind,
      Except.bind, pure, Except.pure]

/-- The origin the model records for coordinates below `2 ^ 31`: the coordinates. -/
theorem coords_origin {rs vs : List Nat}
    (h : List.Forall₂ (fun r v => t.regs r = some (b32 v) ∧ v < 2 ^ 31) rs vs) (k : Nat) :
    (BitVec.ofNat 32 ((vs.map (BitVec.ofNat 64)).getD k 0).toNat).toInt =
      ((vs.getD k 0 : Nat) : Int) := by
  have key : ∀ x : Nat, x < 2 ^ 31 → (BitVec.ofNat 32 (BitVec.ofNat 64 x).toNat).toInt = x := by
    intro x hx
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact toInt_ofNat_lt32 hx
  induction h generalizing k with
  | nil => simp [List.getD]
  | cons hrv _ ih =>
    cases k with
    | zero => simpa [List.getD] using key _ hrv.2
    | succ k => simpa [List.getD] using ih k

/-- A copy to and an mbarrier of the issuer's own block are routed correctly. -/
theorem ownRoute (hpre : Pre P L mem0) (hg : g < L.threads) (a m : Nat) :
    TensorRoute L (g / L.block) true .one ⟨.shared, g / L.block, a⟩ ⟨.shared, g / L.block, m⟩ := by
  have hc : g / L.block < L.grid := by
    rw [block_div hpre, hpre.grid]
    exact cta_lt hpre hg
  have hin : CtaInCluster L (g / L.block) (g / L.block) := ⟨hc, hc, rfl⟩
  refine ⟨hpre.launchValid.1, rfl, rfl, hin, hin, fun h => ?_,
    (sameCtaGroup_iff L .one _ _).2 ⟨hin, rfl⟩⟩
  cases h

/-! ### The event -/

/-- **A tensor load of the kernel fires exactly its issue event**: the copy `loadSpec` through
the map of parameter object `i`, from the values of its registers. `rs` are the coordinate
registers and `vs` their values; `a` and `m` are the shared addresses in the destination and the
mbarrier register. -/
theorem tensorLoad_event (hpre : Pre P L mem0) (hg : g < L.threads) {i : Fin 11}
    (hname : paramName i.val = param (objName i)) {pc dst rm mb pol a m : Nat}
    {rs vs : List Nat} {x : BitVec 64} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensor true false dst 0 (.reg rm) (rs.map Opnd.reg) mb 0 none .tile (some (.reg pol))))
      e o)
    (hrm : t.regs rm = some (.ptr 64 true (.param (paramName i.val)) 0))
    (hdst : t.regs dst = some (b32 a)) (ha : a < 2 ^ 32) (ha128 : a % 128 = 0)
    (hmb : t.regs mb = some (b32 m)) (hm : m < 2 ^ 32) (hm8 : m % 8 = 0)
    (hpol : t.regs pol = some (.bits 64 x))
    (hcs : List.Forall₂ (fun r v => t.regs r = some (b32 v) ∧ v < 2 ^ 31) rs vs)
    (hlen : rs.length = (preMap P i).1 + 1)
    (hbox : vs.getD 0 0 * (preMap P i).2.format.bytes % 16 = 0) :
    e = ⟨pc, .tensorIssue (P.objectBase i) (loadSpec P (g / L.block) i vs a m)⟩ ∧
      o = some (next t) := by
  have hobj := hpre.objectAlign i
  have hpolicy : cachePolicyRead L g t (some (.reg pol)) = .ok () := by
    simp only [cachePolicyRead, readBits, readReg, hpol, bind, Except.bind, pure, Except.pure]
  have hmap : tensorMap L g t (.reg rm) (rs.map Opnd.reg) .tile =
      .ok (P.objectBase i, ⟨(preMap P i).1, (preMap P i).2⟩) := by
    simp only [tensorMap, mapAddress hpre hname hrm, bind, Except.bind, pure, Except.pure,
      pre_map hpre i, List.length_map, hlen, TensorMode.coordinates, preMap_valid hpre i,
      show P.objectBase i % 64 = 0 by omega, ↓reduceIte, true_or]
  have horigin : (fun axis : Fin ((preMap P i).1 + 1) =>
      (BitVec.ofNat 32 ((vs.map (BitVec.ofNat 64)).getD axis.val 0).toNat).toInt) =
      fun axis => ((vs.getD axis.val 0 : Nat) : Int) :=
    funext fun axis => coords_origin hcs axis.val
  have hbox' : requireBoxAligned (preMap P i).2
      (fun axis => ((vs.getD axis.val 0 : Nat) : Int)) = .ok () := by
    refine (requireBoxAligned_eq_ok _ _).2 ?_
    show ((vs.getD 0 0 : Nat) : Int) * ((preMap P i).2.format.bytes : Int) % 16 = 0
    exact_mod_cast hbox
  have hcopy : tensorLoadCopy L g t true false dst 0 (.reg rm) (rs.map Opnd.reg) mb 0 .tile =
      .ok (P.objectBase i, loadSpec P (g / L.block) i vs a m) := by
    simp only [tensorLoadCopy, bind, Except.bind, pure, Except.pure, hmap, sharedDst hdst ha,
      mbarClusterLoc_b32 hmb hm hm8, coords_read hcs, hbox', ha128, TensorMode.transfer,
      TensorMode.rowCoordinates, ↓reduceIte, horigin, Bool.false_eq_true, loadSpec]
  have htm : eventTmpl Assumptions.all L g t
      (.cpTensor true false dst 0 (.reg rm) (rs.map Opnd.reg) mb 0 none .tile (some (.reg pol))) =
      .tensorIssue (P.objectBase i) (loadSpec P (g / L.block) i vs a m) (next t) := by
    have hr := ownRoute hpre hg a m
    simp only [eventTmpl, tensorTmpl, hpolicy, hcopy, ofExec, bind, Except.bind, pure,
      Except.pure]
    rw [ite_eq_left (by simpa [loadSpec] using hr)]
  rw [htm] at hf
  exact hf

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref
