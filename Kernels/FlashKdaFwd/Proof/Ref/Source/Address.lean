-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.TensorLoad
public import Kernels.FlashKdaFwd.Proof.Ref.Swizzle
public import Lemmas.Tensor.LoadWritten

@[expose] public section

/-! # The bytes of a tensor load, in closed form (generic part)

A tensor load ("copy") moves a box of a global tensor into shared memory. The model
(`Core/Async/Tensor`) describes it byte by byte: a *slot* `(x, y, k)` is byte `k` of the element
in column `x` (the innermost dimension) of row `y` of the box; the load reads the slot's global
byte (`TensorCopy.readLoc`), or nothing when the element is outside the tensor, and writes the
slot's shared byte (`TensorCopy.writeLoc`) with the byte it read, or with the descriptor's fill.

This file states these three things without the model's intermediate definitions, for the boxes
the kernel uses: every dimension is traversed with stride one, and the box spans one index of
its last dimension (ranks 2 and 3). Nothing here names the kernel's maps.

* `copyOf d origin sb mb`: the copy through descriptor `d` of the box at `origin`, to the shared
  location `sb`, completing on the mbarrier `mb` (what `Ref/TensorLoad.lean: loadSpec` builds);
  `originOf vs`: the origin given by the list `vs` of the instruction's coordinates.
* **Source address**: `readLoc1`, `readLoc2`, `readLoc3` (rank 1, 2, 3): for a slot of the box,
  `readLoc` is the byte `base + Σ coordinate × stride + k` when every coordinate is below its
  extent, and nothing otherwise. `readLoc_of_source` turns the model's `source` of a slot into a
  `readLoc`.
* **Destination address**: `writeLoc_plain` (no swizzle: `sb + y × row bytes + x × element
  bytes + k`) and `writeLoc_b32` (the 32-byte swizzle of a tile whose base is a multiple of 128:
  the kernel's swizzle `swzAbs` of the same address).
* **Content**, for the record `rec` of a load in a consistent execution, once the load has
  notified its mbarrier (only then has it written every slot): `writeByte_copied` (a slot whose
  global byte has a launch value that no write covers holds that value) and `writeByte_filled`
  (a slot outside the tensor holds the byte of the descriptor's fill). `spec_of_issue` says the
  record of an issue event is of the issue's copy.

Words: the *record* of a load is the model's observation of what the load has done so far
(`Execution.tensor`); it is *notified* when the load has signalled its mbarrier. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
open PTX TensorDescriptor
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Ref

noncomputable section

/-- **A tile copy**: through descriptor `d`, the box at `origin`, to the shared location `sb`,
completing on the mbarrier `mb`, with cluster addresses and CTA group one. -/
abbrev copyOf {outer : Nat} (d : Descriptor outer) (origin : Fin (outer + 1) → Int)
    (sb mb : Loc) : TensorCopy.Spec := ⟨⟨outer, d, origin, sb, none⟩, mb, true, .one⟩

/-- **The origin of a box** from the coordinates of the instruction, innermost first (what
`Ref/TensorLoad.lean: loadSpec` records). -/
abbrev originOf {n : Nat} (vs : List Nat) : Fin n → Int :=
  fun axis => ((vs.getD axis.val 0 : Nat) : Int)

/-- The slot of a position inside the box. -/
theorem slotAt_eq {outer : Nat} (d : Descriptor outer) {x y k : Nat}
    (hx : x < TensorTile.count d.box 0) (hy : y < TensorTile.rows d.box)
    (hk : k < d.format.bytes) :
    TensorTransfer.slotAt d x y k = some ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨k, hk⟩⟩ := by
  unfold TensorTransfer.slotAt
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hk]

/-- The rows of a rank-2 box with unit traversal that spans one index of dimension 1. -/
theorem rows2 {d : Descriptor 1} (ht : ∀ a, d.box.traversal a = 1) (h1 : d.box.size 1 = 1) :
    TensorTile.rows d.box = 1 := by
  show TensorTile.count d.box 1 = _
  simp [TensorTile.count, TensorTile.step, ht, h1]

/-- A rank-1 box has one row. -/
theorem rows1 (d : Descriptor 0) : TensorTile.rows d.box = 1 := rfl

/-! ### The global address of a slot -/

/-- **Rank 3**: the global address of a slot of a box with unit traversal that spans one index of
dimension 2. -/
theorem globalAddress3 {d : Descriptor 2} (ht : ∀ a, d.box.traversal a = 1)
    (h2 : d.box.size 2 = 1) {origin : Fin 3 → Int} {v0 v1 v2 : Nat} (ho0 : origin 0 = v0)
    (ho1 : origin 1 = v1) (ho2 : origin 2 = v2) (slot : TensorTransfer.Slot d) :
    TensorTransfer.globalAddress d origin none slot =
      if v0 + slot.1.val < d.extent 0 ∧ v1 + slot.2.1.val < d.extent 1 ∧ v2 < d.extent 2 then
        some (d.base + ((v0 + slot.1.val) * d.format.bytes +
          (v1 + slot.2.1.val) * d.outerStride 0 + v2 * d.outerStride 1) + slot.2.2.val)
      else none := by
  obtain ⟨c0, c1, c2⟩ := coord3 ht h2 origin slot
  rw [ho0] at c0
  rw [ho1] at c1
  rw [ho2] at c2
  have hb : slot.2.2.val < (geometry d).elementBytes := slot.2.2.isLt
  unfold TensorTransfer.globalAddress TensorAddress.lookup
  by_cases h : v0 + slot.1.val < d.extent 0 ∧ v1 + slot.2.1.val < d.extent 1 ∧ v2 < d.extent 2
  · have hc : ∀ axis : Fin 3, 0 ≤ TensorTransfer.coord d origin none slot axis ∧
        TensorTransfer.coord d origin none slot axis <
          (((geometry d).extent axis : Nat) : Int) := by
      intro axis
      fin_cases axis
      · show 0 ≤ TensorTransfer.coord d origin none slot 0 ∧
          TensorTransfer.coord d origin none slot 0 < ((d.extent 0 : Nat) : Int)
        rw [c0]
        omega
      · show 0 ≤ TensorTransfer.coord d origin none slot 1 ∧
          TensorTransfer.coord d origin none slot 1 < ((d.extent 1 : Nat) : Int)
        rw [c1]
        omega
      · show 0 ≤ TensorTransfer.coord d origin none slot 2 ∧
          TensorTransfer.coord d origin none slot 2 < ((d.extent 2 : Nat) : Int)
        rw [c2]
        omega
    rw [ite_eq_left h, ite_eq_left ⟨hc, hb⟩]
    unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_three, c0, c1, c2]
    show some (d.base + (((v0 : Int) + (slot.1.val : Int)).toNat * d.format.bytes +
      ((v1 : Int) + (slot.2.1.val : Int)).toNat * d.outerStride 0 +
      ((v2 : Nat) : Int).toNat * d.outerStride 1) + slot.2.2.val) = _
    rw [show ((v0 : Int) + (slot.1.val : Int)).toNat = v0 + slot.1.val by omega,
      show ((v1 : Int) + (slot.2.1.val : Int)).toNat = v1 + slot.2.1.val by omega,
      Int.toNat_natCast]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨hc, -⟩
    apply h
    have h0 := hc 0
    have h1 := hc 1
    have h2' := hc 2
    rw [c0] at h0
    rw [c1] at h1
    rw [c2] at h2'
    change _ ∧ _ < ((d.extent 0 : Nat) : Int) at h0
    change _ ∧ _ < ((d.extent 1 : Nat) : Int) at h1
    change _ ∧ _ < ((d.extent 2 : Nat) : Int) at h2'
    omega

/-- **Rank 2**: the global address of a slot of a box with unit traversal that spans one index of
dimension 1. -/
theorem globalAddress2 {d : Descriptor 1} (ht : ∀ a, d.box.traversal a = 1)
    (h1 : d.box.size 1 = 1) {origin : Fin 2 → Int} {v0 v1 : Nat} (ho0 : origin 0 = v0)
    (ho1 : origin 1 = v1) (slot : TensorTransfer.Slot d) :
    TensorTransfer.globalAddress d origin none slot =
      if v0 + slot.1.val < d.extent 0 ∧ v1 < d.extent 1 then
        some (d.base + ((v0 + slot.1.val) * d.format.bytes + v1 * d.outerStride 0) +
          slot.2.2.val)
      else none := by
  obtain ⟨c0, c1⟩ := coord2 ht h1 origin slot
  rw [ho0] at c0
  rw [ho1] at c1
  have hb : slot.2.2.val < (geometry d).elementBytes := slot.2.2.isLt
  unfold TensorTransfer.globalAddress TensorAddress.lookup
  by_cases h : v0 + slot.1.val < d.extent 0 ∧ v1 < d.extent 1
  · have hc : ∀ axis : Fin 2, 0 ≤ TensorTransfer.coord d origin none slot axis ∧
        TensorTransfer.coord d origin none slot axis <
          (((geometry d).extent axis : Nat) : Int) := by
      intro axis
      fin_cases axis
      · show 0 ≤ TensorTransfer.coord d origin none slot 0 ∧
          TensorTransfer.coord d origin none slot 0 < ((d.extent 0 : Nat) : Int)
        rw [c0]
        omega
      · show 0 ≤ TensorTransfer.coord d origin none slot 1 ∧
          TensorTransfer.coord d origin none slot 1 < ((d.extent 1 : Nat) : Int)
        rw [c1]
        omega
    rw [ite_eq_left h, ite_eq_left ⟨hc, hb⟩]
    unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_two, c0, c1]
    show some (d.base + (((v0 : Int) + (slot.1.val : Int)).toNat * d.format.bytes +
      ((v1 : Nat) : Int).toNat * d.outerStride 0) + slot.2.2.val) = _
    rw [show ((v0 : Int) + (slot.1.val : Int)).toNat = v0 + slot.1.val by omega,
      Int.toNat_natCast]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨hc, -⟩
    apply h
    have h0 := hc 0
    have h1' := hc 1
    rw [c0] at h0
    rw [c1] at h1'
    change _ ∧ _ < ((d.extent 0 : Nat) : Int) at h0
    change _ ∧ _ < ((d.extent 1 : Nat) : Int) at h1'
    omega

/-- **Rank 1**: the global address of a slot of a box. -/
theorem globalAddress1 {d : Descriptor 0} {origin : Fin 1 → Int} {v0 : Nat}
    (ho0 : origin 0 = v0) (slot : TensorTransfer.Slot d) :
    TensorTransfer.globalAddress d origin none slot =
      if v0 + slot.1.val < d.extent 0 then
        some (d.base + (v0 + slot.1.val) * d.format.bytes + slot.2.2.val)
      else none := by
  have c0 := coord1 origin slot
  rw [ho0] at c0
  have hb : slot.2.2.val < (geometry d).elementBytes := slot.2.2.isLt
  unfold TensorTransfer.globalAddress TensorAddress.lookup
  by_cases h : v0 + slot.1.val < d.extent 0
  · have hc : ∀ axis : Fin 1, 0 ≤ TensorTransfer.coord d origin none slot axis ∧
        TensorTransfer.coord d origin none slot axis <
          (((geometry d).extent axis : Nat) : Int) := by
      intro axis
      fin_cases axis
      show 0 ≤ TensorTransfer.coord d origin none slot 0 ∧
        TensorTransfer.coord d origin none slot 0 < ((d.extent 0 : Nat) : Int)
      rw [c0]
      omega
    rw [ite_eq_left h, ite_eq_left ⟨hc, hb⟩]
    unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_one, c0]
    show some (d.base + ((v0 : Int) + (slot.1.val : Int)).toNat * d.format.bytes +
      slot.2.2.val) = _
    rw [show ((v0 : Int) + (slot.1.val : Int)).toNat = v0 + slot.1.val by omega]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨hc, -⟩
    apply h
    have h0 := hc 0
    rw [c0] at h0
    change _ ∧ _ < ((d.extent 0 : Nat) : Int) at h0
    omega

/-! ### The global byte a slot is read from -/

/-- **Rank 3: the source byte of slot `(x, y, k)`** of a box with unit traversal that spans one
index of dimension 2, at the origin `(v0, v1, v2)`: byte `k` of element
`(v0 + x, v1 + y, v2)` when that element exists. -/
theorem readLoc3 {d : Descriptor 2} (ht : ∀ a, d.box.traversal a = 1) (h2 : d.box.size 2 = 1)
    {origin : Fin 3 → Int} {v0 v1 v2 : Nat} (ho0 : origin 0 = v0) (ho1 : origin 1 = v1)
    (ho2 : origin 2 = v2) (sb mb : Loc) {x y k : Nat} (hx : x < d.box.size 0)
    (hy : y < d.box.size 1) (hk : k < d.format.bytes) :
    TensorCopy.readLoc (copyOf d origin sb mb) x y k =
      if v0 + x < d.extent 0 ∧ v1 + y < d.extent 1 ∧ v2 < d.extent 2 then
        some ⟨.global, 0, d.base + ((v0 + x) * d.format.bytes + (v1 + y) * d.outerStride 0 +
          v2 * d.outerStride 1) + k⟩
      else none := by
  have hx' : x < TensorTile.count d.box 0 := by rw [count0]; exact hx
  have hy' : y < TensorTile.rows d.box := by rw [rows3 ht h2]; exact hy
  show TensorTransfer.sourceLoc d origin none x y k = _
  unfold TensorTransfer.sourceLoc
  rw [slotAt_eq d hx' hy' hk]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [globalAddress3 ht h2 ho0 ho1 ho2]
  split_ifs <;> rfl

/-- **Rank 2: the source byte of slot `(x, 0, k)`** of a box with unit traversal that spans one
index of dimension 1, at the origin `(v0, v1)`. -/
theorem readLoc2 {d : Descriptor 1} (ht : ∀ a, d.box.traversal a = 1) (h1 : d.box.size 1 = 1)
    {origin : Fin 2 → Int} {v0 v1 : Nat} (ho0 : origin 0 = v0) (ho1 : origin 1 = v1)
    (sb mb : Loc) {x k : Nat} (hx : x < d.box.size 0) (hk : k < d.format.bytes) :
    TensorCopy.readLoc (copyOf d origin sb mb) x 0 k =
      if v0 + x < d.extent 0 ∧ v1 < d.extent 1 then
        some ⟨.global, 0, d.base + ((v0 + x) * d.format.bytes + v1 * d.outerStride 0) + k⟩
      else none := by
  have hx' : x < TensorTile.count d.box 0 := by rw [count0]; exact hx
  have hy' : 0 < TensorTile.rows d.box := by rw [rows2 ht h1]; exact Nat.one_pos
  show TensorTransfer.sourceLoc d origin none x 0 k = _
  unfold TensorTransfer.sourceLoc
  rw [slotAt_eq d hx' hy' hk]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [globalAddress2 ht h1 ho0 ho1]
  split_ifs <;> rfl

/-- **Rank 1: the source byte of slot `(x, 0, k)`** of a box at the origin `v0`. -/
theorem readLoc1 {d : Descriptor 0} {origin : Fin 1 → Int} {v0 : Nat} (ho0 : origin 0 = v0)
    (sb mb : Loc) {x k : Nat} (hx : x < d.box.size 0) (hk : k < d.format.bytes) :
    TensorCopy.readLoc (copyOf d origin sb mb) x 0 k =
      if v0 + x < d.extent 0 then
        some ⟨.global, 0, d.base + (v0 + x) * d.format.bytes + k⟩
      else none := by
  have hx' : x < TensorTile.count d.box 0 := by rw [count0]; exact hx
  have hy' : 0 < TensorTile.rows d.box := Nat.one_pos
  show TensorTransfer.sourceLoc d origin none x 0 k = _
  unfold TensorTransfer.sourceLoc
  rw [slotAt_eq d hx' hy' hk]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [globalAddress1 ho0]
  split_ifs <;> rfl

/-- The model's global source of a slot, as a `readLoc`. -/
theorem readLoc_of_source {s : TensorCopy.Spec} {slot : TensorTransfer.Slot s.descriptor}
    {a : Nat} (h : TensorCopy.source s slot = .global a) :
    TensorCopy.readLoc s slot.1.val slot.2.1.val slot.2.2.val = some ⟨.global, 0, a⟩ := by
  rw [TensorCopy.readLoc_source, slotAt_eq s.descriptor slot.1.isLt slot.2.1.isLt slot.2.2.isLt]
  show (match TensorCopy.source s slot with
    | .global address => some (⟨.global, 0, address⟩ : Loc)
    | .fill .. => none) = _
  rw [h]

/-! ### The shared byte a slot is written to -/

/-- **Without swizzle**, slot `(x, y, k)` is written at the destination plus `y` rows, `x`
elements and `k` bytes. -/
theorem writeLoc_plain {outer : Nat} {d : Descriptor outer} (hsw : d.swizzle = .none)
    (origin : Fin (outer + 1) → Int) (sb mb : Loc) {x y k : Nat}
    (hx : x < TensorTile.count d.box 0) (hy : y < TensorTile.rows d.box)
    (hk : k < d.format.bytes) :
    TensorCopy.writeLoc (copyOf d origin sb mb) x y k =
      some ⟨sb.space, sb.cta,
        sb.addr + (y * (d.box.size 0 * d.format.bytes) + x * d.format.bytes + k)⟩ := by
  show (TensorTransfer.slotAt d x y k).map (copyOf d origin sb mb).sharedLoc = _
  rw [slotAt_eq d hx hy hk, Option.map_some]
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, hsw, TensorTile.swizzleWidth, TensorSwizzle.offset_none, count0,
    Nat.max_eq_left (Nat.zero_le _)]

/-- **With the 32-byte swizzle**, for rows of 32 bytes and a destination that is a multiple of
128: slot `(x, y, k)` is written at the kernel's swizzle (`swzAbs`: bit 4 of the address is
flipped when bit 7 is set) of the address it would have without swizzle. -/
theorem writeLoc_b32 {outer : Nat} {d : Descriptor outer} (hsw : d.swizzle = .b32)
    (hrow : d.box.size 0 * d.format.bytes = 32) (origin : Fin (outer + 1) → Int) {sb : Loc}
    (mb : Loc) (hb : sb.addr % 128 = 0) {x y k : Nat} (hx : x < TensorTile.count d.box 0)
    (hy : y < TensorTile.rows d.box) (hk : k < d.format.bytes) :
    TensorCopy.writeLoc (copyOf d origin sb mb) x y k =
      some ⟨sb.space, sb.cta, swzAbs (sb.addr + (y * 32 + x * d.format.bytes + k))⟩ := by
  show (TensorTransfer.slotAt d x y k).map (copyOf d origin sb mb).sharedLoc = _
  rw [slotAt_eq d hx hy hk, Option.map_some, swzAbs_base _ _ hb]
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, hsw, TensorTile.swizzleWidth, count0, hrow, Nat.max_self]

/-! ### What a completed load has written -/

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **The record of an issue event is of the issue's copy.** -/
theorem spec_of_issue (hX : Consistent L K A mem0 X) {i : EvId} {pc al : Nat}
    {sp : TensorCopy.Spec} {rec : TensorCopy.Observation}
    (hiss : X.get i = some ⟨pc, .tensorIssue al sp⟩) (hrec : X.tensor i = some rec) :
    rec.spec = sp := by
  obtain ⟨⟨al', pc', hio⟩, -⟩ := hX.tensor i rec hrec
  rw [hiss] at hio
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
  exact hio.2.2.symm

/-- **A notified load has copied a launch byte that nothing writes**: at a slot whose global
source `l` has the launch value `v` and is covered by no write of the execution, the load's
record holds `v`. -/
theorem writeByte_copied (hX : Consistent L K A mem0 X) {i : EvId}
    {rec : TensorCopy.Observation} (hrec : X.tensor i = some rec)
    (hn : rec.effects.notified = true) {x y k : Nat} {l : Loc} {v : Byte}
    (hl : TensorCopy.readLoc rec.spec x y k = some l) (hm : mem0 l = some (some v))
    (hnw : ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers l) :
    TensorCopy.writeByte rec x y k = some v := by
  obtain ⟨b, hb⟩ := writeByte_of_notified hX hrec hn hl
  obtain ⟨⟨addr, hi⟩, -⟩ := hX.tensor i rec hrec
  rw [hb, tensor_writeByte_of_initial hX hrec hi hl hb hm hnw]

/-- **A notified load has filled a slot outside its tensor**: at a slot of the box that has no
global source, the load's record holds the byte of the descriptor's fill. -/
theorem writeByte_filled (hX : Consistent L K A mem0 X) {i : EvId}
    {rec : TensorCopy.Observation} (hrec : X.tensor i = some rec)
    (hn : rec.effects.notified = true) {x y k : Nat}
    (hx : x < TensorTile.count rec.spec.descriptor.box 0)
    (hy : y < TensorTile.rows rec.spec.descriptor.box)
    (hk : k < rec.spec.descriptor.format.bytes)
    (hl : TensorCopy.readLoc rec.spec x y k = none) :
    TensorCopy.writeByte rec x y k = TensorCopy.Content.byte
      (.filled rec.spec.descriptor.fill rec.spec.descriptor.format k) := by
  have hok := (hX.tensor i rec hrec).2.1
  have hs := slotAt_eq rec.spec.descriptor hx hy hk
  obtain ⟨value, hv⟩ := hok.complete hn ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨k, hk⟩⟩
  have hw := hok.writes _ value hv
  rw [TensorCopy.readLoc_source, hs, Option.bind_some] at hl
  have hsrc : TensorCopy.source rec.spec ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨k, hk⟩⟩ =
      .fill rec.spec.descriptor.fill rec.spec.descriptor.format k := by
    unfold TensorCopy.source at hl ⊢
    cases hg : rec.spec.globalAddress ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨k, hk⟩⟩ with
    | none => rfl
    | some a =>
      rw [hg] at hl
      cases hl
  rw [hsrc] at hw
  dsimp only at hw
  simp only [TensorCopy.writeByte, hs, Option.bind_some, hv, hw]

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
