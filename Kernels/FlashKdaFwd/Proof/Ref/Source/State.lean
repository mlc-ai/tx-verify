-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Source.Maps
public import Kernels.FlashKdaFwd.Proof.Ref.Source.Inputs
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Defs

@[expose] public section

/-! # The sixteen loads of the initial state: source, frame, content

The load leader of a block (thread 128) issues sixteen tensor loads of the FP32 initial state
before the tile loop; the `j`-th is the copy `stateSpec P L g j` (`Ref/Startup/Shapes.lean`):
through the map of parameter object 8, the box of the 8 key features `8 j .. 8 j + 7` of all 128
value channels of the block's plane `H * seq + head`, to the `j`-th 4096 bytes of the FP32 state
buffer (window bytes 32768 to 98303), with the 32-byte swizzle.

* `stateSpec_read`, `stateSpec_read_loc`: **the source address** of slot `(x, y, k)`: byte `k`
  of the entry (value channel `y`, key feature `8 j + x`) of the block's sequence and head in
  the initial-state array (`Params.initialLoc`). Every slot is inside the array.
* `stateSpec_source`: **`StateSource P L`** (`Ref/Startup/Direct.lean`), the hypothesis the
  startup phase left open: no load selects an element outside the array, and every byte a load
  reads is a byte of the array (`Main.lean: stateSource` is this theorem).
* `stateSpec_input`: every byte a load reads is a launch input byte (allocated, no output, no
  final-state byte: the load part of `DirectFacts.globalReadFrame`).
* `stateSpec_ok`: the copy is routed to the issuer's block, its descriptor is valid and its box
  is not empty (the first three parts of the progress premise `TensorSources`).
* `stateSpec_write`: **the destination** of slot `(x, y, k)`: the kernel's swizzle of window
  byte `32768 + 4096 j + 32 y + 4 x + k`.
* `state_load_content`: **the content**. For every offset `o` of the buffer: the slot
  (`stateX`, `stateY`, `stateK`) of load `stateQ L o` is written at window byte `32768 + o`, and
  the record of that load, once notified, holds there the byte `initBuf P L c o` of the value
  layer (`Proof/Values/Ends/Defs.lean`: the byte of the FP32 payload of the entry whose
  swizzled address this is), which is defined.

Words: the *window* of a block is its shared memory from the address of `shared_mem`
(`Launch.sharedBase`); `unswz L o` is the offset in the buffer, before swizzling, of the byte
that the swizzle puts at offset `o`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
open PTX TensorDescriptor
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (stateSpec StateSource)
open PTX.Kernels.FlashKdaFwd.Proof.Values.Ends (initBuf initState bufByte stateByte entry elemOf
  entry_elemOf swzAddr swzAddr_sub swzAddr_swzAddr)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g j x y k : Nat}

/-! ### Source -/

/-- A load of the initial state as a copy through `stateMap`. -/
theorem stateSpec_eq (P : Params) (L : Launch) (g j : Nat) :
    stateSpec P L g j = copyOf (stateMap P.initialBase (P.sequences * P.heads) (P.allocation 8))
      (originOf [8 * j, 0, P.heads * seqOf P g + headOf P g])
      ⟨.shared, g / L.block, P.sharedBase + (32768 + 4096 * j)⟩
      ⟨.shared, g / L.block, P.sharedBase + 98384⟩ := rfl

/-- The slots of a load of the initial state: 8 columns, 128 rows, 4 bytes. -/
theorem stateSpec_box {l : Loc}
    (h : TensorCopy.readLoc (stateSpec P L g j) x y k = some l ∨
      TensorCopy.writeLoc (stateSpec P L g j) x y k = some l) : x < 8 ∧ y < 128 ∧ k < 4 := by
  obtain ⟨h0, h1, h2⟩ := box_state P.initialBase (P.sequences * P.heads) (P.allocation 8)
  have hb : x < TensorTile.count (stateSpec P L g j).descriptor.box 0 ∧
      y < TensorTile.rows (stateSpec P L g j).descriptor.box ∧
      k < (stateSpec P L g j).descriptor.format.bytes := by
    rcases h with h | h
    · exact TensorCopy.readLoc_bounds h
    · exact TensorCopy.writeLoc_bounds h
  exact ⟨Nat.lt_of_lt_of_eq hb.1 h0, Nat.lt_of_lt_of_eq hb.2.1 h1, Nat.lt_of_lt_of_eq hb.2.2 h2⟩

/-- **The source address of a slot of a load of the initial state**: byte `k` of the entry
(value channel `y`, key feature `8 j + x`) of the plane of the block's sequence and head. -/
theorem stateSpec_read (hpre : Pre P L mem0) (hg : g < L.threads) (hj : j < 16) (hx : x < 8)
    (hy : y < 128) (hk : k < 4) :
    TensorCopy.readLoc (stateSpec P L g j) x y k = some ⟨.global, 0, P.initialBase +
      65536 * (seqOf P g * P.heads + headOf P g) + 512 * y + 4 * (8 * j + x) + k⟩ := by
  have hpl := plane_lt hpre hg
  have hc : seqOf P g * P.heads = P.heads * seqOf P g := Nat.mul_comm _ _
  rw [stateSpec_eq, read_state _ _ _ _ _ _ _ _ hx hy hk, ite_eq_left ⟨by omega, by omega, hpl⟩]
  congr 2
  omega

/-- The source address in the specification's location function `Params.initialLoc`: slot
`(x, y, k)` of load `j` reads byte `k` of the entry (value channel `y`, key feature
`8 j + x`) of the initial state of the block's sequence and head. -/
theorem stateSpec_read_loc (hpre : Pre P L mem0) (hg : g < L.threads) (hj : j < 16)
    (hx : x < 8) (hy : y < 128) (hk : k < 4) :
    TensorCopy.readLoc (stateSpec P L g j) x y k =
      some ((P.initialLoc (seqOf P g) (headOf P g) ⟨y, hy⟩ ⟨8 * j + x, by omega⟩).at k) :=
  stateSpec_read hpre hg hj hx hy hk

/-- **`StateSource P L`**: a load of the initial state selects no element outside the array, and
every byte it reads is a byte of the array. -/
theorem stateSpec_source (hpre : Pre P L mem0) : StateSource P L := by
  intro g hg j hj
  have hpl := plane_lt hpre hg
  refine ⟨?_, fun x y k l h => ?_⟩
  · exact noOob3 (d := stateMap P.initialBase (P.sequences * P.heads) (P.allocation 8))
      (fun _ => rfl) rfl (v0 := 8 * j) (v1 := 0) (v2 := P.heads * seqOf P g + headOf P g)
      rfl rfl rfl (show 8 * j + 8 ≤ 128 by omega) (show 0 + 128 ≤ 128 by omega) hpl
  · obtain ⟨hx, hy, hk⟩ := stateSpec_box (.inl h)
    rw [stateSpec_read hpre hg hj hx hy hk] at h
    obtain rfl := Option.some.inj h
    have hc : seqOf P g * P.heads = P.heads * seqOf P g := Nat.mul_comm _ _
    refine ⟨65536 * (seqOf P g * P.heads + headOf P g) + 512 * y + 4 * (8 * j + x) + k, ?_, ?_⟩
    · unfold Params.stateBytes
      omega
    · simp only [Loc.mk.injEq, true_and]
      omega

/-- **Every byte a load of the initial state reads is a launch input byte.** -/
theorem stateSpec_input (hpre : Pre P L mem0) (hg : g < L.threads) (hj : j < 16) {l : Loc}
    (h : TensorCopy.readLoc (stateSpec P L g j) x y k = some l) : InputByte P mem0 l := by
  obtain ⟨k', hk', rfl⟩ := (stateSpec_source hpre g hg j hj).2 x y k l h
  exact initial_input hpre hk'

/-- **The first three parts of the progress premise `TensorSources` for a load of the initial
state**: routed to the issuer's block, a valid descriptor, a box that is not empty. -/
theorem stateSpec_ok (hpre : Pre P L mem0) (hg : g < L.threads) (j : Nat) :
    TensorCopy.RoutingOk L (g / L.block) (stateSpec P L g j) ∧
      TensorDescriptor.Valid (stateSpec P L g j).descriptor ∧
      0 < TensorTransfer.bytes (stateSpec P L g j).descriptor := by
  refine ⟨ownRoute hpre hg _ _, preMap_valid hpre 8, ?_⟩
  rw [stateSpec, loadSpec_bytes]
  decide

/-! ### Destination -/

/-- **The destination of a slot of a load of the initial state**: the kernel's swizzle of the
window byte `32768 + 4096 j + 32 y + 4 x + k` of the issuer's block. -/
theorem stateSpec_write (hpre : Pre P L mem0) (hx : x < 8) (hy : y < 128) (hk : k < 4) :
    TensorCopy.writeLoc (stateSpec P L g j) x y k = some ⟨.shared, g / L.block,
      swzAbs (P.sharedBase + (32768 + 4096 * j) + (y * 32 + x * 4 + k))⟩ := by
  have ha := hpre.sharedAlignment
  rw [stateSpec_eq, write_state _ _ _ _ (show (⟨.shared, g / L.block,
    P.sharedBase + (32768 + 4096 * j)⟩ : Loc).addr % 128 = 0 by simp only; omega) hx hy hk]

/-! ### Content -/

/-- **The offset before swizzling** of the byte that the swizzle puts at offset `o` of the FP32
state buffer. -/
def unswz (L : Launch) (o : Nat) : Nat :=
  swzAbs (L.sharedBase + 32768 + o) - (L.sharedBase + 32768)

/-- The load that writes offset `o` of the buffer. -/
def stateQ (L : Launch) (o : Nat) : Nat := unswz L o / 4096
/-- The column of the slot that is written at offset `o` of the buffer. -/
def stateX (L : Launch) (o : Nat) : Nat := unswz L o % 32 / 4
/-- The row of the slot that is written at offset `o` of the buffer. -/
def stateY (L : Launch) (o : Nat) : Nat := unswz L o % 4096 / 32
/-- The byte of the slot that is written at offset `o` of the buffer. -/
def stateK (L : Launch) (o : Nat) : Nat := unswz L o % 4

/-- The kernel's swizzle is the value layer's. -/
theorem swzAbs_eq (a : Nat) : swzAbs a = swzAddr a := rfl

/-- The unswizzled offset stays in the buffer, and swizzling it gives the offset back. -/
theorem unswz_spec (hpre : Pre P L mem0) {o : Nat} (ho : o < 65536) :
    unswz L o < 65536 ∧ swzAbs (L.sharedBase + 32768 + unswz L o) = L.sharedBase + 32768 + o := by
  have hb : L.sharedBase % 32 = 0 := by
    have := hpre.sharedAlignment
    rw [hpre.sharedBase]
    omega
  obtain ⟨h1, h2⟩ := swzAddr_sub (o := o) hb
  rw [← swzAbs_eq] at h1 h2
  refine ⟨by unfold unswz; omega, ?_⟩
  rw [show L.sharedBase + 32768 + unswz L o = swzAbs (L.sharedBase + 32768 + o) by
    unfold unswz; omega, swzAbs_swzAbs]

/-- **What the sixteen loads leave at offset `o` of the FP32 state buffer** of the block of
thread `g`: load `stateQ L o` has the slot `(stateX, stateY, stateK)` at window byte
`32768 + o`, and its record, once notified, holds there the byte `initBuf P L c o`, which is
defined. -/
theorem state_load_content (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hW : WriteFrame P X)
    (hg : g < L.threads) {o : Nat} (ho : o < 65536) :
    stateQ L o < 16 ∧
      TensorCopy.writeLoc (stateSpec P L g (stateQ L o)) (stateX L o) (stateY L o) (stateK L o) =
        some ⟨.shared, g / L.block, L.sharedBase + (32768 + o)⟩ ∧
      ∀ (i : EvId) (rec : TensorCopy.Observation), X.tensor i = some rec →
        rec.spec = stateSpec P L g (stateQ L o) → rec.effects.notified = true →
        TensorCopy.writeByte rec (stateX L o) (stateY L o) (stateK L o) =
            initBuf P L (g / L.block) o ∧ (initBuf P L (g / L.block) o).isSome := by
  obtain ⟨hu, hsw⟩ := unswz_spec hpre ho
  have hq : stateQ L o < 16 := by unfold stateQ; omega
  have hx : stateX L o < 8 := by unfold stateX; omega
  have hy : stateY L o < 128 := by unfold stateY; omega
  have hk : stateK L o < 4 := by unfold stateK; omega
  have hsum : 4096 * stateQ L o + (stateY L o * 32 + stateX L o * 4 + stateK L o) =
      unswz L o := by
    unfold stateQ stateX stateY stateK
    omega
  -- the value: the byte of the payload of the entry
  have hval : initBuf P L (g / L.block) o = some ((Value.float .f32 (P.initial (seqOf P g)
      (headOf P g) ⟨stateY L o, hy⟩ ⟨8 * stateQ L o + stateX L o, by omega⟩)).byteAt
      (stateK L o)) := by
    have he : unswz L o / 4 =
        elemOf (⟨stateY L o, hy⟩ : Fin 128) (⟨8 * stateQ L o + stateX L o, by omega⟩ : Fin 128)
        := by
      unfold elemOf stateQ stateX stateY
      simp only
      omega
    have hS : initState P (g / L.block) = P.initial (seqOf P g) (headOf P g) := by
      unfold initState seqOf headOf
      rw [hpre.block]
    show stateByte (initState P (g / L.block)) (unswz L o) = _
    unfold stateByte
    rw [ite_eq_left hu, he, entry_elemOf, hS]
    rfl
  refine ⟨hq, ?_, fun i rec hrec hspec hn => ⟨?_, by rw [hval]; rfl⟩⟩
  · have hb := hpre.sharedBase
    have e1 : P.sharedBase + (32768 + 4096 * stateQ L o) +
        (stateY L o * 32 + stateX L o * 4 + stateK L o) = L.sharedBase + 32768 + unswz L o := by
      omega
    rw [stateSpec_write hpre hx hy hk, e1, hsw, Nat.add_assoc]
  · rw [hval]
    have hl := stateSpec_read hpre hg hq hx hy hk
    rw [← hspec] at hl
    have hin : InputByte P mem0 _ := stateSpec_input hpre hg hq (hspec ▸ hl)
    exact writeByte_copied hX hrec hn hl
      (initial_byte hpre (seqOf_lt hpre g) (headOf_lt hpre hg) ⟨stateY L o, hy⟩
        ⟨8 * stateQ L o + stateX L o, by omega⟩ hk) (hin.unwritten hW)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
