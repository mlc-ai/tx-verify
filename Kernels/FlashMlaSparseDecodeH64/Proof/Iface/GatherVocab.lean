-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.CoordLoad

@[expose] public section

/-! # The cache maps, slot rows and stored coordinate words: vocabulary

The base, rows and bytes of the main and the extra cache, the map a gather of a cache has
(`gatherMap`), the physical row of a selected slot (`slotRow`), and `StoredWord`: the word an index
lane stores for position `pos` of its row is `-1` or the coordinate of the slot's row. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- The number of rows (token rows of 528 bytes) of the main or extra cache. -/
def cacheRows (P : Params) (extra : Bool) : Nat :=
  if extra then P.extraNumBlocks * (P.extraBlockStride / 528)
  else P.numBlocks * (P.blockStride / 528)

/-- Byte `k` of row `r` of the main or extra cache, as `Pre` gives it. -/
def cacheByte (P : Params) (extra : Bool) (r k : Nat) : Nat :=
  if extra then (P.extraKvByte r k).val else (P.kvByte r k).val

/-- The map of the main cache (`extra = false`) or of the extra cache, with four rows. -/
def gatherMap (P : Params) (extra : Bool) : Σ n, TensorDescriptor.Descriptor n :=
  if extra then ⟨1, (encodeKv P.extraKvBase P.extraNumBlocks P.extraBlockStride
    P.extraKvClass).fourRows⟩
  else ⟨1, (encodeKv P.kvBase P.numBlocks P.blockStride P.kvClass).fourRows⟩

/-- The physical row of slot `j` of the main (`extra = false`) or extra cache. -/
def slotRow (P : Params) (e q : Nat) (extra : Bool) (j : Nat) : Nat :=
  if extra then tokenRow P.extraPage P.extraBlockStride (P.extraIdx e q j)
  else tokenRow P.page P.blockStride (P.idx e q j)

/-- A coordinate read of the TMA warp's code (a read at a pc of the role). -/
def tmaRd (e : Event) : Bool :=
  match e.kind with
  | .rd _ _ => decide (2165 ≤ e.pc ∧ e.pc ≤ 2330)
  | _ => false

/-- **A stored coordinate word** `z` for position `pos` of the row of query `(e, q)` of the main
(`extra = false`) or extra cache: `-1`, or the physical row of the selected slot. -/
def StoredWord (P : Params) (e q : Nat) (extra : Bool) (pos : Nat) (z : BitVec 64) : Prop :=
  wordInt (.bits 32 z) = -1 ∨
    (slotValid P e q extra pos ∧ wordInt (.bits 32 z) = (slotRow P e q extra pos : Int))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
