-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorStore

@[expose] public section

namespace PTX.TensorStore
noncomputable section

/-! ## DEP-TENSOR-STORE-BYTES — output tensor byte footprints and observed values
Statement: Every selected byte of a tensor store reserves its shared source location, including
  out-of-bounds bytes, which may be read or skipped. Only in-bounds bytes have a global write
  location, and a reduction also reads the old destination byte at that location.

Defs: TensorStore.readLoc, TensorStore.writeLoc, TensorStore.readByte, TensorStore.writeByte,
  TensorStore.oldByte

Source:
- §9.7.10.28.5.3 (shared-to-global tensor)
- DEP-TENSOR-STORE-EFFECTS
- EXT-TMA-STORE-OOB

Direction: reading

Applies: Selected byte slots of tiled output copies

Premises: The instruction fixes the descriptor, origin and local shared source; effect records
  retain actual read and write bytes.

Effect: Common read-source, allocation and conflicting-access queries.
-/
/-- The shared location that byte `(x, y, k)` of the store reads. -/
def readLoc (s : Spec) (x y k : Nat) : Option Loc :=
  (TensorTransfer.slotAt s.descriptor x y k).map s.sharedLoc
/-- The global location that byte `(x, y, k)` of the store writes, if it is in bounds. -/
def writeLoc (s : Spec) (x y k : Nat) : Option Loc :=
  (TensorTransfer.slotAt s.descriptor x y k).bind (destination s)
/-- The byte that the recorded effects read for byte `(x, y, k)`, if any. -/
def readByte (o : Observation) (x y k : Nat) : Option Byte :=
  (TensorTransfer.slotAt o.spec.descriptor x y k).bind o.effects.read
/-- The byte that the recorded effects write for byte `(x, y, k)`, if any. -/
def writeByte (o : Observation) (x y k : Nat) : Option Byte :=
  (TensorTransfer.slotAt o.spec.descriptor x y k).bind o.effects.write
/-- The old destination byte that a reduction read for byte `(x, y, k)`, if any. -/
def oldByte (o : Observation) (x y k : Nat) : Option Byte :=
  (TensorTransfer.slotAt o.spec.descriptor x y k).bind o.effects.old

end
end PTX.TensorStore
