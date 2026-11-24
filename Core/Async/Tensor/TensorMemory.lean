-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorCopy

@[expose] public section

namespace PTX.TensorCopy
noncomputable section

/-! ## DEP-TENSOR-LOAD-BYTES — scalar byte adapters for tensor effects
Statement: Each byte of a tensor load reads a one-byte global location and writes the shared
  location of its swizzled address. A copied byte keeps its value, and a zero fill is the zero of
  the descriptor's element type. A NaN fill, and a zero fill of `f64`, have no scalar value and are
  unsupported.

Defs: TensorCopy.zeroValue, TensorCopy.Content.byte, TensorCopy.readLoc, TensorCopy.writeLoc,
  TensorCopy.readByte, TensorCopy.writeByte

Source:
- §5.5.3.3 (zero fill)
- §9.7.10.28.5.3 (tensor copy)
- MEM-BYTE

Direction: scope

Applies: Selected byte slots of the represented tensor copy; zero fill uses represented integer,
  f16, bf16 and f32 scalar values

Premises: The slot belongs to the copy. CopyOk constrains each write to its recorded read or typed
  fill source.

Effect: Adapters for execution memory queries. OOB-NaN and f64 zero fill have no scalar byte
  (`Content.byte` is none): the Value type does not represent those floating values, so such
  content is unsupported (ERR-TENSOR-FILL-VALUE rejects its writes). A missing effect is distinct
  from a zero-valued byte.
-/
/-- The zero of an element format as a scalar value; `f64` has none. -/
def zeroValue : TensorDescriptor.Format → Option Value
  | .f16 => some (.float .f16 0)
  | .bf16 => some (.float .bf16 0)
  | .f32 => some (.float .f32 0)
  | .f64 => none
  | f => some (.bits (f.bytes * 8) 0)

/-- The scalar byte of a written content: the copied byte, or the byte of the zero fill; the NaN
fill has none. -/
def Content.byte : Content → Option Byte
  | .copied b => some b
  | .filled .zero format k => (zeroValue format).map (fun v => v.byteAt k)
  | .filled .oobNan _ _ => none

/-- The global location that byte `(x, y, k)` of the load reads, if it is in bounds. -/
def readLoc (s : Spec) (x y k : Nat) : Option Loc :=
  TensorTransfer.sourceLoc s.descriptor s.origin s.rows x y k

/-- The shared location that byte `(x, y, k)` of the load writes. -/
def writeLoc (s : Spec) (x y k : Nat) : Option Loc :=
  (TensorTransfer.slotAt s.descriptor x y k).map s.sharedLoc

/-- The byte that the recorded effects read for byte `(x, y, k)`, if any. -/
def readByte (o : Observation) (x y k : Nat) : Option Byte :=
  (TensorTransfer.slotAt o.spec.descriptor x y k).bind o.effects.read

/-- The scalar byte that the recorded effects write for byte `(x, y, k)`, if any. -/
def writeByte (o : Observation) (x y k : Nat) : Option Byte :=
  (TensorTransfer.slotAt o.spec.descriptor x y k).bind fun slot =>
    (o.effects.write slot).bind Content.byte

end
end PTX.TensorCopy
