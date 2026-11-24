-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fin.VecNotation
public import Core.Async.Tensor.TensorSafety
public import Core.Thread.Run

/-! Bounding-box start alignment of tensor copies (§5.5.3.1, EXT-TMA-BOX-ALIGN): the global
start of a box must be 16-byte aligned, and a B200 traps otherwise (`Tools/probes/tma2d.ptx`,
`Tools/probes/tma2d_store.ptx`). -/
namespace PTX.Tests.TensorBoxAlign
open TensorDescriptor
noncomputable section

private def u8 : Descriptor 1 := ⟨.u8, 4096, ![256, 64], ![256], ⟨![64, 8], ![1, 1]⟩, .none, .zero,
    .small⟩
private def f16 : Descriptor 1 := { u8 with format := .f16, outerStride := ![512] }

-- The innermost coordinate's byte offset decides; outer coordinates never misalign (strides
-- are multiples of 16).
example : BoxAligned u8 ![0, 3] ∧ BoxAligned u8 ![16, 5] ∧ BoxAligned u8 ![48, 63] := by decide
example : BoxAligned u8 ![-16, -3] := by decide
example : ¬ BoxAligned u8 ![8, 0] ∧ ¬ BoxAligned u8 ![4, 0] ∧ ¬ BoxAligned u8 ![-8, 0] := by decide
-- Element width scales the offset: 8 two-byte elements are 16 bytes.
example : BoxAligned f16 ![8, 1] ∧ ¬ BoxAligned f16 ![4, 1] := by decide
example : BoxAligned { u8 with format := .f32 } ![4, 1] ∧ BoxAligned { u8 with format := .f64 } ![2,
    1] :=
  by decide

/-! ## Shared layout cases checked byte for byte on a B200 (`run_tma2d tma2d.ptx`)

Model positions (relative to the shared buffer) of a few elements of the probe's cases. -/

open TensorTile in
-- 128B swizzle at offset 384 (phase 3): element (i, j) of a 128x16 u8 box.
example : sharedByte ⟨![128, 16], ![1, 1]⟩ 1 .b128 384 0 0 0 = 384 + 48 ∧
    sharedByte ⟨![128, 16], ![1, 1]⟩ 1 .b128 384 17 2 0 = 384 + 256 + 65 := by decide
open TensorTile in
-- A 32-byte inner box under 128B swizzle: rows are padded to 128 bytes.
example : rowBytes ⟨![32, 8], ![1, 1]⟩ 1 .b128 = 128 ∧
    sharedByte ⟨![32, 8], ![1, 1]⟩ 1 .b128 0 5 3 0 = 3 * 128 + 48 + 5 := by decide
open TensorTile in
-- 64B swizzle at offset 640 (phase 5 mod 4 = 1).
example : sharedByte ⟨![64, 16], ![1, 1]⟩ 1 .b64 640 0 0 0 = 640 + 16 := by decide

/-! ## Loads, stores, reductions and prefetches with a misaligned box are undefined

One check, `requireBoxAligned`, decides at issue; a misaligned box produces an undefined-behaviour
event for each instruction, so no issue event records one. -/

private def tmap : Descriptor 1 :=
  ⟨.f16, 4096, ![8192, 8192], ![16384], ⟨![64, 128], ![1, 1]⟩, .b128, .zero, .small⟩
private def L : Launch := {
  grid := 2, block := 128, params := fun _ => none, clusterSize := ⟨2, by decide⟩,
  tensorMaps := fun address => if address = 1024 then some ⟨1, tmap⟩ else none }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 128)
  | 1 => some (.ptr 32 false (.shared 1 0) 64)
  | 2 => some (.bits 64 1024)
  | _ => none }
private def fault : Tmpl → Option Fault
  | .ub f => some f
  | _ => none

example : requireBoxAligned tmap ![8, 3] = .ok () := rfl
example : requireBoxAligned tmap ![4, 3] = .error .misaligned := rfl
example : requireBoxAligned tmap ![-8, 3] = .ok () := rfl

-- f16 elements: the box start is aligned exactly when the innermost coordinate is a multiple of 8.
private def load (x : Int) : Op :=
  .cpTensor true true 0 0 (.reg 2) [(.imm x), (.imm 32)] 1 0 none .tile
example : fault (tensorTmpl L 128 t (load 4)) = some .misaligned := rfl
example : fault (tensorTmpl L 128 t (load 12)) = some .misaligned := rfl
example : fault (tensorTmpl L 128 t (load 8)) = none := rfl
example : fault (tensorTmpl L 128 t (load (-8))) = none := rfl
-- A multicast load is checked before its copies are fanned out.
example : fault (tensorTmpl L 128 t
    (.cpTensor true false 0 0 (.reg 2) [(.imm 4), (.imm 32)] 1 0 (some (2, .imm 3)) .tile)) =
    some .misaligned := rfl
example : tensorLoadCopy L 128 t true true 0 0 (.reg 2) [(.imm 4), (.imm 32)] 1 0 .tile =
    .error .misaligned := rfl

private def store (x : Int) (reduce : Option AtomOp := none) : Op :=
  .cpTensorStore (.reg 2) [(.imm x), (.imm 0)] 0 0 none .tile reduce
example : fault (tensorStoreTmpl L 0 t (store 4)) = some .misaligned := rfl
example : fault (tensorStoreTmpl L 0 t (store 8)) = none := rfl
-- A reduction has the same box check.
example : fault (tensorStoreTmpl L 0 t (store 4 (some .add))) = some .misaligned := rfl
example : fault (tensorStoreTmpl L 0 t (store 8 (some .add))) = none := rfl

private def prefetch (x : Int) : Op := .prefetchTensor (.reg 2) [(.imm x), (.imm 0)] .tile none
example : fault (tensorPrefetchTmpl L 0 t (prefetch 4)) = some .misaligned := rfl
example : fault (tensorPrefetchTmpl L 0 t (prefetch 8)) = none := rfl

-- An issue event that the thread rule produced has an aligned box.
example {a : Nat} {s : TensorCopy.Spec}
    (h : tensorLoadCopy L 128 t true true 0 0 (.reg 2) [(.imm 8), (.imm 32)] 1 0 .tile =
      .ok (a, s)) : BoxAligned s.descriptor s.origin :=
  tensorLoadCopy_boxAligned _ _ _ _ _ _ _ _ _ _ _ _ h
example {a : Nat} {s : TensorStore.Spec}
    (h : tensorStoreSpec L 0 t (.reg 2) [(.imm 8), (.imm 0)] 0 0 none .tile none = .ok (a, s)) :
    BoxAligned s.descriptor s.origin :=
  tensorStoreSpec_boxAligned _ _ _ _ _ _ _ _ _ _ h

end
end PTX.Tests.TensorBoxAlign
