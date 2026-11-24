-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Lemmas.Tensor.TensorTransfer
public import Mathlib.Tactic

/-! Tensor copies of rank 1 to 5 (`cp.async.bulk.tensor.<n>d`): decoding, issue rules,
selected-row geometry and shared placement. Rows flatten the outer axes with axis 1 varying
fastest; `Tools/probes/tma{1,3,4,5}d.ptx` with `run_tmand.cu` matched this layout (padding,
swizzle phases, out-of-bounds zero fill) byte for byte on a B200. -/
namespace PTX.Tests.TensorRank
open TensorTile
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩, ⟨"rd".toList, 2, 64⟩], labels := [], params := [] }
private def vec (cs : List String) : Syntax.Operand := .vector (cs.map Syntax.Operand.literal)

/-! ## Decoding: the rank qualifier fixes the coordinate count -/

example : Decode.op env
    "cp.async.bulk.tensor.3d.shared::cluster.global.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["16", "1", "-1"]],
      .address [.register "r1"]] =
    .ok (.cpTensor true false 0 0 (.reg 4) [.imm 16, .imm 1, .imm (-1)] 1 0 none .tile) := rfl
example : Decode.op env "cp.async.bulk.tensor.1d.shared::cta.global.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["48"]], .address [.register "r1"]] =
    .ok (.cpTensor false false 0 0 (.reg 4) [.imm 48] 1 0 none .tile) := rfl
example : Decode.op env
    "cp.async.bulk.tensor.5d.shared::cluster.global.mbarrier::complete_tx::bytes.cta_group::2"
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1", "2", "1", "1"]],
      .address [.register "r1"]] =
    .ok (.cpTensor true true 0 0 (.reg 4) [.imm 0, .imm 1, .imm 2, .imm 1,
      .imm 1] 1 0 none .tile) :=
  rfl
-- A coordinate count that disagrees with the rank, or an unknown rank, has no instruction.
example : (Decode.op env "cp.async.bulk.tensor.3d.shared::cta.global.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1"]],
      .address [.register "r1"]]).isOk = false := rfl
example : (Decode.op env "cp.async.bulk.tensor.6d.shared::cta.global.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1", "2", "3", "4", "5"]],
      .address [.register "r1"]]).isOk = false := rfl
-- Stores, with and without a cache hint.
example : Decode.op env "cp.async.bulk.tensor.4d.global.shared::cta.tile.bulk_group"
    [.address [.register "rd0", vec ["0", "0", "1", "2"]], .address [.register "r0"]] =
    .ok (.cpTensorStore (.reg 4) [.imm 0, .imm 0, .imm 1, .imm 2] 0 0 none .tile none) := rfl
example : Decode.op env "cp.async.bulk.tensor.3d.global.shared::cta.bulk_group.L2::cache_hint"
    [.address [.register "rd0", vec ["0", "0", "1"]], .address [.register "r0"], .register "rd1"] =
    .ok (.cpTensorStore (.reg 4) [.imm 0, .imm 0, .imm 1] 0 0 (some (.reg 5)) .tile none) := rfl

/-! ## Selected rows: outer axes in mixed radix, axis 1 fastest -/

private def box3 : Box 3 := ⟨![16, 3, 2], ![1, 1, 1]⟩
private def box5 : Box 5 := ⟨![16, 2, 3, 2, 2], ![1, 1, 1, 1, 1]⟩
example : rows box3 = 6 ∧ rows box5 = 24 := by decide
example : indexOf box3 5 0 = ![5, 0, 0] ∧ indexOf box3 5 2 = ![5, 2, 0] ∧
    indexOf box3 5 5 = ![5, 2, 1] := by decide
example : indexOf box5 7 23 = ![7, 1, 2, 1, 1] := by decide
-- Traversal strides of outer axes count selected elements, not box elements.
example : rows (⟨![16, 5, 4], ![1, 2, 3]⟩ : Box 3) = 3 * 2 := by decide
-- A two-dimensional box: one row per outer index, as before.
example (b : Box 2) : rows b = count b 1 := rfl
-- Every in-range row's outer indices are in range (the slot is a selected element).
example : ∀ r < rows box5, ∀ axis : Fin 4,
    unflatten 4 (fun a => count box5 a.succ) r axis < count box5 axis.succ := by decide

/-! ## Shared placement of hardware-checked elements -/

-- Rank 3, box 16×3×2, 32-byte swizzle at offset 256: element (5, 2, 1) is row 5.
example : sharedByte box3 1 .b32 256 5 5 0 = 437 := by decide
-- Rank 5, box 16×2×3×2×2, 128-byte swizzle at offset 1024: element (7, 1, 2, 1, 1) is row 23.
example : sharedByte box5 1 .b128 1024 7 23 0 = 4087 := by decide
-- Rank 4, box 16×3×2×3, 64-byte swizzle at offset 512: element (3, 2, 1, 2) is row 17.
example : sharedByte (⟨![16, 3, 2, 3], ![1, 1, 1, 1]⟩ : Box 4) 1 .b64 512 3 17 0 = 1603 := by
  decide
-- A 16-byte inner box under a swizzle has rows padded to the swizzle width.
example : rowBytes box3 1 .b32 = 32 ∧ rowBytes box3 1 .none = 16 := by decide

/-! ## Descriptors and byte counts -/

private def d3 : TensorDescriptor.Descriptor 2 :=
  ⟨.u8, 4096, ![64, 6, 5], ![64, 384], box3, .b32, .zero, .small⟩
private def d5 : TensorDescriptor.Descriptor 4 :=
  ⟨.u8, 4096, ![64, 6, 5, 4, 3], ![64, 384, 1920, 7680], box5, .b128, .zero, .small⟩
example : TensorDescriptor.Valid d3 ∧ TensorDescriptor.Valid d5 := by decide
example : TensorTransfer.bytes d3 = 96 ∧ TensorTransfer.bytes d5 = 384 := by decide
-- Six dimensions are not a valid descriptor.
example : ¬ TensorDescriptor.Valid
    (⟨.u8, 4096, fun _ => 2, fun _ => 16, ⟨fun _ => 1, fun _ => 1⟩, .none, .zero, .small⟩ :
      TensorDescriptor.Descriptor 5) := by decide
-- The box start alignment is the inner coordinate's alone, at any rank.
example : TensorDescriptor.BoxAligned d3 ![16, 1, -1] ∧ ¬ TensorDescriptor.BoxAligned d3 ![8, 0,
    0] := by
  decide

-- Slot geometry: in-bounds slots read the tensor, out-of-bounds slots on any axis fill.
/-- A slot's global source and shared byte. -/
private def place {outer : Nat} (d : TensorDescriptor.Descriptor outer) (origin : Fin (outer + 1) →
    Int)
    (rows : Option (Fin 4 → Int)) (base : Nat) (slot : TensorTransfer.Slot d) :
    Option Nat × Nat :=
  ((⟨outer, d, origin, ⟨.shared, 0, base⟩, rows⟩ : TensorBox).globalAddress slot,
    TensorTile.sharedByte d.box d.format.bytes d.swizzle base slot.1.val slot.2.1.val slot.2.2.val)
private def slot3 : TensorTransfer.Slot d3 := ⟨⟨5, by decide⟩, ⟨5, by decide⟩, ⟨0, by decide⟩⟩
example : TensorTransfer.index slot3 = ![5, 2, 1] := by decide
example : (place d3 ![32, 4, 3] none 256 slot3).2 = 437 := by decide
-- Axis 1 at 4 + 2 = 6 is past the extent 6: the byte is filled, not read.
example : (place d3 ![32, 4, 3] none 256 slot3).1 = none := by decide
-- In bounds: base + x + 64 y + 384 z for (32 + 5, 1 + 2, 3 + 1).
example : (place d3 ![32, 1, 3] none 256 slot3).1 =
    some (4096 + 37 + 3 * 64 + 4 * 384) := by decide

/-! ## Issue rules: the map's rank must match the instruction's -/

private def L : Launch := {
  grid := 2, block := 128, params := fun _ => none, clusterSize := ⟨2, by decide⟩,
  tensorMaps := fun address => if address = 1024 then some ⟨2, d3⟩ else none }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 256)
  | 1 => some (.bits 32 64)
  | 4 => some (.bits 64 1024)
  | _ => none }
/-- The issued rank and origin of a tensor-load template. -/
private def issued : Tmpl → Option (Nat × List Int)
  | .tensorIssue _ s _ => some (s.outer, List.ofFn s.origin)
  | _ => none

example : issued (tensorTmpl L 0 t
    (.cpTensor false false 0 0 (.reg 4) [.imm 32, .imm 4, .imm (-1)] 1 0 none .tile)) =
    some (2, [32, 4, -1]) := rfl
-- Two coordinates for a three-dimensional map: no issue.
example : tensorTmpl L 0 t (.cpTensor false false 0 0 (.reg 4) [.imm 32, .imm 4] 1 0 none .tile) =
    .ub .badValue := rfl
-- Stores take the same rank check, and negative store coordinates on any axis are rejected.
example : tensorStoreTmpl L 0 t (.cpTensorStore (.reg 4) [.imm 0, .imm 0] 0 0 none .tile none) =
    .ub .badValue := rfl
example : tensorStoreTmpl L 0 t (.cpTensorStore (.reg 4) [.imm 0, .imm 0,
    .imm (-1)] 0 0 none .tile none) =
    .ub .badValue := rfl
private def storedRank : Tmpl → Option (Nat × List Int)
  | .tensorStore _ s _ => some (s.outer, List.ofFn s.origin)
  | _ => none
example : storedRank (tensorStoreTmpl L 0 t
    (.cpTensorStore (.reg 4) [.imm 16, .imm 0, .imm 2] 0 0 none .tile none)) = some (2, [16, 0,
      2]) :=
  rfl

end
end PTX.Tests.TensorRank
