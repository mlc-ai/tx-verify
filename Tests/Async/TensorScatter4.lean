-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.TensorStore.TensorStore
public import Lemmas.TensorStore.TensorStoreThread
public import Mathlib.Tactic

/-! `cp.async.bulk.tensor.2d.global.shared::cta.tile::scatter4` (EXT-TMA-SCATTER4): decoding, the
four-row box, per-row global destinations and the issue rule. The values reproduce cases of
`Tools/probes/tma_scatter4.ptx` (u8 tensor 256 × 64 at 4096, element `(x, y)` at
`4096 + 256 y + x`), which matched the model in every tensor byte on a B200. -/
namespace PTX.Tests.TensorScatter4
open TensorTile TensorTransfer
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 8, 32⟩, ⟨"rd".toList, 2, 64⟩], labels := [], params := [] }
private def vec (cs : List String) : Syntax.Operand := .vector (cs.map Syntax.Operand.literal)

/-! ## Decoding -/

example : Decode.op env "cp.async.bulk.tensor.2d.global.shared::cta.tile::scatter4.bulk_group"
    [.address [.register "rd0", vec ["16", "9", "2", "40", "3"]], .address [.register "r0"]] =
    .ok (.cpTensorStore (.reg 8) [.imm 16, .imm 9, .imm 2, .imm 40, .imm 3] 0 0 none
      .fourRows
           none) := rfl
example : Decode.op env
    "cp.async.bulk.tensor.2d.global.shared::cta.tile::scatter4.bulk_group.L2::cache_hint"
    [.address [.register "rd0", vec ["0", "1", "2", "3", "4"]], .address [.register "r0"],
      .register "rd1"] =
    .ok (.cpTensorStore (.reg 8) [.imm 0, .imm 1, .imm 2, .imm 3, .imm 4] 0 0
      (some (.reg 9)) .fourRows
           none) := rfl
-- Tile stores, with or without `.tile`, keep their coordinate count.
example : Decode.op env "cp.async.bulk.tensor.2d.global.shared::cta.bulk_group"
    [.address [.register "rd0", vec ["0", "1"]], .address [.register "r0"]] =
    .ok (.cpTensorStore (.reg 8) [.imm 0, .imm 1] 0 0 none .tile none) := rfl
example : (Decode.op env "cp.async.bulk.tensor.2d.global.shared::cta.tile.bulk_group"
    [.address [.register "rd0", vec ["0", "1", "2", "3", "4"]], .address [.register "r0"]]).isOk =
    false := rfl
-- scatter4 needs `.2d` and five coordinates.
example : (Decode.op env "cp.async.bulk.tensor.3d.global.shared::cta.tile::scatter4.bulk_group"
    [.address [.register "rd0", vec ["0", "1", "2", "3", "4"]], .address [.register "r0"]]).isOk =
    false := rfl
example : (Decode.op env "cp.async.bulk.tensor.2d.global.shared::cta.tile::scatter4.bulk_group"
    [.address [.register "rd0", vec ["0", "1"]], .address [.register "r0"]]).isOk = false := rfl
-- `.tile::scatter4` is a store mode, not a load mode.
example : (Decode.op env
    "cp.async.bulk.tensor.2d.shared::cluster.global.tile::scatter4.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1", "2", "3", "4"]],
      .address [.register "r1"]]).isOk = false := rfl
example : TensorMode.coordinates .fourRows 1 = 5 ∧ TensorMode.coordinates .tile 4 = 5 := ⟨rfl, rfl⟩

/-! ## Per-row destinations (probe cases) -/

private def map (w : Nat) (sw : TensorSwizzle.Mode) : TensorDescriptor.Descriptor 1 :=
  ⟨.u8, 4096, ![256, 64], ![256], ⟨![w, 1], ![1, 1]⟩, sw, .zero, .small⟩
private def store (w : Nat) (sw : TensorSwizzle.Mode) (x : Int) (ys : Fin 4 → Int) (off : Nat) :
    TensorStore.Spec := ⟨⟨1, (map w sw).fourRows, ![x, ys 0], ⟨.shared, 0, off⟩, some ys⟩, none⟩
private def slot (d : TensorDescriptor.Descriptor 1) (i j : Nat) (hi : i < count d.fourRows.box 0)
    (hj : j < rows d.fourRows.box) : Slot d.fourRows :=
  ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨0, TensorDescriptor.format_bytes_pos _⟩⟩

-- No swizzle at 256, x = 16, rows (9, 2, 40, 3): shared byte 389 goes to tensor (21, 40).
example : TensorStore.destination (store 64 .none 16 ![9, 2, 40, 3] 256)
    (slot _ 5 2 (by decide) (by decide)) = some ⟨.global, 0, 14357⟩ := by decide
example : ((store 64 .none 16 ![9, 2, 40, 3] 256).sharedLoc
    (slot _ 5 2 (by decide) (by decide))).addr = 389 := by decide
-- 128-byte swizzle at 384, x = 32, rows (1, 30, 7, 8): shared byte 548 goes to tensor (132, 30).
example : TensorStore.destination (store 128 .b128 32 ![1, 30, 7, 8] 384)
    (slot _ 100 1 (by decide) (by decide)) = some ⟨.global, 0, 11908⟩ := by decide
example : ((store 128 .b128 32 ![1, 30, 7, 8] 384).sharedLoc
    (slot _ 100 1 (by decide) (by decide))).addr = 548 := by decide
-- Rows past the extent, and columns past the right edge, are not written.
example : TensorStore.destination (store 64 .b128 0 ![3, 5, 64, 70] 0)
    (slot _ 20 2 (by decide) (by decide)) = none := by decide
example : TensorStore.destination (store 64 .b128 0 ![3, 5, 64, 70] 0)
    (slot _ 20 1 (by decide) (by decide)) = some ⟨.global, 0, 4096 + 5 * 256 + 20⟩ := by decide
example : TensorStore.destination (store 128 .b128 192 ![60, 1, 63, 0] 1024)
    (slot _ 70 0 (by decide) (by decide)) = none := by decide
example : TensorStore.destination (store 128 .b128 192 ![60, 1, 63, 0] 1024)
    (slot _ 63 3 (by decide) (by decide)) = some ⟨.global, 0, 4096 + 255⟩ := by decide
-- Validity: nonnegative origin and rows, local shared source, 128-byte alignment.
example : TensorStore.Valid 0 (store 64 .none 16 ![9, 2, 40, 3] 256) := by
  refine ⟨by decide, ?_, ?_, rfl, rfl, by decide⟩
  · intro axis; fin_cases axis <;> decide
  · rintro ys ⟨⟩ j; fin_cases j <;> decide

/-! ## The issue rule -/

private def maps (address : Nat) : Option ((outer : Nat) × TensorDescriptor.Descriptor outer) :=
  if address = 1024 then some ⟨1, map 64 .none⟩
  else if address = 2048 then some ⟨1, { map 64 .none with box := ⟨![64, 2], ![1, 1]⟩ }⟩
  else none
private def L : Launch := {
  grid := 1, block := 128, params := fun _ => none, tensorMaps := maps }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 256)
  | 8 => some (.bits 64 1024)
  | 9 => some (.bits 64 2048)
  | _ => none }
private def cs (y1 : Int) : List Opnd := [.imm 16, .imm 9, .imm y1, .imm 40, .imm 3]
private def op (m : Nat) (c : List Opnd) : Op := .cpTensorStore (.reg m) c 0 0 none .fourRows none
private def stored : Tmpl → Option (Nat × List Int × Option (List Int) × Nat × Nat)
  | .tensorStore _ s _ =>
    some (s.outer, List.ofFn s.origin, s.rows.map List.ofFn, rows s.descriptor.box,
      bytes s.descriptor)
  | _ => none

example : stored (tensorStoreTmpl L 0 t (op 8 (cs 2))) =
    some (1, [16, 9], some [9, 2, 40, 3], 4, 256) := rfl
-- A negative row coordinate traps on the B200: no issue.
example : tensorStoreTmpl L 0 t (op 8 (cs (-1))) = .ub .badValue := rfl
-- Box dimension 1 must be one; five coordinates; a tile store of a 2D map takes two.
example : tensorStoreTmpl L 0 t (op 9 (cs 2)) = .ub .badValue := rfl
example : tensorStoreTmpl L 0 t (op 8 ((cs 2).take 4)) = .ub .badValue := rfl
example : tensorStoreTmpl L 0 t (.cpTensorStore (.reg 8) (cs 2) 0 0 none .tile none) =
    .ub .badValue := rfl
-- The source must be 128-byte aligned.
example : tensorStoreTmpl L 0 t (.cpTensorStore (.reg 8) (cs 2) 0 64 none .fourRows none) =
    .ub .misaligned := rfl
-- A successful issue records row coordinates exactly in scatter4 mode.
example {a : Nat} {s : TensorStore.Spec} {u : TState}
    (h : tensorStoreTmpl L 0 t (op 8 (cs 2)) = .tensorStore a s u) : s.rows ≠ none := by
  obtain ⟨hc, -⟩ := tensorStoreTmpl_issue h
  obtain ⟨-, d, -, -, -, hr, -⟩ := tensorStoreSpec_ok hc
  intro hn
  cases hr.mp hn

end
end PTX.Tests.TensorScatter4
