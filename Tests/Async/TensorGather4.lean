-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.Tensor.TensorTransfer
public import Lemmas.Tensor.TensorMulticast
public import Core.Async.Tensor.TensorAllocation
public import Mathlib.Tactic

/-! `cp.async.bulk.tensor.2d.tile::gather4` (EXT-TMA-GATHER4): decoding, the four-row transfer
box, per-row source coordinates, shared placement and the issue rule. The slot values reproduce
cases of `Tools/probes/tma_gather4.ptx` (u8 tensor 256 × 64 at 4096, element `(x, y)` at
`4096 + 256 y + x`), which matched the model byte for byte on a B200. -/
namespace PTX.Tests.TensorGather4
open TensorTile TensorTransfer
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 8, 32⟩, ⟨"rd".toList, 2, 64⟩, ⟨"rs".toList, 2, 16⟩], labels := [],
      params := [] }
private def vec (cs : List String) : Syntax.Operand := .vector (cs.map Syntax.Operand.literal)
private def g4 : String :=
  "cp.async.bulk.tensor.2d.shared::cluster.global.tile::gather4.mbarrier::complete_tx::bytes"

/-! ## Decoding: `{x, y0, y1, y2, y3}` on a 2D load -/

example : Decode.op env g4
    [.address [.register "r0"], .address [.register "rd0", vec ["16", "9", "2", "40", "2"]],
      .address [.register "r1"]] =
    .ok (.cpTensor true false 0 0 (.reg 8) [.imm 16, .imm 9, .imm 2, .imm 40, .imm 2] 1 0
      none .fourRows) := rfl
-- With `.cta_group::2` and with `.multicast::cluster`.
example : Decode.op env (g4 ++ ".cta_group::2")
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1", "2", "3", "4"]],
      .address [.register "r1"]] =
    .ok (.cpTensor true true 0 0 (.reg 8) [.imm 0, .imm 1, .imm 2, .imm 3, .imm 4] 1 0
      none .fourRows) := rfl
example : Decode.op env (g4 ++ ".multicast::cluster")
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1", "2", "3", "4"]],
      .address [.register "r1"], .register "rs1"] =
    .ok (.cpTensor true false 0 0 (.reg 8) [.imm 0, .imm 1, .imm 2, .imm 3, .imm 4] 1 0
      (some (16, .reg 11)) .fourRows) := rfl
-- An explicit `.tile` is the default mode.
example : Decode.op env
    "cp.async.bulk.tensor.2d.shared::cluster.global.tile.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["16", "9"]],
      .address [.register "r1"]] =
    .ok (.cpTensor true false 0 0 (.reg 8) [.imm 16, .imm 9] 1 0 none .tile) := rfl
-- gather4 needs `.2d` and five coordinates; a 2D tile load needs two.
example : (Decode.op env
    "cp.async.bulk.tensor.3d.shared::cluster.global.tile::gather4.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1", "2", "3", "4"]],
      .address [.register "r1"]]).isOk = false := rfl
example : (Decode.op env g4
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1"]],
      .address [.register "r1"]]).isOk = false := rfl
example : (Decode.op env
    "cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1", "2", "3", "4"]],
      .address [.register "r1"]]).isOk = false := rfl
-- Other load modes are not represented.
example : (Decode.op env
    "cp.async.bulk.tensor.3d.shared::cluster.global.im2col.mbarrier::complete_tx::bytes"
    [.address [.register "r0"], .address [.register "rd0", vec ["0", "1", "2"]],
      .address [.register "r1"]]).isOk = false := rfl

/-! ## The four-row transfer box -/

/-- The probe's maps: u8, 256 × 64 at 4096, box `w × 1`, the given swizzle. -/
private def map (w : Nat) (sw : TensorSwizzle.Mode) : TensorDescriptor.Descriptor 1 :=
  ⟨.u8, 4096, ![256, 64], ![256], ⟨![w, 1], ![1, 1]⟩, sw, .zero, .small⟩
example : TensorDescriptor.Valid (map 64 .none) ∧ TensorDescriptor.Valid (map 128 .b128) ∧
    TensorDescriptor.Valid (map 64 .b64) ∧ TensorDescriptor.Valid (map 32 .b128) := by decide
-- Four rows of the map's width, with unit traversal; the mbarrier receives 4 × the row bytes.
example : rows (map 64 .none).fourRows.box = 4 ∧ count (map 64 .none).fourRows.box 0 = 64 := by
  decide
example : bytes (map 64 .none).fourRows = 256 ∧ bytes (map 128 .b128).fourRows = 512 ∧
    bytes (map 32 .b128).fourRows = 128 := by decide
-- The map's box itself has one row.
example : rows (map 64 .none).box = 1 := by decide
-- Four rows keep the descriptor valid, and the shared layout of a four-row tile.
example : TensorDescriptor.Valid (map 64 .b64).fourRows := by decide
example : rowBytes (map 32 .b128).fourRows.box 1 .b128 = 128 := by decide

/-! ## Per-row sources and shared placement (probe cases) -/

/-- A slot's global source and shared byte. -/
private def place {outer : Nat} (d : TensorDescriptor.Descriptor outer) (origin : Fin (outer + 1) →
    Int)
    (rows : Option (Fin 4 → Int)) (base : Nat) (slot : Slot d) :
    Option Nat × Nat :=
  ((⟨outer, d, origin, ⟨.shared, 0, base⟩, rows⟩ : TensorBox).globalAddress slot,
    TensorTile.sharedByte d.box d.format.bytes d.swizzle base slot.1.val slot.2.1.val slot.2.2.val)
private def slot (d : TensorDescriptor.Descriptor 1) (i j : Nat) (hi : i < count d.fourRows.box 0)
    (hj : j < rows d.fourRows.box) : Slot d.fourRows :=
  ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨0, TensorDescriptor.format_bytes_pos _⟩⟩

-- No swizzle at 256, x = 16, rows (9, 2, 40, 2): element 5 of row 2 is tensor (21, 40).
example : place (map 64 .none).fourRows ![16, 9] (some ![9, 2, 40, 2]) 256
    (slot _ 5 2 (by decide) (by decide)) = ⟨some 14357, 389⟩ := by decide
-- Rows 1 and 3 repeat tensor row 2.
example : (place (map 64 .none).fourRows ![16, 9] (some ![9, 2, 40, 2]) 256
    (slot _ 7 1 (by decide) (by decide))).1 =
    (place (map 64 .none).fourRows ![16, 9] (some ![9, 2, 40, 2]) 256
    (slot _ 7 3 (by decide) (by decide))).1 := by decide
-- 128-byte swizzle at 384, x = 32, rows (1, 30, 7, 7): element 100 of row 1.
example : place (map 128 .b128).fourRows ![32, 1] (some ![1, 30, 7, 7]) 384
    (slot _ 100 1 (by decide) (by decide)) = ⟨some 11908, 548⟩ := by decide
-- 64-byte swizzle at 640, x = 0, rows (11, 12, 50, 4): two 64-byte rows per 128-byte pattern row.
example : place (map 64 .b64).fourRows ![0, 11] (some ![11, 12, 50, 4]) 640
    (slot _ 40 3 (by decide) (by decide)) = ⟨some 5160, 840⟩ := by decide
-- A 32-byte row under the 128-byte swizzle is padded to 128 bytes.
example : place (map 32 .b128).fourRows ![0, 1] (some ![1, 2, 3, 4]) 0
    (slot _ 31 3 (by decide) (by decide)) = ⟨some 5151, 431⟩ := by decide
-- Out of bounds per row: x = -16, rows (-3, 5, 64, 70).
example : place (map 64 .b128).fourRows ![-16, -3] (some ![-3, 5, 64, 70]) 0
    (slot _ 20 1 (by decide) (by decide)) = ⟨some 5380, 132⟩ := by decide
example : place (map 64 .b128).fourRows ![-16, -3] (some ![-3, 5, 64, 70]) 0
    (slot _ 20 0 (by decide) (by decide)) = ⟨none, 20⟩ := by decide
example : place (map 64 .b128).fourRows ![-16, -3] (some ![-3, 5, 64, 70]) 0
    (slot _ 10 1 (by decide) (by decide)) = ⟨none, 154⟩ := by decide
example : place (map 64 .b128).fourRows ![-16, -3] (some ![-3, 5, 64, 70]) 0
    (slot _ 20 2 (by decide) (by decide)) = ⟨none, 308⟩ := by decide
-- The row coordinates, not `origin 1 + row`, select the tensor row.
example : (place (map 64 .none).fourRows ![16, 9] none 256
    (slot _ 5 2 (by decide) (by decide))).1 = some (4096 + 11 * 256 + 21) := by decide
-- Distinct slots of a gather4 copy have distinct destinations.
example : Function.Injective (fun s : Slot (map 128 .b128).fourRows =>
      TensorTile.sharedByte (map 128 .b128).fourRows.box 1 .b128 384 s.1.val s.2.1.val s.2.2.val) :=
  sharedByte_injective _ _

/-! ## Large-class OOB backing sees each row -/

example : TensorHasOob (map 64 .none).fourRows ![0, 0] (some ![0, 1, 64, 2]) := by
  refine ⟨slot _ 0 2 (by decide) (by decide), fun h => ?_⟩
  have h1 := h 1
  norm_num [TensorDescriptor.geometry, TensorTransfer.coord, slot, map,
    TensorDescriptor.Descriptor.fourRows] at h1
example : TensorHasOob (map 64 .none).fourRows ![-16, 0] (some ![0, 1, 63, 2]) := by
  refine ⟨slot _ 0 0 (by decide) (by decide), fun h => ?_⟩
  have h0 := h 0
  norm_num [TensorDescriptor.geometry, TensorTransfer.coord, slot, map,
    TensorDescriptor.Descriptor.fourRows] at h0

/-! ## The issue rule -/

private def maps (address : Nat) : Option ((outer : Nat) × TensorDescriptor.Descriptor outer) :=
  if address = 1024 then some ⟨1, map 64 .none⟩
  else if address = 2048 then some ⟨1, { map 64 .none with box := ⟨![64, 2], ![1, 1]⟩ }⟩
  else if address = 3072 then some ⟨2, ⟨.u8, 4096, ![256, 64, 2], ![256, 16384],
    ⟨![64, 1, 1], ![1, 1, 1]⟩, .none, .zero, .small⟩⟩
  else none
private def L : Launch := {
  grid := 2, block := 128, params := fun _ => none, clusterSize := ⟨2, by decide⟩, tensorMaps :=
    maps }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 256)
  | 1 => some (.bits 32 64)
  | 8 => some (.bits 64 1024)
  | 9 => some (.bits 64 2048)
  | 12 => some (.bits 64 3072)
  | _ => none }
private def ys : List Opnd := [.imm 16, .imm 9, .imm 2, .imm 40, .imm (-2)]
private def load (m : Nat) (cs : List Opnd) : Op :=
  .cpTensor false false 0 0 (.reg m) cs 1 0 none .fourRows
/-- The issued rank, origin, row coordinates, transfer rows and bytes of a template. -/
private def issued : Tmpl → Option (Nat × List Int × Option (List Int) × Nat × Nat)
  | .tensorIssue _ s _ =>
    some (s.outer, List.ofFn s.origin, s.rows.map List.ofFn, rows s.descriptor.box,
      bytes s.descriptor)
  | _ => none

-- The issue records `(x, y0)`, the four signed row coordinates and the four-row box.
example : issued (tensorTmpl L 0 t (load 8 ys)) =
    some (1, [16, 9], some [9, 2, 40, -2], 4, 256) := rfl
-- The same instruction in tile mode would need two coordinates.
example : tensorTmpl L 0 t (.cpTensor false false 0 0 (.reg 8) ys 1 0 none .tile) =
    .ub .badValue := rfl
-- Box dimension 1 must be one (other values trap on the B200).
example : tensorTmpl L 0 t (load 9 ys) = .ub .badValue := rfl
-- gather4 needs a 2D map, and five coordinates.
example : tensorTmpl L 0 t (load 12 ys) = .ub .badValue := rfl
example : tensorTmpl L 0 t (load 8 (ys.take 4)) = .ub .badValue := rfl
-- The destination must be 128-byte aligned.
example : tensorTmpl L 0 t (.cpTensor false false 0 64 (.reg 8) ys 1 0 none .fourRows) =
    .ub .misaligned := rfl
-- A successful unicast issue is the copy of `tensorLoadCopy` and continues at the next instruction.
example {a : Nat} {s : TensorCopy.Spec} {u : TState}
    (h : tensorTmpl L 0 t (load 8 ys) = .tensorIssue a s u) :
    s.rows.isSome := by
  obtain ⟨hc, -⟩ := tensorTmpl_unicast_issue h
  obtain ⟨-, -, d, -, -, -, hr⟩ := tensorLoadCopy_ok hc
  cases hs : s.rows with
  | none => cases hr.mp hs
  | some _ => rfl

-- An unaligned inner start traps, as in tile mode (EXT-TMA-BOX-ALIGN).
example : ¬ TensorDescriptor.BoxAligned (map 64 .none).fourRows ![8, 0] ∧
    TensorDescriptor.BoxAligned (map 64 .none).fourRows ![-16, 0] := by decide

/-! ## With `.multicast::cluster` (`Tools/probes/tma_mc_gather4.ptx`: 4-CTA cluster, masks 0xF,
0x5, 0xA, 0xE, 0x1 matched every CTA's buffer on a B200) -/

private def mcL : Launch := {
  grid := 8, block := 128, params := fun _ => none, clusterSize := ⟨4, by decide⟩, tensorMaps :=
    maps }
private def mcState (mask sub : Nat) : TState := { pc := 7, sub, regs := fun
  | 0 => some (.bits 32 1024)
  | 1 => some (.ptr 32 false (.shared 0 0) 64)
  | 8 => some (.bits 64 1024)
  | 11 => some (.bits 16 (BitVec.ofNat 64 mask))
  | _ => none }
private def mcOp : Op :=
  .cpTensor true false 0 0 (.reg 8) [.imm 0, .imm 5, .imm 8, .imm 6, .imm 12] 1 0
    (some (16, .reg 11)) .fourRows
/-- Destination CTA, row coordinates, transfer bytes and the continuation's (pc, sub step). -/
private def mcStep : Tmpl → Option (Nat × Option (List Int) × Nat × Nat × Nat)
  | .tensorIssue _ s u => some (s.sharedBase.cta, s.rows.map List.ofFn, bytes s.descriptor, u.pc,
    u.sub)
  | _ => none

-- Each destination gets the same four rows and byte count; the mask's ranks in order.
example : mcStep (tensorTmpl mcL 0 (mcState 0b0101 0) mcOp) =
    some (0, some [5, 8, 6, 12], 256, 7, 1) := rfl
example : mcStep (tensorTmpl mcL 0 (mcState 0b0101 1) mcOp) =
    some (2, some [5, 8, 6, 12], 256, 8, 0) := rfl
example : tensorTmpl mcL 0 (mcState 0 0) mcOp = .ub .badValue := rfl

end
end PTX.Tests.TensorGather4
