-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Tc.TcGroup
public import Core.Tc.TcMmaSafety

/-! The `tcgen05.cp` shapes and multicasts (PROG-ISA-TC-CP, THREAD-TC-CP-CELLS,
DEP-TMEM-COPY-VALUE): decoding, the lanes of each source row, and the rejected forms. -/
namespace PTX.Tests.TcCpShapes
open PTX.TcCopy
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 2, 32⟩, ⟨"rd".toList, 1, 64⟩], labels := [], params := [] }

private def cp (q : String) : Except String Op :=
  Decode.op env q [.address [.register "r0"], .register "rd0"]

private def unmodeled : Except String Op → Bool
  | .ok (.unmodeled _) => true
  | _ => false

/-! ## Decoding -/

example : cp "tcgen05.cp.cta_group::1.128x128b" = .ok (.tcCp .one .s128x128b 0 (.reg 2)) := rfl
example : cp "tcgen05.cp.cta_group::2.128x256b" = .ok (.tcCp .two .s128x256b 0 (.reg 2)) := rfl
example : cp "tcgen05.cp.cta_group::1.64x128b.warpx2::02_13" =
    .ok (.tcCp .one (.s64x128b true) 0 (.reg 2)) := rfl
example : cp "tcgen05.cp.cta_group::2.64x128b.warpx2::01_23" =
    .ok (.tcCp .two (.s64x128b false) 0 (.reg 2)) := rfl
example : cp "tcgen05.cp.cta_group::1.32x128b.warpx4" = .ok (.tcCp .one .s32x128b 0 (.reg 2)) :=
  rfl
-- `.4x256b` and the decompressing forms.
example : cp "tcgen05.cp.cta_group::1.4x256b" = .ok (.tcCp .one .s4x256b 0 (.reg 2)) := rfl
example : cp "tcgen05.cp.cta_group::2.128x128b.b8x16.b6x16_p32" =
    .ok (.tcCp .two .s128x128b 0 (.reg 2) (some .b6x16p32)) := rfl
example : cp "tcgen05.cp.cta_group::1.128x128b.b8x16.b4x16_p64" =
    .ok (.tcCp .one .s128x128b 0 (.reg 2) (some .b4x16p64)) := rfl
example : unmodeled (cp "tcgen05.cp.cta_group::1.4x256b") = false := rfl
-- Rejected: a multicast with a shape that does not take it.
example : (cp "tcgen05.cp.cta_group::1.128x256b.warpx4").toOption = none := rfl
example : (Op.tcCp .two .s128x256b 0 (.reg 2)).tcGroup = some 2 := rfl
example : (Op.tcCp .one .s32x128b 0 (.reg 2)).rule = some .threadTc := rfl

/-! ## Geometry -/

example : (TcCpShape.s128x256b.sourceBytes, TcCpShape.s128x128b.sourceBytes,
    (TcCpShape.s64x128b true).sourceBytes, TcCpShape.s32x128b.sourceBytes) =
    (4096, 2048, 1024, 512) := rfl
-- `.warpx2::02_13`: rows 0..31 to warps 0 and 2, rows 32..63 to warps 1 and 3.
example : (TcCpShape.s64x128b true).lanes 5 = [5, 69] := rfl
example : (TcCpShape.s64x128b true).lanes 40 = [40, 104] := rfl
-- `.warpx2::01_23`: rows 0..31 to warps 0 and 1, rows 32..63 to warps 2 and 3.
example : (TcCpShape.s64x128b false).lanes 5 = [5, 37] := rfl
example : (TcCpShape.s64x128b false).lanes 40 = [72, 104] := rfl
-- `.warpx4`: every warp.
example : TcCpShape.s32x128b.lanes 7 = [7, 39, 71, 103] := rfl
-- `.4x256b`: 4 rows of 32 bytes, row `r` to lane `32 r` (EXT-TCCP).
example : (TcCpShape.s4x256b.sourceBytes, TcCpShape.s4x256b.lanes 0, TcCpShape.s4x256b.lanes 3) =
    (128, [0], [96]) := rfl
example : AddressOk .s4x256b 504 := by decide
example : ¬ AddressOk .s4x256b 505 := by decide
-- Source byte 21 of a 128-bit row is byte 5 of row 1, in column 1 of the address.
example : cell .s128x128b 10 3 1 21 = ⟨3, 1, 11⟩ := rfl
-- The address needs lane field 0 and the shape's columns within 512.
example : AddressOk .s128x128b 508 := by decide
example : ¬ AddressOk .s128x256b 508 := by decide
example : ¬ AddressOk .s128x128b (2 ^ 16) := by decide
-- The word of a 16-byte row.
example (b : Byte) : (word .s128x128b (List.replicate 32 (some b)) 1 3).isSome = true := rfl
example (b : Byte) : word .s128x128b ((List.replicate 31 (some b)) ++ [none]) 1 3 = none := rfl

end
end PTX.Tests.TcCpShapes
