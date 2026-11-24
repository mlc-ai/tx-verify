-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.MatrixLayout

/-! Fragment layouts of the warp-level matrix instructions (THREAD-MATRIX-LAYOUT), checked against
the formulas of §9.7.16.5 and §9.7.16.6 and the figures of `ldmatrix`, `stmatrix`, `movmatrix`
and the sparse metadata (EXT-MATRIX-FIGURES, EXT-MMA-SPARSE-FIGURES, EXT-MMA-FRAGMENTS). -/
namespace PTX.Tests.MatrixLayout

/-! ## `ldmatrix` and `stmatrix` -/

private def ld (shape : MatrixShape) (num : Nat) (trans : Bool) (fmt : MatrixFmt) : MatrixMove :=
  { store := false, shape, num, trans, fmt }

-- Figure 107: lane 5 holds row 1, columns 2 and 3 (bytes 4 to 7 of the row).
example : (List.range 4).map ((ld .m8n8 1 false .b16).source 5 0) =
    [(1, 4), (1, 5), (1, 6), (1, 7)] := by decide
-- `.x4`: register 3 of lane 31 holds the last row of the fourth matrix, supplied by thread 31.
example : (ld .m8n8 4 false .b16).source 31 3 0 = (31, 12) := by decide
-- `.trans`: lane 5 (row 1, columns 2 and 3 of the figure) holds element 1 of memory rows 2 and 3.
example : (List.range 4).map ((ld .m8n8 1 true .b16).source 5 0) =
    [(2, 2), (2, 3), (3, 2), (3, 3)] := by decide
-- Figure 108 with the mandatory `.trans`: register 1 of lane 6 (row 9, columns 8 to 11 of the
-- figure) holds byte 9 of memory rows 8 to 11; `.x2` puts the second matrix in registers 2 and 3,
-- with rows from threads 16 to 31.
example : (List.range 4).map ((ld .m16n16 2 true .b8).source 6 1) =
    [(8, 9), (9, 9), (10, 9), (11, 9)] := by decide
example : (ld .m16n16 2 true .b8).source 6 2 0 = (24, 1) := by decide
-- Figure 111 with the mandatory `.trans`: element e2 of lane 5 is row 9, column 2 of the 16x8
-- matrix, which is byte 9 of memory row 2.
example : ({ store := true, shape := .m16n8, num := 1, trans := true, fmt := .b8 } :
    MatrixMove).source 5 0 2 = (2, 9) := by decide

-- Figures 112 and 113: lane 5's result holds column 1, rows 2 and 3 of the source; source row 2,
-- columns 0 and 1 are in lane 8, so column 1 is its high half.
example : (List.range 4).map (transposeSource 5) = [(8, 2), (8, 3), (12, 2), (12, 3)] := by
  decide
-- Lane 6 (column 1, rows 4 and 5 of the source) reads the high halves of lanes 16 and 20.
example : (List.range 4).map (transposeSource 6) = [(16, 2), (16, 3), (20, 2), (20, 3)] := by
  decide

/-! ## `mma` -/

private def mma (m k : Nat) (a c d : DType) (aRow bCol : Bool := true) : MmaSpec :=
  { m, n := 8, k, aRow, bCol, types := { a, b := a, c, d } }

private def f16 : DType := .float .f16
private def f32 : DType := .float .f32
private def s32 : DType := .int .s 32

-- §9.7.16.5.8, A of `.m16n8k16` `.f16`: lane 6 (groupID 1, threadID_in_group 2), a5 is in row
-- groupID, column 2 * 2 + 1 + 8.
example : (mma 16 16 f16 f32 f32).fragA 6 5 = (0, 1, 13) := by decide
-- a2 is in row groupID + 8, column 4.
example : (mma 16 16 f16 f32 f32).fragA 6 2 = (0, 9, 4) := by decide
-- B: b3 of lane 6 is in row 2 * 2 + 1 + 8 = 13, column 1.
example : (mma 16 16 f16 f32 f32).fragB 6 3 = (0, 13, 1) := by decide
-- C and D: c3 of lane 6 is in row 9, column 5.
example : (mma 16 16 f16 f32 f32).fragCD f32 6 3 = (0, 9, 5) := by decide
-- §9.7.16.5.7, `.tf32` A of `.m16n8k8`: a1 in row groupID + 8, column threadID_in_group; a2 in
-- row groupID, column threadID_in_group + 4.
example : (mma 16 8 (.float .tf32) f32 f32).fragA 6 1 = (0, 9, 2) := by decide
example : (mma 16 8 (.float .tf32) f32 f32).fragA 6 2 = (0, 1, 6) := by decide
-- §9.7.16.5.10, `.s8` B of `.m16n8k32`: b5 of lane 6 in row 2 * 4 + 1 + 16 = 25.
example : (mma 16 32 (.int .s 8) s32 s32).fragB 6 5 = (0, 25, 1) := by decide
-- §9.7.16.5.11, `.s4` A of `.m16n8k64`: a20 of lane 6 in row groupID, column 2 * 8 + 4 + 32.
example : (mma 16 64 (.int .s 4) s32 s32).fragA 6 20 = (0, 1, 52) := by decide
-- §9.7.16.5.8, `.f64` A of `.m16n8k16`: a5 in row groupID + 8, column 5 * 2 - 2 + 2 = 10.
example : (mma 16 16 (.float .f64) (.float .f64) (.float .f64)).fragA 6 5 = (0, 9, 10) := by
  decide
-- EXT-MMA-FRAGMENTS: a40 of lane 6 is in row groupID + 8, column 2 * 32 + 8.
example : (mma 16 256 (.int .b 1) s32 s32).fragA 6 40 = (0, 9, 72) := by decide
-- §9.7.16.5.1, the four-MMA form: lane 21 is in computation 2 (lanes 4-7 and 20-23), high group.
example : (mma 8 4 f16 f16 f16).fragA 21 2 = (1, 5, 2) := by decide
example : (mma 8 4 f16 f16 f16 false).fragA 21 2 = (1, 6, 1) := by decide
example : (mma 8 4 f16 f16 f16).fragB 21 3 = (1, 3, 5) := by decide
example : (mma 8 4 f16 f16 f16 true false).fragB 21 3 = (1, 1, 7) := by decide
-- `.f32` C: row X + 4 with X = (21 & 1) + (6 & 2) = 3; column (6 & 4) + (21 & 2) + (6 & 1) = 4.
example : (mma 8 4 f16 f32 f32).fragCD f32 21 6 = (1, 7, 4) := by decide
-- `.f16` C: row 21 % 4 + 4, column i.
example : (mma 8 4 f16 f16 f16).fragCD f16 21 6 = (1, 5, 6) := by decide

/-- Every position of the A, B and C fragments of a shape is held by exactly one lane and
element: the fragment layout is a bijection onto the matrix. -/
private def bijective (f : Nat → Nat → Nat × Nat × Nat) (n : Nat) : Bool :=
  let ps := (List.range 32).flatMap fun l => (List.range n).map (f l)
  ps.Nodup

example : bijective (mma 16 16 f16 f32 f32).fragA 8 = true := by decide +kernel
example : bijective (mma 16 16 f16 f32 f32).fragB 4 = true := by decide +kernel
example : bijective ((mma 16 16 f16 f32 f32).fragCD f32) 4 = true := by decide +kernel
example : bijective (mma 8 4 f16 f32 f32).fragA 4 = true := by decide +kernel
example : bijective ((mma 8 4 f16 f32 f32).fragCD f32) 8 = true := by decide +kernel

/-! ## `mma.sp` metadata -/

private def sp (k : Nat) (a : DType) (sel : Nat) : MmaSpec :=
  { m := 16, n := 8, k, types := { a, b := a, c := f32, d := f32 }, sparse := some (true, sel) }

-- Figure 122: with selector 1, row 9, chunk 3 is in lane 4 * 1 + 1, bits 16 + 12.
example : (sp 16 f16 1).metaLoc 1 9 3 = (5, 28) := by decide
-- Figure 125: chunk 5 (columns 20 to 23) of row 0 with selector 1 is in lane 3, bits 4 to 7.
example : (sp 32 f16 1).metaLoc 1 0 5 = (3, 4) := by decide
-- Figure 132: row 8 (groupID 0, second half) with selector 1 is in lane 3, chunk 6 at bit 24.
example : (sp 32 (.int .u 8) 1).metaLoc 1 8 6 = (3, 24) := by decide
-- Figures 139 and 140: columns 32 to 35 (chunk 8) of row 9 are in lane 4 + 3, bits 0 to 3.
example : (sp 64 (.int .u 8) 0).metaLoc 0 9 8 = (7, 0) := by decide
-- Field 0b1101: indices 1 and 3; the first compressed element of chunk 2 is column 9, the second
-- column 11.
example : (sp 16 f16 0).sparseCol true 0xD 4 = some 9 := by decide
example : (sp 16 f16 0).sparseCol true 0xD 5 = some 11 := by decide
-- The ordered variant rejects indices not in increasing order; `.sp` accepts them, but not two
-- equal indices (0b0101).
example : (sp 16 f16 0).sparseCol true 0x7 0 = none := by decide
example : (sp 16 f16 0).sparseCol false 0x7 0 = some 3 := by decide
example : (sp 16 f16 0).sparseCol false 0x5 0 = none := by decide
-- `.tf32`: 0b0100 selects the first and 0b1110 the second of two columns; 0b1000 is undefined.
example : (sp 8 (.float .tf32) 0).sparseCol true 0x4 3 = some 6 := by decide
example : (sp 8 (.float .tf32) 0).sparseCol true 0xE 3 = some 7 := by decide
example : (sp 8 (.float .tf32) 0).sparseCol true 0x8 3 = none := by decide
-- 4-bit types: field 0b1100 selects the pairs 0 and 3 of the chunk; compressed elements 4 to 7
-- (chunk 1) are columns 8, 9, 14 and 15.
example : (List.range 4).map (fun c => (sp 64 (.int .s 4) 0).sparseCol true 0xC (4 + c)) =
    [some 8, some 9, some 14, some 15] := by decide

end PTX.Tests.MatrixLayout
