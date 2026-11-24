-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Sync.MatrixExec
public import Core.Sync.Aligned

/-! The events of the warp-level matrix instructions (THREAD-MATRIX, THREAD-MMA-SYNC), the bytes a
lane receives in an instance (DEP-WARP-MATRIX, DEP-WARP-MMA) and the rejected cases: a CTA whose
size is not a multiple of 32, a misaligned row, a row outside shared memory, an exited lane, and
results that cannot be computed (ERR-WARP-MATRIX): saturation that may overflow, a missing
numerical rule and invalid sparse metadata. -/
namespace PTX.Tests.MatrixRun
noncomputable section

private def ldx1 (space : Option StateSpace) : MatrixInstr :=
  { op := .move { store := false, shape := .m8n8, num := 1, trans := false, fmt := .b16 },
    space, addr := some ⟨.reg 8 64, 0⟩, dsts := [0] }

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def at_ (x : Nat) : TState := { regs := fun r => if r = 8 then some (.bits 64 x) else none }

/-! ## The thread rule -/

-- A CTA whose size is not a multiple of 32 has no rule.
example : eventTmpl [] { launch with block := 33 } 0 (at_ 16) (.matrix (ldx1 (some (.shared .cta))))
    = .ub .noRule := rfl
-- Thread 0 supplies the row address of `.x1`: one 16-byte read of its row.
example : (match eventTmpl [] launch 0 (at_ 16) (.matrix (ldx1 (some (.shared .cta)))) with
    | .read a _ => some a
    | _ => none) = some { loc := ⟨.shared, 0, 16⟩, size := 16 } := rfl
-- "The matrix addresses must be naturally aligned accordingly."
example : eventTmpl [] launch 0 (at_ 24) (.matrix (ldx1 (some (.shared .cta)))) =
    .ub .misaligned := rfl
-- A generic number is a global address, outside `.shared`: undefined.
example : eventTmpl [] launch 0 (at_ 16) (.matrix (ldx1 none)) = .ub .badValue := rfl
-- Thread 9 supplies no address for `.x1`: it takes part with no bytes, without reading.
example : eventTmpl [] launch 9 (at_ 24) (.matrix (ldx1 none)) =
    .matrix (ldx1 none).op [] (afterMatrix (at_ 24) 32 [0]) := rfl
-- After its read (sub-step 1) thread 0 takes part with the bytes it read.
example : eventTmpl [] launch 0 { at_ 16 with sub := 1, acc := [byteValue (.bits 8 7, 0)] }
    (.matrix (ldx1 none)) = .matrix (ldx1 none).op [some (.bits 8 7, 0)]
      (afterMatrix { at_ 16 with sub := 1, acc := [byteValue (.bits 8 7, 0)] } 32 [0]) := rfl
-- Received bytes of another length are a fault.
example : (afterMatrix {} 32 [0] [some (.bits 8 7, 0)]).fault = some .typeMismatch := rfl
-- An unset source register of `movmatrix` is a fault.
example : eventTmpl [] launch 0 {} (.matrix { op := .transpose, dsts := [0], srcs := [.reg 1] }) =
    .ub .uninitialized := rfl

/-! ## Received bytes -/

private def byte (x : Nat) : Option Byte := some (.bits 8 (BitVec.ofNat 64 x), 0)
-- Lane `l` contributes the bytes `16 l` to `16 l + 15`.
private def rows (l : Nat) : List (Option Byte) := (List.range 16).map fun k => byte (16 * l + k)

private def mv (store : Bool) (shape : MatrixShape) (fmt : MatrixFmt) : MatrixMove :=
  { store, shape, num := 1, trans := false, fmt }

-- Figure 107: lane 5 receives bytes 4 to 7 of row 1.
example : (match matrixMoveRecv (mv false .m8n8 .b16) rows 5 with
    | .bytes bs => bs
    | .open_ _ => []) = [byte 20, byte 21, byte 22, byte 23] := rfl
-- The 6-bit source format leaves the received bytes open.
example : (match matrixMoveRecv (mv false .m8n16 (.b8x16 true)) rows 5 with
    | .bytes _ => 0
    | .open_ n => n) = 4 := rfl
-- Lane `l` holds the register bytes `4 l` to `4 l + 3`; byte 6 of row 1 of `stmatrix` comes from
-- byte 2 of lane 5 (Figure 110).
private def regs (l : Nat) : List (Option Byte) := (List.range 4).map fun b => byte (4 * l + b)
example : (mv true .m8n8 .b16).storeByte regs 1 6 = byte 22 := rfl
-- `movmatrix`: lane 5 receives the high halves of lanes 8 and 12.
example : transposeRecv regs 5 = [byte 34, byte 35, byte 50, byte 51] := rfl

/-! ## MMA values -/

private def tS8 : MmaTypes := { a := .int .s 8, b := .int .s 8, c := .int .s 32, d := .int .s 32 }
private def tF16 : MmaTypes :=
  { a := .float .f16, b := .float .f16, c := .float .f32, d := .float .f32 }
private def tB1 : MmaTypes := { a := .int .b 1, b := .int .b 1, c := .int .s 32, d := .int .s 32 }

private def s8mma (sat : Bool) : MmaSpec :=
  { m := 8, n := 8, k := 16, satfinite := sat, types := tS8 }

-- Every A element is `a`, every B element `b`, every C element `c`.
private def mmaParts (a b : Nat) (c : Int) (_ : Nat) : List (Option Byte) :=
  (List.replicate 4 (byte a)) ++ (List.replicate 4 (byte b)) ++
    ((TcMma.s32 c).toBytes ++ (TcMma.s32 c).toBytes).map some

-- D = 16 * (-1 * 2) + 5: `.s8` elements are two's complement.
example : mmaRecv [] (s8mma false) (mmaParts 0xFF 2 5) 0 =
    .ok (((TcMma.s32 (-27)).toBytes ++ (TcMma.s32 (-27)).toBytes).map some) := by
  rfl
-- "If .satfinite is not specified, the accumulated value is wrapped instead."
example : mmaRecv [] (s8mma false) (mmaParts 127 127 (2 ^ 31 - 1)) 0 =
    .ok (((TcMma.s32 (2 ^ 31 - 1 + 16 * 127 * 127)).toBytes ++
      (TcMma.s32 (2 ^ 31 - 1 + 16 * 127 * 127)).toBytes).map some) := by
  rfl
-- With `.satfinite` a partial sum may leave the s32 range: no rule.
example : mmaRecv [] (s8mma true) (mmaParts 127 127 (2 ^ 31 - 1)) 0 = .error .noRule := by
  rfl
-- Floating types have no Core arithmetic: without an assumption, no rule.
example : mmaValue [] { m := 16, n := 8, k := 8, types := tF16 } [.float .f16 1] [.float .f16 1]
    (.float .f32 0) = .error .noRule := rfl
-- Single-bit `.xor`: the bits differ in one of the two pairs.
example : mmaValue [] { m := 8, n := 8, k := 128, bitOp := some .xor, types := tB1 }
    [.bits 1 1, .bits 1 0] [.bits 1 1, .bits 1 1] (.bits 32 3) = .ok (TcMma.s32 4) := by
  rfl
-- Sparse metadata 0b0000 (two equal indices) is undefined behaviour.
example : mmaRecv [] { m := 16, n := 8, k := 16, sparse := some (false, 0), types := tS8 }
    (fun _ => List.replicate 36 (byte 0)) 0 = .error .badValue := by
  rfl

/-! ## An exited lane -/

private def op : MatrixOp := .transpose
private def X : Execution where
  tr g := if g = 0 then [⟨0, .matrix op [] []⟩] else if g = 1 then [⟨1, .exit⟩] else []
  rf _ _ := none

-- Lane 1 exited before the instance that lane 0 executes: undefined behaviour.
example (K : Kernel) : AlignedMismatch launch K X :=
  ⟨.matrix, .inr ⟨(0, 0), (1, 0), ⟨0, .matrix op [] []⟩,
    show SameWarp launch 0 1 from ⟨⟨by decide, by decide, by decide⟩, by decide⟩,
    rfl, rfl, rfl, ⟨⟨1, rfl⟩, show (X.tr 1).countP isMatrix ≤ 0 by decide⟩⟩⟩

end

end PTX.Tests.MatrixRun
