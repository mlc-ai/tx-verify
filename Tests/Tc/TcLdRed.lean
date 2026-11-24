-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode

/-! `tcgen05.ld.red` (PROG-ISA-TC-LD-RED, THREAD-TC-LD-RED): decoding, the reduction value and
the rejected cases. -/
namespace PTX.Tests.TcLdRed
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩], labels := [], params := [] }

private def maxU32 : TcLdRed := { isMax := true, ty := .u32, dst := 2 }

/-! ## Decoding -/

example : Decode.op env "tcgen05.ld.red.sync.aligned.32x32b.x2.max.u32"
    [.vector [.register "r0", .register "r1"], .register "r2", .address [.register "r3"]] =
    .ok (.tcLd [0, 1] 3 .s32x32b (some maxU32)) := rfl
example : Decode.op env "tcgen05.ld.red.sync.aligned.16x32bx2.x2.min.abs.NaN.f32"
    [.vector [.register "r0", .register "r1"], .register "r2", .address [.register "r3"],
      .literal "16"] =
    .ok (.tcLd [0, 1] 3 (.s16x32bx2 16)
      (some { isMax := false, ty := .f32, abs := true, nan := true, dst := 2 })) := rfl
-- Rejected: `.x1`, `redval` among the loaded registers.
example : (Decode.op env "tcgen05.ld.red.sync.aligned.32x32b.x1.max.u32"
    [.vector [.register "r0"], .register "r2", .address [.register "r3"]]).toOption = none := rfl
example : (Decode.op env "tcgen05.ld.red.sync.aligned.32x32b.x2.max.u32"
    [.vector [.register "r0", .register "r1"], .register "r1",
      .address [.register "r3"]]).toOption = none := rfl
-- It has THREAD-TC.
example : (Op.tcLd [0, 1] 3 .s32x32b (some maxU32)).rule = some .threadTc := rfl

/-! ## Reduction value -/

private def w (n : Nat) : Value := .bits 32 (BitVec.ofNat 64 n)

-- Unsigned and signed maximum and minimum of 32-bit patterns.
example : TcLdRed.reduceInt false true [w 5, w 0xFFFFFFFF] = .ok (w 0xFFFFFFFF) := rfl
example : TcLdRed.reduceInt true true [w 5, w 0xFFFFFFFF] = .ok (w 5) := rfl
example : TcLdRed.reduceInt true false [w 5, w 0xFFFFFFFF, w 7] = .ok (w 0xFFFFFFFF) := rfl
example : TcLdRed.reduceInt false false [w 5, w 3, w 7] = .ok (w 3) := rfl
-- A value that is not four bytes has no rule.
example : TcLdRed.reduceInt false true [w 5, .bits 16 (BitVec.ofNat 64 1)] =
    .error .typeMismatch := rfl
-- FP32: the loaded value that takes the extreme.
example : TcLdRed.reduceF32 true false [.float .f32 1, .float .f32 3] = .ok (.float .f32 3) := by
  norm_num [TcLdRed.reduceF32, valFloat, List.mapM, List.mapM.loop, List.filter]; rfl
-- `.abs`: the absolute value.
example : TcLdRed.reduceF32 true true [.float .f32 1, .float .f32 (-3)] =
    .ok (.float .f32 3) := by
  norm_num [TcLdRed.reduceF32, valFloat, List.mapM, List.mapM.loop]; rfl
-- The register state after a reduction without a rule records the fault.
example (t : TState) :
    (ldResult t [0] (some maxU32) [.bits 16 (BitVec.ofNat 64 1)]).fault = some .typeMismatch :=
  rfl
-- Without a reduction the load only sets its registers.
example (t : TState) (vals : List Value) : ldResult t [0, 1] none vals = setRegs t [0, 1] vals :=
  rfl

end
end PTX.Tests.TcLdRed
