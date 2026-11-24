-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Sync.WarpUniform

/-! `shfl.sync` with the modes `.up` and `.down` (§9.7.10.6): decoding, the rule, the source lane
and validity predicate that the pseudo-code computes at the boundaries of a segment, and the
event. -/
namespace PTX.Tests.ShflModes
open PTX.Syntax
noncomputable section

/-! ## Decoding and rules -/

-- `%r0` to `%r4` are registers 0 to 4 (32-bit); `%p0` is register 5 (predicate).
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 5, 32⟩, ⟨"%p".toList, 1, 1⟩], labels := [], params := [] }

private def up : WarpInstr :=
  { kind := .shfl .up, ty := some (.int .b 32), dsts := [some 0, some 5],
    srcs := [.reg 1, .reg 2, .reg 3], mask := some (.imm (-1)) }
private def down : WarpInstr := { up with kind := .shfl .down, dsts := [some 0] }

example : Decode.op env "shfl.sync.up.b32"
    [.pair [.register "%r0", .register "%p0"], .register "%r1", .register "%r2",
      .register "%r3", .literal "-1"] = .ok (.warp up) := rfl
example : Decode.op env "shfl.sync.down.b32"
    [.register "%r0", .register "%r1", .register "%r2", .register "%r3", .literal "-1"] =
    .ok (.warp down) := rfl
example : up.rule = some .threadShfl := rfl
example : down.rule = some .threadShfl := rfl
-- A shuffle requires a warp-uniform guard.
example : Op.uniform (.warp up) = true := rfl

/-! ## The source lane at its boundaries

`shflSource mode lane b c` is the source lane and the validity predicate. The segment mask is
bits 8 to 12 of `c` and the clamp is bits 0 to 4. -/

-- `.up`: a lane below `b` has no source lane and copies itself with predicate false.
example : shflSource .up 0 1 0 = (0, false) := by decide
example : shflSource .up 5 1 0 = (4, true) := by decide
-- `.up` with segments of 8 lanes: the lowest lane of a segment has no source in its segment.
example : shflSource .up 9 1 0x1800 = (8, true) := by decide
example : shflSource .up 8 1 0x1800 = (8, false) := by decide
-- `.down` with segments of 8 lanes: the highest lane of a segment has no source in it.
example : shflSource .down 6 1 0x181F = (7, true) := by decide
example : shflSource .down 7 1 0x181F = (7, false) := by decide
example : shflSource .down 31 1 31 = (31, false) := by decide
example : shflSource .down 30 1 31 = (31, true) := by decide
-- "Note that an out of range value of b may still result in a valid computed source lane index
-- j": only the low five bits of `b` are used, so 33 acts as 1.
example : shflSource .up 5 33 0 = (4, true) := by decide
example : shflSource .down 5 33 31 = (6, true) := by decide
example : ∀ lane < 32, shflSource .up lane 33 0 = shflSource .up lane 1 0 := by decide
-- `b = 0`: the lane is its own source, valid when the clamp allows it.
example : shflSource .up 5 0 0 = (5, true) := by decide
example : shflSource .up 5 0 31 = (5, false) := by decide
example : shflSource .down 5 0 31 = (5, true) := by decide
-- The other modes use the same segment rule.
example : shflSource .bfly 3 1 31 = (2, true) := by decide
example : shflSource .idx 3 7 31 = (7, true) := by decide

/-! ## The event -/

-- One warp of 32 threads; registers 1 to 3 hold the operands `a = 5`, `b = 1`, `c = 0`.
private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def t : TState :=
  { regs := fun r => if r = 1 then some (.bits 32 5#64) else if r = 2 then some (.bits 32 1#64)
    else if r = 3 then some (.bits 32 0#64) else none }

example : shflTmpl launch 0 t .up 0 (some 5) (.reg 1) (.reg 2) (.reg 3) (.imm (-1)) =
    .shfl .up (.bits 32 5#64) 1 0 (fun recv ok =>
      next (setReg (setReg t 0 recv) 5 (.pred ok))) := rfl
example : eventTmpl [] launch 0 t (.warp up) =
    .shfl .up (.bits 32 5#64) 1 0 (fun recv ok =>
      next (setReg (setReg t 0 recv) 5 (.pred ok))) := rfl
example : eventTmpl [] launch 0 t (.warp down) =
    shflTmpl launch 0 t .down 0 none (.reg 1) (.reg 2) (.reg 3) (.imm (-1)) := rfl
example : eventTmpl [] launch 0 t (.warp down) =
    .shfl .down (.bits 32 5#64) 1 0 (fun recv _ => next (setReg t 0 recv)) := rfl
-- A partial member mask has no rule.
example : shflTmpl launch 0 t .up 0 none (.reg 1) (.reg 2) (.reg 3) (.imm 3) = .ub .noRule := rfl
-- So has a CTA whose size is not a multiple of 32.
example : shflTmpl { launch with block := 2 } 0 t .down 0 none (.reg 1) (.reg 2) (.reg 3)
    (.imm (-1)) = .ub .noRule := rfl
-- An unset operand is a fault.
example : shflTmpl launch 0 {} .up 0 none (.reg 1) (.reg 2) (.reg 3) (.imm (-1)) =
    .ub .uninitialized := rfl

end
end PTX.Tests.ShflModes
