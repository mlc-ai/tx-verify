-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Tc.TcGroup

/-! The `tcgen05.mma` operand forms of the FlashAttention-4 forward kernel (THREAD-TC): no lane
mask, a constant `enable-input-d` (§4.5.3), A in Tensor Memory at `[a-tmem+imm]`
(THREAD-TC) with `cta_group::2` and M = 256 (EXT-TCFIG), and B MN-major with the
128-byte swizzle (THREAD-TC-SHARED-ADDRESS). -/
namespace PTX.Tests.TcMmaForms
open TcMma
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩, ⟨"rd".toList, 2, 64⟩, ⟨"p".toList, 1, 1⟩], labels := [],
      params := [] }

/-! ## Decoding -/

-- Without the lane-mask operand the mask is `4 * group size` zero words.
example : Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .register "p0"] =
    .ok (.tcMma <| .dense .two false .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 8 (.imm 0)) (.reg 6)) := rfl
example : Decode.op env "tcgen05.mma.cta_group::1.kind::i8"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .register "p0"] =
    .ok (.tcMma <| .dense .one false .i8 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6)) := rfl
-- `enable-input-d` may be an integer constant (FA4's QK MMAs: `0`, then `1`).
example : Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .literal "0"] =
    .ok (.tcMma <| .dense .two false .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 8 (.imm 0)) (.imm 0)) := rfl
-- A in Tensor Memory at a register plus a constant (FA4's PV MMAs), with a constant enable.
example : Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.register "r0"], .address [.offset "+" (.register "r2") (.literal "0x10")],
      .register "rd1", .register "r1", .literal "1"] =
    .ok (.tcMma <| .dense .two false .f16 0 (.tmem 2 16) (.reg 5) (.reg 1)
      (List.replicate 8 (.imm 0)) (.imm 1)) := rfl
example : Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.register "r0"], .address [.register "r2"], .register "rd1", .register "r1",
      .register "p0"] =
    .ok (.tcMma <| .dense .two false .f16 0 (.tmem 2 0) (.reg 5) (.reg 1)
      (List.replicate 8 (.imm 0)) (.reg 6)) := rfl
-- `.ws` takes the same enable operand.
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::f16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1", .literal "1"] =
    .ok (.tcMma <| .dense .one true .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.imm 1)) := rfl

-- Rejected: a float constant or a 32-bit register as enable-input-d, `scale-input-d`, an offset
-- on the destination address.
example : (Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .literal "0f3F800000"]).toOption = none := rfl
example : (Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .vector (List.replicate 8 (.register "r3")), .register "p0", .literal "3"]).toOption =
    none := rfl
example : (Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.offset "+" (.register "r0") (.literal "8")], .register "rd0", .register "rd1",
      .register "r1", .register "p0"]).toOption = none := rfl
example : (Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .register "r3"]).toOption = none := rfl

/-! ## Issue -/

private def launch : Launch :=
  { grid := 8, block := 384, params := fun _ => none, clusterSize := 4 }
-- FA4's PV MMA: idesc `0x10210010` (M = 256, N = 128, F16 inputs, F32 D, B transposed), B the
-- V descriptor (start 134144, stride 1024, 128-byte swizzle), D at column 256, A at column 64.
private def state : TState := { regs := fun
  | 0 => some (.bits 32 256)
  | 2 => some (.bits 32 64)
  | 5 => some (.bits 64 4611756662049480896)
  | 1 => some (.bits 32 270598160)
  | 6 => some (.pred false)
  | _ => none }
private def pv (off : Int) (en : Opnd) : Op :=
  .tcMma <| .dense .two false .f16 0 (.tmem 2 off) (.reg 5) (.reg 1) (List.replicate 8 (.imm 0)) en
private def vDesc : TcShared.Descriptor := ⟨134144, 0, 1024, 0, false, false, .b128⟩
private def pvDesc : Descriptor :=
  ⟨.two, .f16 .f16 .f32, 256, 128, false, false, false, true, false⟩
private def spec (aTmem : Nat) : OperandSpec := ⟨pvDesc, vDesc, vDesc, 6, 7, some aTmem, {}⟩

example : TcMma.decode .two false .f16 270598160 = some pvDesc := by decide
example : TcShared.decode 4611756662049480896 = some vDesc := by decide

-- The A address is the register plus the offset; a constant enable is false exactly at zero.
example : tcTmpl launch (7 * 384 + 3) state (pv 16 (.imm 1)) =
    .tc (.mma 256 (spec 80) true (List.replicate 8 0)) (next state) := rfl
example : tcTmpl launch (6 * 384 + 3) state (pv 56 (.imm 0)) =
    .tc (.mma 256 (spec 120) false (List.replicate 8 0)) (next state) := rfl
example : tcTmpl launch (6 * 384 + 3) state (pv 0 (.reg 6)) =
    .tc (.mma 256 (spec 64) false (List.replicate 8 0)) (next state) := rfl
-- An offset that leaves the column field faults instead of changing the lane field; so does a
-- predicate register holding a non-predicate value.
example : tcTmpl launch 3 state (pv (2 ^ 16) (.imm 1)) = .ub .badValue := rfl
example : tcTmpl launch 3 state (pv (-65) (.imm 1)) = .ub .badValue := rfl
example : tcTmpl launch 3 state (pv 0 (.reg 2)) = .ub .badValue := rfl
example : tmemOffset (5 * 2 ^ 16 + 64) 16 = .ok (5 * 2 ^ 16 + 80) := rfl

/-! ## A's Tensor Memory cells (EXT-TCFIG, Layout A)

A row has 16 FP16 elements (32 bytes) in eight 32-bit columns, two elements per word; rows
0–127 are lanes of the even CTA, rows 128–255 of the odd one. -/

-- Element `(r, k)` is byte `2 k` of row `r`: column `80 + k / 2`, low half for even `k`.
example : aCell (spec 80) 0 = some (⟨6, 0, 80⟩, 0) := by decide
example : aCell (spec 80) (32 * 5 + 2 * 3 + 1) = some (⟨6, 5, 81⟩, 3) := by decide
example : aCell (spec 80) (32 * 127 + 31) = some (⟨6, 127, 87⟩, 3) := by decide
example : aCell (spec 80) (32 * 128) = some (⟨7, 0, 80⟩, 0) := by decide
example : aCell (spec 80) (32 * 255 + 2 * 14) = some (⟨7, 127, 87⟩, 0) := by decide
example : aCell (spec 80) (32 * 256) = none := by decide
-- The A read covers every byte of the issue (`Operand.bytes .a pvDesc = 256 * 32`): no shared
-- location, all in Tensor Memory.
example : Operand.bytes .a pvDesc = 256 * 32 := rfl
example : ∀ r < 256, ∀ b < 32, (aCell (spec 80) (32 * r + b)).isSome := by decide +kernel
-- M = 128 with cta_group::2 (Layout B) has no A cells: such an issue is unsafe.
example : aCell ⟨{ pvDesc with m := 128 }, vDesc, vDesc, 6, 7, some 80, {}⟩ 0 = none := by decide

/-! ## B: V, MN-major with the 128-byte swizzle

B element `(n, k)` of the PV MMA is V's head-dimension column `n` (64 per CTA) and key row `k`.
The tensor copy wrote V's 128-byte rows by key row, swizzled on the absolute address; the
MMA reads the same byte. -/
example : (spec 80).byteLoc .b (32 * 37 + 2 * 5 + 1) =
    some ⟨.shared, 6, TensorSwizzle.offset .b128 0 (134144 + 128 * 5 + 2 * 37 + 1)⟩ := by decide
example : (spec 80).byteLoc .b (32 * (64 + 9) + 2 * 12) =
    some ⟨.shared, 7, TensorSwizzle.offset .b128 0 (134144 + 128 * 12 + 2 * 9)⟩ := by decide
-- The next K step's descriptor (`+0x80`, 2048 bytes) starts 16 key rows further.
example : TcShared.byteAddress 2 .mn { vDesc with start := 134144 + 2048 } 37 5 0 =
    some (TensorSwizzle.offset .b128 0 (134144 + 128 * (16 + 5) + 2 * 37)) := by decide

/-! ## A in shared memory: Q, K-major, a K step inside the swizzle atom

FA4 advances Q's descriptor by `+2` (32 bytes) per K step inside the 128-byte swizzle atom,
with the base-offset field zero. Element `k` of K step `j` is Q's column `16 j + k`. -/
private def qDesc : TcShared.Descriptor := ⟨68608, 16, 1024, 0, false, false, .b128⟩
example : TcShared.decode 4611756662049542336 = some qDesc := by decide
example : TcShared.decode 4611756662049542338 = some { qDesc with start := 68608 + 32 } := by
  decide
example : TcShared.byteAddress 2 .k { qDesc with start := 68608 + 32 } 11 3 1 =
    some (TensorSwizzle.offset .b128 0 (68608 + 128 * 11 + 2 * (16 + 3) + 1)) := by decide
example : ∀ r < 16, ∀ k < 16,
    TcShared.byteAddress 2 .k { qDesc with start := 68608 + 96 } r k 0 =
      some (TensorSwizzle.offset .b128 0 (68608 + 128 * r + 2 * (48 + k))) := by decide

end
end PTX.Tests.TcMmaForms
