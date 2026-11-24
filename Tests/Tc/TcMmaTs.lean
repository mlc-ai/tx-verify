-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Tc.TcGroup

/-! `tcgen05.mma ... [d], [a-tmem], b-desc, ...` (EXT-TCFIG): A read from Tensor Memory. -/
namespace PTX.Tests.TcMmaTs
open TcMma
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩, ⟨"rd".toList, 2, 64⟩, ⟨"p".toList, 1, 1⟩], labels := [],
      params := [] }

-- The address form of A selects the Tensor Memory variant; the register form stays shared.
example : Decode.op env "tcgen05.mma.cta_group::1.kind::i8"
    [.address [.register "r0"], .address [.register "r2"], .register "rd1", .register "r1",
      .vector (List.replicate 4 (.register "r3")), .register "p0"] =
    .ok (.tcMma <| .dense .one false .i8 0 (.tmem 2 0) (.reg 5) (.reg 1)
      (List.replicate 4 (.reg 3)) (.reg 6)) := rfl
example : (Op.tcMma <| .dense .two false .f16 0 (.tmem 2 0) (.reg 5) (.reg 1) [] (.reg 6)).tcGroup =
    some 2 := rfl

private def launch : Launch :=
  { grid := 8, block := 384, params := fun _ => none, clusterSize := 4 }
private def k8 : TcShared.Descriptor := ⟨5120, 128, 256, 0, false, false, .none⟩
private def i8x1 : Descriptor := ⟨.one, .i8 true true false, 128, 8, false, false, false, false,
    false⟩
private def state : TState := { regs := fun
  | 0 => some (.bits 32 0)
  | 2 => some (.bits 32 (BitVec.ofNat 64 64))
  | 5 => some (.bits 64 (320 + 524288 + 70437463654400))
  | 1 => some (.bits 32 134349984)
  | 3 => some (.bits 32 0)
  | 6 => some (.pred false)
  | _ => none }
private def op : Op := .tcMma <| .dense .one false .i8 0 (.tmem 2 0) (.reg 5) (.reg 1)
  (List.replicate 4 (.reg 3)) (.reg 6)
private def spec (cta : Nat) : OperandSpec := ⟨i8x1, k8, k8, cta, cta, some 64, {}⟩

-- The issue records A's Tensor Memory address; the rest is the ordinary MMA rule.
example : tcTmpl launch (5 * 384 + 7) state op =
    .tc (.mma 0 (spec 5) false [0, 0, 0, 0]) (next state) := rfl
example : eventTmpl [] launch 3 state op = .tc (.mma 0 (spec 0) false [0, 0, 0, 0]) (next state) :=
    rfl
-- Transpose A (bit 15) is M-major A in shared memory only (§9.7.18.10.6); with A in Tensor
-- Memory the bit has no stated meaning, so the issue has no rule.
example : (TcMma.decode .one false .i8 (134349984 + 2 ^ 15)).map (·.transposeA) = some true := by
  decide
private def stateT : TState :=
  { state with regs := fun r => if r = 1 then some (.bits 32 (134349984 + 2 ^ 15)) else
               state.regs r }
example : tcTmpl launch (5 * 384 + 7) stateT op = .ub .noRule := rfl

/-! ## A's cells -/

-- Row r of A is lane r; its 32 bytes fill columns 64..71, four bytes per word.
example : aCell (spec 5) 0 = some (⟨5, 0, 64⟩, 0) := by decide
example : aCell (spec 5) (32 * 9 + 22) = some (⟨5, 9, 69⟩, 2) := by decide
example : aCell (spec 5) (32 * 127 + 31) = some (⟨5, 127, 71⟩, 3) := by decide
example : aCell (spec 5) (32 * 128) = none := by decide
-- Shared A has no Tensor Memory cells, and A in Tensor Memory has no shared location.
example : aCell { spec 5 with aTmem := none } 0 = none := rfl
example : (spec 5).byteLoc .a 0 = none := by decide
example : ((spec 5).byteLoc .b 0).isSome = true := by decide
-- A lane field other than 0, or columns past 512, have no cells.
example : aCell { spec 5 with aTmem := some (2 ^ 16) } 0 = none := by decide
example : aCell { spec 5 with aTmem := some 505 } 0 = none := by decide
-- Layout F (M = 64): A uses D's half-datapath lanes, at lane field 0 or 16.
example : aCell { spec 5 with descriptor := { i8x1 with m := 64 } } (32 * 17 + 5) =
    some (⟨5, 33, 65⟩, 1) := by decide
example : aCell { spec 5 with descriptor := { i8x1 with m := 64 }, aTmem := some (16 * 2 ^ 16 +
                              64) }
    (32 * 63) = some (⟨5, 16 + 15 + 96, 64⟩, 0) := by decide
example : aCell { spec 5 with descriptor := { i8x1 with m := 64 }, aTmem := some (8 * 2 ^ 16 + 64) }
    0 = none := by decide
example : aCell { spec 5 with descriptor := { i8x1 with m := 64 } } (32 * 64) = none := by decide
-- cta_group::2, M = 256: rows split between the pair like D.
private def pair : OperandSpec :=
  ⟨⟨.two, .f16 .f16 .f32, 256, 256, false, false, false, false, false⟩, k8, k8, 4, 5, some 0, {}⟩
example : aCell pair (32 * 3) = some (⟨4, 3, 0⟩, 0) := by decide
example : aCell pair (32 * 130 + 5) = some (⟨5, 2, 1⟩, 1) := by decide

/-! ## In an execution -/

private def X : Execution where
  tr := fun g => if g = 0 then [⟨0, .tc (.mma 0 (spec 0) false [0, 0, 0, 0])⟩] else []
  rf := fun _ _ => none

-- The MMA's A cells are part of its Tensor Memory access footprint (lifetime and conflicts).
example : X.MmaACell (0, 0) ⟨0, 9, 69⟩ := ⟨0, spec 0, false, _, 32 * 9 + 22, 2, ⟨0, rfl⟩, by decide⟩
example : X.MmaAccess (0, 0) ⟨0, 9, 69⟩ :=
  .inr (.inr ⟨0, spec 0, false, _, 32 * 9 + 22, 2, ⟨0, rfl⟩, by decide⟩)
-- A has no shared footprint, B keeps its shared one.
example (l : Loc) (k : Nat) : ¬ X.MmaFootprint (0, 0) false k l := by
  rintro (⟨d, s, acc, mask, ⟨pc, h⟩, hl⟩ | ⟨_, _, _, ⟨pc, h⟩, -⟩)
  · simp [Execution.get, X] at h
    obtain ⟨-, -, rfl, -, -⟩ := h
    simp [OperandSpec.byteLoc, spec] at hl
  · simp [Execution.get, X] at h

end
end PTX.Tests.TcMmaTs
