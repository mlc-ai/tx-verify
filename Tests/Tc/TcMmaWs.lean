-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.Tcgen05.TcMmaResultLayout
public import Lemmas.Tcgen05.MmaOperandObservations
public import Core.Tc.TcGroup

/-! `tcgen05.mma.ws`: Table 48 shapes, Layouts E and G, decoding and the shared issue rule. -/
namespace PTX.Tests.TcMmaWs
open PTX.TcMma
noncomputable section

/-! ## Instruction descriptors -/

def g32 : Descriptor := ⟨.one, .f16 .f16 .f32, 32, 64, false, false, false, false, true⟩
def e64 : Descriptor := ⟨.one, .i8 true true false, 64, 128, false, false, false, false, true⟩
def d128 : Descriptor := ⟨.one, .f16 .bf16 .f32, 128, 256, false, false, false, false, true⟩

-- M = 32, N = 64, FP16 inputs, FP32 D.
example : decode .one true .f16 (2 * 2 ^ 24 + 8 * 2 ^ 17 + 16) = some g32 := rfl
-- M = 64, N = 128, signed 8-bit inputs, S32 D.
example : decode .one true .i8 (4 * 2 ^ 24 + 16 * 2 ^ 17 + 32 + 128 + 1024) = some e64 := rfl
example : decode .one true .f16 (8 * 2 ^ 24 + 32 * 2 ^ 17 + 16 + 128 + 1024) = some d128 := rfl
-- M = 32 exists only with .ws; .ws has no cta_group::2 and only N ∈ {64, 128, 256}.
example : decode .one false .f16 (2 * 2 ^ 24 + 8 * 2 ^ 17 + 16) = none := rfl
example : decode .two true .f16 (8 * 2 ^ 24 + 8 * 2 ^ 17 + 16) = none := rfl
example : decode .one true .f16 (2 * 2 ^ 24 + 9 * 2 ^ 17 + 16) = none := rfl
example : decode .one true .f16 (4 * 2 ^ 24 + 24 * 2 ^ 17 + 16) = none := rfl
-- A non-zero B-reuse shift (bits 30–31) has no represented meaning.
example : decode .one true .f16 (2 ^ 30 + 2 * 2 ^ 24 + 8 * 2 ^ 17 + 16) = none := rfl
-- Integer saturation is a kind::i8 flag in .ws mode too.
example : decode .one true .i8 (8 + 4 * 2 ^ 24 + 16 * 2 ^ 17 + 32 + 128 + 1024) =
    some { e64 with kind := .i8 true true true } := rfl
-- M = 64 is valid in both modes but selects different layouts: F without .ws, E with it.
example : halfDatapath ⟨.one, .i8 true true false, 64, 64, false, false, false, false, false⟩ =
    true := rfl
example : halfDatapath ⟨.one, .i8 true true false, 64, 64, false, false, false, false, true⟩ =
    false := rfl

/-! ## Layouts -/

private def smem : TcShared.Descriptor := ⟨0, 0, 1024, 0, false, false, .b128⟩
def spec (d : Descriptor) : OperandSpec := ⟨d, smem, smem, 3, 3, none, {}⟩

-- Layout G (M = 32, 1x4): N splits into four blocks of N/4 columns, block b in lanes 32b..32b+31.
example : resultColumns g32 = 16 := rfl
example : resultCell (spec g32) 100 5 17 = some ⟨3, 37, 101⟩ := rfl
example : resultCell (spec g32) 100 31 63 = some ⟨3, 127, 115⟩ := rfl
example : resultCell (spec g32) 100 0 0 = some ⟨3, 0, 100⟩ := rfl
-- Layout E (M = 64, 2x2): two blocks of N/2 columns, lanes 0..63 and 64..127.
example : resultColumns e64 = 64 := rfl
example : resultCell (spec e64) 0 10 70 = some ⟨3, 74, 6⟩ := rfl
example : resultCell (spec e64) 0 63 127 = some ⟨3, 127, 63⟩ := rfl
-- .ws with M = 128 is Layout D.
example : resultColumns d128 = 256 := rfl
example : resultCell (spec d128) 256 100 255 = some ⟨3, 100, 511⟩ := rfl
-- Out-of-range rows/columns and column ranges past 512 have no cell; .ws has no lane-16 alignment.
example : resultCell (spec g32) 100 32 0 = none := rfl
example : resultCell (spec g32) 100 0 64 = none := rfl
example : resultCell (spec g32) 497 0 0 = none := rfl
example : resultCell (spec e64) (16 * 2 ^ 16) 0 0 = none := rfl

-- Distinct matrix elements occupy distinct TMEM cells (checked exhaustively for Layout G).
example : ∀ r < 32, ∀ c < 64, ∀ r' < 32, ∀ c' < 64,
    r + 32 * (c / 16) = r' + 32 * (c' / 16) → c % 16 = c' % 16 → r = r' ∧ c = c' := by
  intro r hr c hc r' hr' c' hc' hl hcol; omega
-- Every cell of a valid .ws issue is a physical cell.
example {row col : Nat} {cell : Cell} (h : resultCell (spec g32) 100 row col = some cell) :
    cell.lane < 128 ∧ cell.column < 512 := resultCell_bounds h

-- Writes are unmasked: the all-zero mask the issue rule supplies writes every result cell.
example : writeCell (spec e64) 0 [0, 0, 0, 0] 63 127 = some ⟨3, 127, 63⟩ := rfl
example : writeCell (spec g32) 100 [0, 0, 0, 0] 31 63 = some ⟨3, 127, 115⟩ := rfl

/-! ## Decoding and issue -/

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩, ⟨"rd".toList, 2, 64⟩, ⟨"p".toList, 1, 1⟩], labels := [],
      params := [] }
private def wsArgs : List Syntax.Operand :=
  [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1", .register "p0"]

example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::f16" wsArgs =
    .ok (.tcMma <| .dense .one true .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6)) := rfl
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::i8.collector::b2::fill" wsArgs =
    .ok (.tcMma { TcMmaInstr.dense .one true .i8 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6) with collectorB := .fill, bBuffer := 2 }) := rfl
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::f16.collector::b0::discard" wsArgs =
    .ok (.tcMma <| .dense .one true .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6)) := rfl
-- Collector reuse reads B from the collector buffer: the usage is recorded and every reuse must
-- justify its fill (ERR-TC-COLLECTOR-REUSE).
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::f16.collector::b0::use" wsArgs =
    .ok (.tcMma { TcMmaInstr.dense .one true .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6) with collectorB := .use }) := rfl
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::f16.collector::b3::lastuse" wsArgs =
    .ok (.tcMma { TcMmaInstr.dense .one true .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6) with collectorB := .lastuse, bBuffer := 3 }) := rfl
-- There is no cta_group::2 form; the zero-column mask is recorded and its value is checked by the
-- issue rule; kind::tf32 and kind::f8f6f4 are decoded.
example : (Decode.op env "tcgen05.mma.ws.cta_group::2.kind::f16" wsArgs).toOption = none := rfl
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::f16" (wsArgs ++ [.register "rd0"]) =
    .ok (.tcMma { TcMmaInstr.dense .one true .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6) with zeroColumnMask := some (.reg 4) }) := rfl
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::tf32" wsArgs =
    .ok (.tcMma <| .dense .one true .tf32 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6)) := rfl
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::f8f6f4" wsArgs =
    .ok (.tcMma <| .dense .one true .f8f6f4 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6)) := rfl

private def launch : Launch :=
  { grid := 8, block := 128, params := fun _ => none, clusterSize := 1 }
private def wsState (idesc : Nat) : TState := { regs := fun
  | 0 => some (.bits 32 0)
  | 4 => some (.bits 64 4611756662049472576)
  | 5 => some (.bits 64 4611756662049480768)
  | 1 => some (.bits 32 idesc)
  | 6 => some (.pred true)
  | _ => none }
private def wsOp (k : MmaKind) : Op :=
  .tcMma <| .dense .one true k 0 (.smem (.reg 4)) (.reg 5) (.reg 1) (List.replicate 4 (.imm 0))
    (.reg 6)
private def wsSpec (d : Descriptor) (cta : Nat) : OperandSpec := {
  descriptor := d
  a := ⟨1024, 0, 1024, 0, false, false, .b128⟩
  b := ⟨132096, 0, 1024, 0, false, false, .b128⟩
  lowCta := cta
  highCta := cta
  aTmem := none }

-- One issuing thread produces the ordinary MMA event, in its own CTA, with every lane enabled.
example : tcTmpl launch (5 * 128 + 9) (wsState (4 * 2 ^ 24 + 16 * 2 ^ 17 + 32 + 128 + 1024))
    (wsOp .i8) =
    .tc (.mma 0 (wsSpec e64 5) true [0, 0, 0, 0])
      (next (wsState (4 * 2 ^ 24 + 16 * 2 ^ 17 + 32 + 128 + 1024))) := rfl
example : eventTmpl [] launch 0 (wsState (2 * 2 ^ 24 + 8 * 2 ^ 17 + 16)) (wsOp .f16) =
    .tc (.mma 0 (wsSpec g32 0) true [0, 0, 0, 0])
      (next (wsState (2 * 2 ^ 24 + 8 * 2 ^ 17 + 16))) := rfl
-- A .ws-only shape is not accepted by the non-.ws instruction, and vice versa.
example : tcTmpl launch 0 (wsState (2 * 2 ^ 24 + 8 * 2 ^ 17 + 16))
    (.tcMma <| .dense .one false .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6)) = .ub .noRule := rfl
example : tcTmpl launch 0 (wsState (8 * 2 ^ 24 + 1 * 2 ^ 17 + 16)) (wsOp .f16) = .ub .noRule := rfl
-- .ws is cta_group::1 for the kernel's uniform-group check.
example : (wsOp .f16).tcGroup = some 1 := rfl

end
end PTX.Tests.TcMmaWs
