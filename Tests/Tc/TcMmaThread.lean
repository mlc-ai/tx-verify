-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.Tcgen05.TcMmaOperands

namespace PTX.Tests.TcMmaThread
noncomputable section

private def launch : Launch :=
  { grid := 8, block := 384, params := fun _ => none, clusterSize := 4 }
/-- A launch with one-CTA clusters: no CTA pair exists. -/
private def noPair : Launch := { grid := 8, block := 384, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩, ⟨"rd".toList, 2, 64⟩, ⟨"p".toList, 1, 1⟩], labels := [],
      params := [] }

-- Both production opcodes decode to the one MMA instruction, keeping group and kind.
example : Decode.op env "tcgen05.mma.cta_group::2.kind::f16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .vector (List.replicate 8 (.register "r3")), .register "p0"] =
    .ok (.tcMma <| .dense .two false .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 8 (.reg 3)) (.reg 6)) := rfl
example : Decode.op env "tcgen05.mma.cta_group::1.kind::i8"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .vector (List.replicate 4 (.register "r3")), .register "p0"] =
    .ok (.tcMma <| .dense .one false .i8 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.reg 3)) (.reg 6)) := rfl
example : Decode.op env "tcgen05.mma.cta_group::1.kind::tf32"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .vector (List.replicate 4 (.register "r3")), .register "p0"] =
    .ok (.tcMma <| .dense .one false .tf32 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.reg 3)) (.reg 6)) := rfl
private def noRule : Except String Op → Bool
  | .ok op => op.rule.isNone
  | _ => false
-- Kinds without a representation decode to an instruction with no rule.
example : noRule (Decode.op env "tcgen05.mma.cta_group::1.kind::ti16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .vector (List.replicate 4 (.register "r3")), .register "p0"]) = true := rfl

private def state (accumulate : Bool) : TState := { regs := fun
  | 0 => some (.bits 32 64)
  | 4 => some (.bits 64 4611756662049472576)
  | 5 => some (.bits 64 4611756662049480768)
  | 1 => some (.bits 32 272629776)
  | 3 => some (.bits 32 0)
  | 6 => some (.pred accumulate)
  | _ => none }
private def op : Op := .tcMma <| .dense .two false .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
  (List.replicate 8 (.reg 3)) (.reg 6)
private def spec : TcMma.OperandSpec := {
  descriptor := ⟨.two, .f16 .f16 .f32, 256, 256, false, false, false, false, false⟩
  a := ⟨1024, 0, 1024, 0, false, false, .b128⟩
  b := ⟨132096, 0, 1024, 0, false, false, .b128⟩
  lowCta := 6
  highCta := 7
  aTmem := none }

-- Issuing from either CTA selects the same pair. No read values appear in this event.
example : tcTmpl launch (7 * 384 + 3) (state true) op =
    .tc (.mma 64 spec true (List.replicate 8 0)) (next (state true)) := rfl
example : eventTmpl [] launch (6 * 384 + 17) (state false) op =
    .tc (.mma 64 spec false (List.replicate 8 0)) (next (state false)) := rfl

-- Nonzero output masks are retained, not replaced by an all-enabled assumption.
example : tcTmpl launch (7 * 384) (state true)
    (.tcMma <| .dense .two false .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      ([1, 2, 4, 8, 16, 32, 64, 128].map Opnd.imm) (.reg 6)) =
    .tc (.mma 64 spec true [1, 2, 4, 8, 16, 32, 64, 128]) (next (state true)) := rfl

example : tcTmpl launch (8 * 384) (state true) op = .ub .badValue := rfl
-- A cta_group::2 MMA needs a pair: in a launch whose clusters hold one CTA it faults.
example : tcTmpl noPair 0 (state true) op = .ub .badValue := rfl
-- The mask vector has four words per CTA of the group.
example : tcTmpl launch 0 (state true)
    (.tcMma <| .dense .two false .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.reg 3)) (.reg 6)) = .ub .badValue := rfl
example : tcTmpl launch 0 (state true)
    (.tcMma <| .dense .two false .f16 0 (.smem (.reg 4)) (.reg 5) (.imm 0)
      (List.replicate 8 (.reg 3)) (.reg 6)) = .ub .noRule := rfl
-- The kind qualifier selects the instruction-descriptor table.
example : tcTmpl launch 0 (state true)
    (.tcMma <| .dense .two false .i8 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 8 (.reg 3)) (.reg 6)) = .ub .noRule := rfl

-- cta_group::1, kind::i8, as in the integer GEMM: descriptors with start `16 s`,
-- leading offset 128 and stride 256, no swizzle; both operands in the issuer's CTA.
private def i8State : TState := { regs := fun
  | 11 => some (.bits 32 0)
  | 10 => some (.bits 64 (64 + 524288 + 70437463654400))
  | 9 => some (.bits 64 (320 + 524288 + 70437463654400))
  | 8 => some (.bits 32 134349984)
  | 7 => some (.bits 32 0)
  | 12 => some (.pred false)
  | _ => none }
private def i8Op : Op := .tcMma <| .dense .one false .i8 11 (.smem (.reg 10)) (.reg 9) (.reg 8)
  (List.replicate 4 (.reg 7)) (.reg 12)
private def i8Spec (cta : Nat) : TcMma.OperandSpec := {
  descriptor := ⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩
  a := ⟨1024, 128, 256, 0, false, false, .none⟩
  b := ⟨5120, 128, 256, 0, false, false, .none⟩
  lowCta := cta
  highCta := cta
  aTmem := none }

example : tcTmpl launch 5 i8State i8Op =
    .tc (.mma 0 (i8Spec 0) false [0, 0, 0, 0]) (next i8State) := rfl
example : tcTmpl launch (5 * 384 + 7) i8State i8Op =
    .tc (.mma 0 (i8Spec 5) false [0, 0, 0, 0]) (next i8State) := rfl
-- Eight mask words are a group-2 vector.
example : tcTmpl launch 5 i8State
    (.tcMma <| .dense .one false .i8 11 (.smem (.reg 10)) (.reg 9) (.reg 8)
      (List.replicate 8 (.reg 7)) (.reg 12)) = .ub .badValue := rfl
-- An i8 descriptor is not an f16 one.
example : tcTmpl launch 5 i8State
    (.tcMma <| .dense .one false .f16 11 (.smem (.reg 10)) (.reg 9) (.reg 8)
      (List.replicate 4 (.reg 7)) (.reg 12)) = .ub .noRule := rfl

-- Provenance follows from the common constructor, not a per-kernel hypothesis.
example {L : Launch} {issuer : Nat} {d : TcMma.Descriptor}
    {a b : TcShared.Descriptor} {s : TcMma.OperandSpec}
    (h : TcMma.makeOperands L issuer d a b = some s) : s.MatchesLaunch L issuer :=
  TcMma.makeOperands_matches h

end
end PTX.Tests.TcMmaThread
