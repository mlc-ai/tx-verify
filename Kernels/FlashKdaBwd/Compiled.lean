-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaBwd.Ptx
public import Core.Source.Decode
public import Core.Float.Round
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # Compiled sigmoid backward specialization from the one-token FLA public call
The indices below are instruction counters after label resolution. The inputs come from one
of eight unrolled scalar chains in the generated entry. -/
@[expose] public section
namespace FlashKda.Backward.Compiled
open PTX

def op (kind : FOp) (mode : FMode) (dst : Nat) (src : List Opnd) : Instr :=
  ⟨none, .float { op := kind, ty := ⟨.f32, 1⟩, mode, dsts := [some dst], srcs := src }⟩

def chain : Option (List Instr) := do
  let m := Generated.FlaKdaBwd.module
  let p ← (Decode.prepare m.globals m.functions[0]!).toOption
  [92,103,111,112,120,128,136,144,160].mapM fun pc => do
    let s ← p.instrs[pc]?
    let .ok [i] := Decode.code p.env pc [s] | none
    return i

set_option maxRecDepth 10000 in
/-- Recover the exponential, denominator, reciprocal, subtraction, product and narrowing
from the actual FLA specialization, including the data dependency through the denominator. -/
theorem compiled_chain : chain = some [
    op .ex2 .approx 59 [.reg 57], op .add .ieee 73 [.reg 59, .f32imm 0x3f800000],
    ⟨none, .move {
      kind := .scalar, ty := .int .b 32, dsts := [some 81], srcs := [.f32imm 0x3f800000]}⟩,
    op .div .full 82 [.reg 81, .reg 73], op .mul .ieee 90 [.reg 40, .reg 30],
    op .mul .ieee 98 [.reg 90, .reg 82], op .sub .ieee 106 [.reg 81, .reg 82],
    op .mul .ieee 114 [.reg 98, .reg 106],
    ⟨none,.cvt {
      dst := .float .bf16, src := .float .f32, rnd := some .rn, d := 13, srcs := [.reg 114]}⟩] := by
  rfl

/-- Any positive exponential below the midpoint between one and the next binary32 word
rounds away in the denominator. This statement is conditional on the exponential's result. -/
theorem denominator_rounds_to_one {e : ℝ} (he : 0 < e) (ht : e < 1/2^24) :
    (Layout.binary 8 23 true .ieee).round .rn .inf (1+e) false = some (.fin 1) := by
  have hp : 0 ≤ 1+e := by linarith
  rw [Layout.round_between (m := .rn) (F := 0x3f800000) (by trivial) (by decide)
    (by rw [abs_of_nonneg hp]; norm_num [Layout.magnitude, Layout.bias]; linarith)
    (by rw [abs_of_nonneg hp]; norm_num [Layout.magnitude, Layout.bias] at *; linarith)
    (by simp)]
  norm_num [RoundMode.away, abs_of_nonneg hp, Layout.magnitude, Layout.bias, Layout.fieldVal,
    show ¬1+e < 0 by linarith]
  norm_num at ht
  intro h
  linarith

end FlashKda.Backward.Compiled
