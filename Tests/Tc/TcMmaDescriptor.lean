-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic
public import Lemmas.Tcgen05.MmaOperandObservations

namespace PTX.Tests.TcMmaDescriptor
open TcMma

private def f16 (m n : Nat) : Descriptor :=
  ⟨.two, .f16 .f16 .f32, m, n, false, false, false, false, false⟩
private def i8 (m n : Nat) : Descriptor :=
  ⟨.one, .i8 true true false, m, n, false, false, false, false, false⟩

-- The actual production PTX descriptors, not new kernel-specific Core constants.
example : decode .two false .f16 272629776 = some (f16 256 256) := rfl
example : decode .one false .i8 134349984 = some (i8 128 8) := rfl
example : decode .two false .f16 0x10400490 = some { f16 256 256 with kind := .f16 .bf16 .f32 } :=
    rfl
example : decode .two false .f16 0x10400000 = some { f16 256 256 with kind := .f16 .f16 .f16 } :=
    rfl
example : decode .two false .f16 0x08040010 = some (f16 128 16) := rfl

-- The `.kind` qualifier selects the type table: an i8 word is not an f16 one.
example : decode .two false .f16 134349984 = none := rfl
example : decode .one false .i8 272629776 = none := rfl
-- Unsigned and signed 8-bit inputs are independent per operand.
example : decode .one false .i8 (134349984 - 128) = some { i8 128 8 with kind :=
                                                                         .i8 false true false } :=
    rfl
example : decode .one false .i8 (134349984 - 1024) = some { i8 128 8 with kind :=
                                                                          .i8 true false false } :=
    rfl
-- i8 has only an S32 D, and no negation.
example : decode .one false .i8 (134349984 - 16) = none := rfl
example : decode .one false .i8 (134349984 + 2 ^ 13) = none := rfl
example : decode .one false .i8 (134349984 + 2 ^ 14) = none := rfl
-- Transposition is retained for i8 as for f16.
example : decode .one false .i8 (134349984 + 2 ^ 15) = some { i8 128 8 with transposeA := true } :=
    rfl

-- The same word decodes per CTA group: Table 48 shapes differ between groups.
example : decode .one false .f16 (8 * 2 ^ 24 + 1 * 2 ^ 17 + 16) =
    some { f16 128 8 with group := .one } := rfl
example : decode .two false .f16 (8 * 2 ^ 24 + 1 * 2 ^ 17 + 16) = none := rfl
example : decode .one false .f16 (16 * 2 ^ 24 + 2 * 2 ^ 17 + 16) = none := rfl
example : decode .two false .i8 (16 * 2 ^ 24 + 4 * 2 ^ 17 + 0x4a0) =
    some { i8 256 32 with group := .two } := rfl
example : decode .two false .i8 (16 * 2 ^ 24 + 2 * 2 ^ 17 + 0x4a0) = none := rfl

-- Every Table 48 dense group-2 f16 shape, not just the production 256x256 tile.
example (m : Fin 2) (n : Fin 16) :
    decode .two false .f16 ((if m.val = 0 then 8 else 16) * 2 ^ 24 + (n.val + 1) * 2 * 2 ^ 17 +
      16) =
      some (f16 (if m.val = 0 then 128 else 256) ((n.val + 1) * 16)) := by
  fin_cases m <;> fin_cases n <;> rfl

-- Every Table 48 dense group-1 i8 N at M = 128: 8 to 32 by 8, then 48 to 256 by 16.
example (n : Fin 32) :
    (decode .one false .i8 (8 * 2 ^ 24 + (n.val + 1) * 2 ^ 17 + 0x4a0)).isSome =
      (n.val < 4 || n.val % 2 = 1 && 4 < n.val) := by
  fin_cases n <;> rfl

-- Negation and transposition are retained independently, not discarded.
example : decode .two false .f16 0x10402010 = some { f16 256 256 with negateA := true } := rfl
example : decode .two false .f16 0x10404010 = some { f16 256 256 with negateB := true } := rfl
example : decode .two false .f16 0x10408010 = some { f16 256 256 with transposeA := true } := rfl
example : decode .two false .f16 0x10410010 = some { f16 256 256 with transposeB := true } := rfl

-- The sparsity selector (bits 0–1) has no effect; the sparse flag (bit 2) is not represented.
example : decode .two false .f16 0x10400013 = some (f16 256 256) := rfl
example : decode .two false .f16 0x10400014 = none := rfl
example : decode .two false .f16 0x10400018 = none := rfl
-- Bit 3 selects saturation for kind::i8; it is rejected for kind::f16.
example : decode .one false .i8 (134349984 + 8) = some { i8 128 8 with kind :=
                                                                       .i8 true true true } := rfl
example : decode .two false .f16 (272629776 + 8) = none := rfl
example : decode .two false .f16 0x10400050 = none := rfl
example : decode .two false .f16 0x10c00010 = none := rfl
example : decode .two false .f16 0x30400010 = none := rfl
example : decode .two false .f16 0x50400010 = none := rfl
example : decode .two false .f16 0x110400010 = none := rfl

-- Illegal shapes/types, and mixed input formats outside the represented scope.
example : decode .two false .f16 0x04400010 = none := rfl
example : decode .two false .f16 0x10020010 = none := rfl
example : decode .two false .f16 0x10440010 = none := rfl
example : decode .two false .f16 0x10400020 = none := rfl
example : decode .two false .f16 0x10400480 = none := rfl
example : decode .two false .f16 0x10400090 = none := rfl

-- Decoding keeps the instruction's group and gives a valid descriptor.
example {x : Nat} {d : Descriptor} (h : decode .one false .i8 x = some d) : d.group = .one ∧
    Valid d :=
  ⟨decode_group h, decode_valid h⟩

end PTX.Tests.TcMmaDescriptor
