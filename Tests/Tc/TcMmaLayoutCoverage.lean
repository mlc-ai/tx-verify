-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaResultLayout

/-! Whole-matrix checks of the D layouts (THREAD-TC-MMA-RESULT-LAYOUT): every row and column of a
small instance against its closed form, Layout F's half-datapath lanes and alignments, and the
output-lane mask lane by lane. -/
namespace PTX.Tests.TcMmaLayoutCoverage
open PTX.TcMma
noncomputable section

private def smem : TcShared.Descriptor := ⟨0, 0, 1024, 0, false, false, .b128⟩
private def spec (d : Descriptor) (lo hi : Nat) : OperandSpec := ⟨d, smem, smem, lo, hi, none, {}⟩
private def i8 : Kind := .i8 true true false

/-! ## Layout D (M = 128, cta_group::1): row `i` is lane `i`, column `j` is `base + j` -/

private def dD : Descriptor := ⟨.one, i8, 128, 8, false, false, false, false, false⟩
example : Valid dD := by decide
example : ∀ r < 128, ∀ c < 8, resultCell (spec dD 5 5) 40 r c = some ⟨5, r, 40 + c⟩ := by decide

/-! ## Layout F (M = 64, cta_group::1): row `i` is lane `field + i % 16 + 32 (i / 16)` -/

private def dF : Descriptor := ⟨.one, i8, 64, 8, false, false, false, false, false⟩
example : Valid dF ∧ halfDatapath dF = true ∧ resultColumns dF = 8 := by decide
example : ∀ r < 64, ∀ c < 8,
    resultCell (spec dF 2 2) 16 r c = some ⟨2, r % 16 + 32 * (r / 16), 16 + c⟩ := by decide
-- Lane field 16 shifts every row by 16 lanes: the two alignments use disjoint lanes.
example : ∀ r < 64, ∀ c < 8, resultCell (spec dF 2 2) (16 * 2 ^ 16) r c =
    some ⟨2, 16 + r % 16 + 32 * (r / 16), c⟩ := by decide
example : ∀ r < 64, ∀ r' < 64, r % 16 + 32 * (r / 16) ≠ 16 + r' % 16 + 32 * (r' / 16) := by
  decide
-- Other lane fields are not Layout F alignments.
example : ∀ f < 128, f ≠ 0 → f ≠ 16 → resultCell (spec dF 2 2) (f * 2 ^ 16) 0 0 = none := by
  decide
example : LaneAligned dF 16 ∧ ¬ LaneAligned dF 32 ∧ ¬ LaneAligned dD 16 := by decide
-- Rows past 64 and columns past N have no cell.
example : resultCell (spec dF 2 2) 0 64 0 = none ∧ resultCell (spec dF 2 2) 0 0 8 = none := by
  decide
-- An FP32 Layout F with N = 256 at column 256 reaches the last physical column.
private def dF256 : Descriptor := ⟨.one, .f16 .f16 .f32, 64, 256, false, false, false, false, false⟩
example : resultCell (spec dF256 0 0) 256 63 255 = some ⟨0, 111, 511⟩ := by decide
example : resultCell (spec dF256 0 0) 257 0 0 = none := by decide

/-! ## Layout A (M = 256, cta_group::2) and B (M = 128, cta_group::2) -/

private def f16 : Kind := .f16 .f16 .f32
private def dA : Descriptor := ⟨.two, f16, 256, 16, false, false, false, false, false⟩
private def dB : Descriptor := ⟨.two, f16, 128, 16, false, false, false, false, false⟩
example : Valid dA ∧ Valid dB := by decide
-- kind::i8 with cta_group::2 needs N ≥ 32 (Table 48).
example : ¬ Valid { dB with kind := i8 } ∧ Valid { dB with kind := i8, n := 32 } := by decide
example : ∀ r < 128, ∀ c < 16, resultCell (spec dA 6 7) 0 r c = some ⟨6, r, c⟩ := by decide
example : ∀ r < 128, ∀ c < 16, resultCell (spec dA 6 7) 0 (128 + r) c = some ⟨7, r, c⟩ := by
  decide
-- Layout B: 64 rows per CTA, N in two blocks of N/2 columns over lanes 0..63 and 64..127.
example : resultColumns dB = 8 := by decide
example : ∀ r < 128, ∀ c < 16, resultCell (spec dB 6 7) 0 r c =
    some ⟨if r < 64 then 6 else 7, r % 64 + 64 * (c / 8), c % 8⟩ := by decide

/-! ## Layouts E and G (`.ws`, M = 64 and 32) -/

private def dE : Descriptor := ⟨.one, i8, 64, 64, false, false, false, false, true⟩
private def dG : Descriptor := ⟨.one, i8, 32, 64, false, false, false, false, true⟩
example : ∀ r < 64, ∀ c < 64,
    resultCell (spec dE 1 1) 0 r c = some ⟨1, r + 64 * (c / 32), c % 32⟩ := by decide
example : ∀ r < 32, ∀ c < 64,
    resultCell (spec dG 1 1) 0 r c = some ⟨1, r + 32 * (c / 16), c % 16⟩ := by decide

/-! ## Output-lane masks: bit `l` of the group's lane numbering disables exactly lane `l` -/

private def bit (l : Nat) : List Nat :=
  (List.range 4).map fun w => if w = l / 32 then 2 ^ (l % 32) else 0
example : ∀ l < 128, (writeCell (spec dD 5 5) 0 (bit l) l 0).isSome = false ∧
    (writeCell (spec dD 5 5) 0 (bit l) ((l + 1) % 128) 0).isSome = true := by decide
example : ∀ r < 128, (writeCell (spec dD 5 5) 0 (bit 77) r 0).isSome = decide (r ≠ 77) := by
  decide
-- Layout F: masking lane 33 disables row 17 (lane 1 + 32), and no other row.
example : ∀ r < 64, (writeCell (spec dF 2 2) 0 (bit 33) r 0).isSome = decide (r ≠ 17) := by
  decide
-- Masks need exactly 4 × group-size words of 32 bits.
example : writeCell (spec dD 5 5) 0 [0, 0, 0] 0 0 = none ∧
    writeCell (spec dD 5 5) 0 [0, 0, 0, 2 ^ 32] 0 0 = none := by decide
-- cta_group::2 numbers the low CTA's lanes 0..127 and the high CTA's 128..255.
private def bit8 (l : Nat) : List Nat :=
  (List.range 8).map fun w => if w = l / 32 then 2 ^ (l % 32) else 0
example : ∀ r < 128, (writeCell (spec dA 6 7) 0 (bit8 130) r 0).isSome = true ∧
    (writeCell (spec dA 6 7) 0 (bit8 130) (128 + r) 0).isSome = decide (r ≠ 2) := by decide

end
end PTX.Tests.TcMmaLayoutCoverage
