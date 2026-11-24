-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmEdge

@[expose] public section

/-! # The bias widening of the score stage (pcs 1303-1430)

After the wait for the S tile's load (pc 1298) and where the block has bias (`%p96` false), the
code widens the 64 `bf16` bias words to `f32` in 32 groups of four instructions (pc `1303 + 4 j`
for the packed word `%r(1486 - j)`, which holds the pair of bias words `2 (31 - j)` and
`2 (31 - j) + 1`): the unpack of the packed word into two half-word registers (`mov.b32 {lo, hi},
%r`), the conversions of the two halves (`cvt.f32.bf16`, the high half first) and the pack of the
two `f32` numbers into one 64-bit register (`mov.b64 %rd, {lo, hi}`).

This file gives the local steps of the group and the group as a piece between explicit facts: from
the packed word holding the pair of two `bf16` numbers `x`, `y` to the 64-bit register holding the
pair of the two `f32` numbers `x`, `y` (the widening of a `bf16` number is exact, read by
`Assumptions.bf16Exact`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

/-! ### The local steps -/

/-- The instruction `cvt.f32.bf16 d, a`. -/
def cvtW (d a : Nat) : CvtInstr :=
  ⟨.float .f32, .float .bf16, none, false, false, false, false, false, false, false, d, .same,
    [.reg a]⟩

/-! ### The group of four instructions between explicit facts -/

/-- The instruction at `pc` is `mov.b32 {a, b}, r` (an unpack of a 32-bit word). -/
def unpack32At (pc a b r : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .move m⟩ => m == ⟨.unpack, .int .b 32, [some a, some b], [.reg r]⟩
  | _ => false

theorem unpack32At_spec {pc a b r : Nat} (h : unpack32At pc a b r = true) :
    kernel.code[pc]? = some ⟨none, .move ⟨.unpack, .int .b 32, [some a, some b], [.reg r]⟩⟩ := by
  unfold unpack32At at h
  split at h
  · rename_i m hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

/-- The instruction at `pc` is `cvt.f32.bf16 d, a`. -/
def cvtWidenAt (pc d a : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .cvt c⟩ => c == cvtW d a
  | _ => false

theorem cvtWidenAt_spec {pc d a : Nat} (h : cvtWidenAt pc d a = true) :
    kernel.code[pc]? = some ⟨none, .cvt (cvtW d a)⟩ := by
  unfold cvtWidenAt at h
  split at h
  · rename_i c hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

/-- The 32 groups: the unpack of `%r(1486 - j)` into `%rs(216 + 2 j)` and `%rs(217 + 2 j)`, the two
conversions into `%r(485 + 2 j)` (high half) and `%r(486 + 2 j)` (low half) and the pack into
`%rd(327 + j)`. -/
theorem widen_code : ∀ j < 32, unpack32At (1303 + 4 * j) (397 + 2 * j) (398 + 2 * j) (1947 - j) =
      true ∧ cvtWidenAt (1304 + 4 * j) (946 + 2 * j) (398 + 2 * j) = true ∧
    cvtWidenAt (1305 + 4 * j) (947 + 2 * j) (397 + 2 * j) = true ∧
    packAt (1306 + 4 * j) (2275 + j) (947 + 2 * j) (946 + 2 * j) 64 = true := by
  decide +kernel

theorem emu_widen : ∀ j < 32, ∀ k < 4,
    Assumptions.emuSites.contains (1303 + 4 * j + k) = false := by
  decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
