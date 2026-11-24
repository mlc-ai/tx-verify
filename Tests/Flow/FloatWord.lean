-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SegSym
public import Lemmas.Flow.Fragment
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
public import Kernels.TmlFa4Fwd.Flow.Code
public import Kernels.TmlFa4Fwd.Flow.Sites

/-! # `seg_sym` on a word whose binary32 number a hypothesis gives

Checked on the tml-fa4 softmax warps' negation of the scale word (`neg.f32 %r170, %r6072`, PTX
pc 4398): the register holds the launch word `.bits 32 x`, Core's `neg` classifies it through its
pattern, and no assumption takes `neg`. With the hypothesis `f32Value x.toNat = some s` and
`0 < s` in context, `seg_sym` takes the step by `Seg.negWord`: the destination holds the payload
`-s`.

The same word is packed twice into the multiplier of the exponent's packed `fma`s (pc 4402,
`mov.b64 %rd738, {%r6072, %r6072}`; Core joins the two words into one 64-bit word). With the
hypothesis `classify .f32 (.bits 32 w) = .ok (.fin s)` for the launch word `w` (`truncBits 32`
of the parameter), the assumption-ruled `fma.rn.f32x2` at pcs 4403 and 4406 read the joined
word as the pair `(s, s)`. -/

namespace PTX.Tests.FloatWord
open PTX PTX.Proof PTX.Flow PTX.Kernels.TmlFa4Fwd

set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- No assumption of tml-fa4 gives the negation at pc 4398 a rule. -/
theorem neg_none {L : Launch} {g : Nat} :
    NoRuleAt Assumptions.all L g 4398
      (.float { op := .neg, ty := ⟨.f32, 1⟩, dsts := [some 1230], srcs := [.reg 7132] }) := by
  intro t _ a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

scoped macro_rules | `(tactic| sym_local_none) => `(tactic| exact neg_none)

/-- The negation of the scale word. -/
example (L : Launch) (g : Nat) (x : BitVec 64) (s : ℚ) (hx : f32Value x.toNat = some s)
    (hs : 0 < s) :
    ∃ n, Seg kernel Assumptions.all L g n 4398 ((7132, .bits 32 x) :: []) 4399
      [(1230, .float .f32 ((-s : ℚ) : ℝ))] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

/-- No assumption of tml-fa4 gives a move a rule. -/
theorem move_none {L : Launch} {g pc : Nat} (m : MoveInstr) :
    NoRuleAt Assumptions.all L g pc (.move m) := by
  intro t _ a ha
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

scoped macro_rules | `(tactic| sym_local_none) => `(tactic| exact move_none _)

/-- The scaled scores of the first four elements: the row maximum `m` times the negated scale,
the packs, two packed `fma`s whose multiplier is the scale word packed twice, and their unpacks
(pcs 4399 to 4407). -/
example (L : Launch) (g S : Nat) (s : ℚ) (m : ℝ) (x : Fin 4 → ℝ)
    (hw : classify .f32 (.bits 32 (truncBits 32 (BitVec.ofNat 64 S))) = .ok (.fin s)) :
    ∃ n, Seg kernel Assumptions.all L g n 4399
      ((7132, .bits 32 (truncBits 32 (BitVec.ofNat 64 S))) ::
       (1230, .float .f32 ((-s : ℚ) : ℝ)) :: (3685, .float .f32 m) ::
       (3240, .float .f32 (x 0)) :: (3242, .float .f32 (x 1)) ::
       (3246, .float .f32 (x 2)) :: (3248, .float .f32 (x 3)) :: [])
      4408 [] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

/-- An assumption-ruled `mul.f32` that reads a word directly (here register 1230 holds a launch
word instead of the negated scale): the rule step reads it as `s` (pc 4399). -/
example (L : Launch) (g S : Nat) (s : ℚ) (m : ℝ)
    (hw : classify .f32 (.bits 32 (truncBits 32 (BitVec.ofNat 64 S))) = .ok (.fin s)) :
    ∃ n, Seg kernel Assumptions.all L g n 4399
      ((1230, .bits 32 (truncBits 32 (BitVec.ofNat 64 S))) :: (3685, .float .f32 m) :: [])
      4400 [] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

/-- A `.bf16x2` word loaded from an unmasked and a masked bias element (stored as the payload and
as the bits of `-∞`) has the packed return kind, and so does a word of two masked elements. -/
example (x : ℝ) : (RetKind.packed .bf16).acceptsVal (.pair (.float .bf16 x) (.bits 16 0xFF80)) ∧
    (RetKind.packed .bf16).acceptsVal (.bits 32 0xFF80FF80) := by
  simp [RetKind.acceptsVal, packedVal, packedElem, FloatFmt.bytes]

end PTX.Tests.FloatWord
