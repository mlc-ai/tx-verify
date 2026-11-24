-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SegSym
public import Lemmas.Flow.FloatOutcome
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
public import Kernels.TmlFa4Fwd.Flow.Code
public import Kernels.TmlFa4Fwd.Flow.Sites

/-! # Conditional `selp` values and faulting floating steps in `seg_sym`

Checked on the tml-fa4 softmax warps' masked maximum (PTX pcs 3872 to 4405): with the role's
opt-in `sym_selp_value`, each floating `selp` of a score or `-∞` on a mask bit writes the
conditional value instead of splitting the walk; the `max.f32` steps read such values as the
conditional of their readings and write `erealValue .f32` of the maximum; a pack of two
conditional values, the packed `fma` that reads it and the unpack of its result into two registers
are taken on each side of the conditions (the `-∞` sides by the exact rule on an infinity, the
moves by their step evaluated through `Seg.writes`); so are the exponent's `ex2.approx` (Core's
`+0` on `-∞`) and the probability packs. A floating step that no assumption takes and
Core has no rule for (an opaque NaN operand of `add.f32`) proves `DeadFrom` through the kernel's
`sym_fault`. -/

namespace PTX.Tests.SelpValue
open PTX PTX.Proof PTX.Flow PTX.Kernels.TmlFa4Fwd

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option seg_sym.decideHeartbeats 40000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

scoped macro_rules | `(tactic| sym_selp_value) => `(tactic| skip)

/-- The first two selects of the mask's first word (pcs 3872 to 3884). -/
example (L : Launch) (g : Nat) (m : BitVec 64) (x y : Nat → ℝ) :
    ∃ n, Seg kernel Assumptions.all L g n 3872
    ((3235, .bits 32 m) ::
     (7897, .pair (.float .f32 (x 0)) (.float .f32 (y 0))) ::
     (7899, .pair (.float .f32 (x 1)) (.float .f32 (y 1))) :: [])
    3884 [] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

/-- The first step of the fold, on two conditional elements: the maximum of their readings. -/
example (L : Launch) (g : Nat) (c : Nat → Bool) (x : Nat → ℝ) :
    ∃ n, Seg kernel Assumptions.all L g n 4329
    ((3240, if c 0 = true then .float .f32 (x 0) else .bits 32 (BitVec.ofNat 64 4286578688)) ::
     (3242, if c 1 = true then .float .f32 (x 1) else .bits 32 (BitVec.ofNat 64 4286578688)) ::
     [])
    4330 [(3620, Assumption.erealValue .f32 (max (if c 0 = true then ((x 0 : ℝ) : EReal) else ⊥)
      (if c 1 = true then ((x 1 : ℝ) : EReal) else ⊥)))] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

/-- The comparison of the fold's value with `-∞` and the `selp` of it or zero (pcs 4395 to
4397): a `selp` between a written value and a constant. -/
example (L : Launch) (g : Nat) (c : Bool) (z : ℝ) :
    ∃ n, Seg kernel Assumptions.all L g n 4395
    ((7256, Assumption.erealValue .f32 (max (if c = true then ((z : ℝ) : EReal) else ⊥) ⊥)) ::
     [])
    4397 [] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

/-- The packs, the first packed `fma` of the exponent and the unpack of its result into two
registers (pcs 4400 to 4405). -/
example (L : Launch) (g : Nat) (c : Nat → Bool) (x : Nat → ℝ) (s mn : ℝ) (hs : 0 < s) :
    ∃ n, Seg kernel Assumptions.all L g n 4400
    ((3686, .float .f32 mn) :: (7132, .float .f32 s) ::
     (3240, if c 0 = true then .float .f32 (x 0) else .bits 32 (BitVec.ofNat 64 4286578688)) ::
     (3242, if c 1 = true then .float .f32 (x 1) else .bits 32 (BitVec.ofNat 64 4286578688)) ::
     [])
    4405 [] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

/-- The exponent `ex2.approx` of a conditional value (pc 4594): the approximation's rule on the
real side, Core's table on the `-∞` side (`+0`). -/
example (L : Launch) (g : Nat) (c : Nat → Bool) (y : Nat → ℝ) :
    ∃ n, Seg kernel Assumptions.all L g n 4594
    ((3687, if c 0 = true then .float .f32 (y 0) else Assumption.erealValue .f32 ⊥) :: [])
    4595 [] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

/-- The probability pack `cvt.rn.bf16x2.f32` of two conditional values (pc 4626): the
conversion rule on each side. -/
example (L : Launch) (g : Nat) (c : Nat → Bool) (z : Nat → ℝ) :
    ∃ n, Seg kernel Assumptions.all L g n 4626
    ((1234, if c 3 = true then .float .f32 (z 3) else .float .f32 0) ::
     (1233, if c 2 = true then .float .f32 (z 2) else .float .f32 0) :: [])
    4627 [] := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

set_option hygiene false in
scoped macro_rules | `(tactic| sym_fault) => `(tactic| (
  intro R cf hR
  have h1 : R 3952 = some (.nan .f32) := holds_mem hR (by fact_mem)
  rw [Assumption.SegFreePc.exec (pc := 5005) (by sym_seg_free) rfl]
  have h2 : R 3953 = some (.float .f32 y) := holds_mem hR (by fact_mem)
  simp only [execLocalRule, Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
    List.cons_append, List.nil_append, List.findSome?_cons]
  simp [Assumptions.idealArith, Assumptions.approx, Assumptions.lg2, Assumptions.bf16Convert,
    Assumptions.swExp2, Assumptions.pollAgree, Assumptions.commitOrder, Assumptions.tcLdDataflow,
    Assumptions.delayedTmem, Assumptions.inputReadOnly, Assumption.idealReal,
    Assumption.approxExact, Assumption.execIdealFloat, Assumption.readERealOpnd, readReg, h1, h2,
    Assumption.readEReal, classify, Assumption.bindRead, Assumption.FloatForm.ofOp,
    Assumption.ApproxForm.ofOp, Assumptions.arithScope, Assumption.readEReal.ofDatum, pure,
    Except.pure, Assumptions.lg2Operands, Assumptions.biasWidenOperands,
    Assumptions.probPackOperands,
    Option.bind, Assumption.segmentExact, Assumption.pollAgreeAt, Assumption.commitOrderAt,
    Assumption.tcLdDataflowAt, Op.rule, FloatInstr.rule, FloatInstr.lane, floatLane, bind,
    Except.bind, readBits, FloatInstr.ieee]
  obtain ⟨e, he⟩ := coreFloat_add_error (fz := false) (.nan .f32) (.float .f32 y)
  exact ⟨e, by rw [execLocal_add_core (fz := false) (OpndIs.reg h1) (OpndIs.reg h2), he]; rfl⟩))

/-- An opaque NaN operand of `add.f32` (pc 5005) kills the thread. -/
example (L : Launch) (g : Nat) (y : ℝ) :
    DeadFrom kernel Assumptions.all L g 5005
      ((3952, .nan .f32) :: (3953, .float .f32 y) :: []) := by
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

end PTX.Tests.SelpValue
