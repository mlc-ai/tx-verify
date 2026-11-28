-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads

@[expose] public section

/-! # The bytes of a `.nc` read are inputs

`NcApart P l`: the global byte `l` lies neither in the output tensor nor in the LSE output (the
two buffers the kernel writes). `NcRead P m l` adds that `Pre` allocates it. The launch-word and
index reads of the kernel cover such bytes only: `Pre` places the arrays they read apart from the
two outputs. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- **The byte lies in neither output**: not in the output tensor, not in the LSE output. -/
def NcApart (P : Params) (l : Loc) : Prop :=
  ¬ (l.space = .global ∧ l.cta = 0 ∧ P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P) ∧
  ¬ (l.space = .global ∧ l.cta = 0 ∧ P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P)

/-- **What a `.nc` read covers**: allocated bytes of the inputs. -/
structure NcRead (P : Params) (m : Mem0) (l : Loc) : Prop where
  /-- `Pre` allocates the byte. -/
  alloc : m l ≠ none
  /-- It is a global byte. -/
  space : l.space = .global
  /-- It is no byte of the outputs. -/
  apart : NcApart P l

/-- A byte of a range apart from both outputs is no output byte. -/
theorem ncApart_of {P : Params} {lo n a : Nat}
    (ho : Apart n (tensorBytes P) lo P.outBase) (hl : Apart n (lseBytes P) lo P.lseBase)
    (h1 : lo ≤ a) (h2 : a < lo + n) : NcApart P ⟨.global, 0, a⟩ := by
  unfold Apart at ho hl
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only at h <;> omega

/-- The row `(y s_q + x) topk + j` lies below `b s_q topk`. -/
theorem row_lt {b sq tk x y j : Nat} (hx : x < sq) (hy : y < b) (hj : j < tk) :
    (y * sq + x) * tk + j < b * sq * tk := by
  have h1 : y * sq + x + 1 ≤ b * sq := by
    have : (y + 1) * sq ≤ b * sq := Nat.mul_le_mul_right _ hy
    nlinarith
  have h2 : (y * sq + x + 1) * tk ≤ b * sq * tk := Nat.mul_le_mul_right _ h1
  nlinarith

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
