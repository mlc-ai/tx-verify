-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Selp
public import Lemmas.Flow.Arith32
public import Lemmas.Flow.SegDead
public import Lemmas.Flow.Havoc

@[expose] public section

/-! # `div.u32` of two register facts

A proof tool. The core's `div` has no rule for a zero divisor (`intDiv`), so a segment that divides
by a register whose value the machine does not know to be nonzero cannot be evaluated by kernel
reduction. `Seg.div_u32` is the one-instruction piece under the divisor's nonzero test, and
`SegU.div_u32` the strict-free (UB-tolerant) piece: a zero divisor kills the thread. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

namespace Arith32

/-- `div.u32` of the 32-bit words `x` and `y`, as the core computes it for a nonzero `y`. -/
abbrev divu32 (x y : BitVec 64) : BitVec 64 :=
  intBits 32 ((intOf .u 32 (r32 x)).tdiv (intOf .u 32 (r32 y)))

end Arith32

open Arith32

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- One `div.u32 d, a, r` on two facts of 32-bit words, for a nonzero divisor. -/
theorem Seg.div_u32 {pc d a r : Nat} {x y : BitVec 64} {F : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩⟩)
    (ha : (a, Value.bits 32 x) ∈ F) (hr : (r, Value.bits 32 y) ∈ F)
    (hz : (r32 y).toNat % 4294967296 ≠ 0) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (pc + 1) ((d, .bits 32 (divu32 x y)) :: F) := by
  intro t h
  refine ⟨_, ?_, At.set h hd⟩
  have hx := holds_mem h.2.2.2.2 ha
  have hy := holds_mem h.2.2.2.2 hr
  have hz0 : ((truncBits 32 y).toNat : Int) % 4294967296 ≠ 0 := by
    intro h0; apply hz; unfold r32; omega
  have hiu : ∀ z : BitVec 64, intOf IType.u 32 z = ((z.toNat : Int) % 4294967296) := fun z => by
    simp only [intOf]; split <;> first | omega | simp_all
  have hnn : ∀ z : Nat, ¬ ((z : Int) % 4294967296 < 0) := fun z => by omega
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, Op.varyingSregs,
    Opnd.varying?, List.filterMap, hA.exec, execLocalRule_of_none (hL t h.1),
    execLocal_int (i := ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩) rfl,
    execInt, intResult, intDiv, readBits, readReg, hx, hy, hiu, hz0, hnn, bind, Except.bind, pure,
    Except.pure, DType.intLanes?, DType.width, divu32, r32]

/-- A segment from fewer facts: the start facts `F'` imply those `F` it starts from. -/
theorem SegU.weaken_start {a b : Nat} {F F' G : List (Nat × Value)}
    (h : SegU K A L g a F b G) (hF : ∀ R, Holds R F' → Holds R F) : SegU K A L g a F' b G :=
  fun t ht => h t (At.mono ht (hF _ ht.2.2.2.2))

/-- **A division by a register fact in a UB-tolerant segment**: a zero divisor kills the thread,
a nonzero one continues with the quotient as a fact. -/
theorem SegU.div_u32 {pc d a r b : Nat} {x y : BitVec 64} {F G : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩⟩)
    (ha : (a, Value.bits 32 x) ∈ F) (hr : (r, Value.bits 32 y) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc)
    (h : (r32 y).toNat % 4294967296 ≠ 0 →
      SegU K A L g (pc + 1) ((d, .bits 32 (divu32 x y)) :: F) b G) :
    SegU K A L g pc F b G := by
  by_cases hz : (r32 y).toNat % 4294967296 = 0
  · intro t ht
    refine .inr (dead_of_error (f := .noRule) (op := .int ⟨.div, .int .u 32, false, [some d],
      [.reg a, .reg r]⟩) (ht.1 ▸ hc) rfl ht.2.2.2.1 ?_)
    have hy := holds_mem ht.2.2.2.2 hr
    have hx := holds_mem ht.2.2.2.2 ha
    have hiu : ∀ z : BitVec 64, intOf IType.u 32 z = ((z.toNat : Int) % 4294967296) := fun z => by
      simp only [intOf]; split <;> first | omega | simp_all
    have hz0 : intOf IType.u 32 (truncBits 32 y) = 0 := by
      rw [hiu]; unfold r32 at hz; omega
    simp [hA.exec (ht.1), execLocalRule_of_none (hL t ht.1),
      execLocal_int (i := ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩) rfl,
      execInt, intResult, intDiv, readBits, readReg, hx, hy, hz0, bind, Except.bind, pure,
      Except.pure, DType.intLanes?, DType.width, throw, throwThe, MonadExceptOf.throw]
  · exact SegU.comp (SegU.of_seg (Seg.div_u32 hc ha hr hz hd hL hA)) (h hz)

end
end PTX.Flow
