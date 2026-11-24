-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Pointer

@[expose] public section

/-! # `selp` of two immediates on a predicate fact

A proof tool. The evaluation of a segment stops at a `selp` whose predicate is a symbolic
`Bool` (a bit of the thread index, say). `Seg.selp_imm` is that one step as a piece of a
segment chain: the destination holds the immediate the predicate selects, as an `if` on the
predicate, which the normal form's `split_ifs` handles in later pieces. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- One `selp.b32 d, a, b, p` with immediates `a`, `b` and the predicate fact `(p, c)`. -/
theorem Seg.selp_imm {pc d p : Nat} {a b : Int} {c : Bool} {ik : IType} {F : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.selp, .int ik 32, false, [some d], [.imm a, .imm b, .reg p]⟩⟩)
    (hp : (p, Value.pred c) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.selp, .int ik 32, false, [some d],
        [.imm a, .imm b, .reg p]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (pc + 1)
      ((d, .bits 32 (truncBits 32 (BitVec.ofInt 64 (if c then a else b)))) :: F) := by
  intro t h
  refine ⟨_, ?_, At.set h hd⟩
  have hr := holds_mem h.2.2.2.2 hp
  cases c <;>
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, Op.varyingSregs,
    Opnd.varying?, List.filterMap, hA.exec, execLocalRule_of_none (hL t h.1),
    execLocal_selp (i := ⟨.selp, .int ik 32, false, [some d], [.imm a, .imm b, .reg p]⟩) rfl,
    execMove, DType.width, readReg, hr, readValue, readBits, Value.bytes, bind, Except.bind, pure,
    Except.pure]

/-- `Seg.selp_imm` with the selected value restated as `v`. -/
theorem Seg.selp_imm_eq {pc d p : Nat} {a b : Int} {c : Bool} {ik : IType} {F : List (Nat × Value)}
    {v : Value} (hc : K.code[pc]? =
      some ⟨none, .int ⟨.selp, .int ik 32, false, [some d], [.imm a, .imm b, .reg p]⟩⟩)
    (hp : (p, Value.pred c) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hv : Value.bits 32 (truncBits 32 (BitVec.ofInt 64 (if c then a else b))) = v)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.selp, .int ik 32, false, [some d],
        [.imm a, .imm b, .reg p]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (pc + 1) ((d, v) :: F) :=
  hv ▸ Seg.selp_imm hc hp hd hL hA
