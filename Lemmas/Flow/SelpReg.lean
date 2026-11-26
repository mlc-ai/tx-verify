-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Selp
public import Lemmas.Flow.Arith32

@[expose] public section

/-! # `selp` of a register and an immediate on a predicate fact

`Seg.selp_ri` is `Seg.selp_imm` (`Lemmas/Flow/Selp.lean`) for a register `a` holding `.bits 32 x`
and an immediate: the evaluation of a segment stops at a `selp` whose predicate is a symbolic
`Bool`, and the destination holds `sel c x (i32 b)`. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Flow.Arith32

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- One `selp.b32 d, a, b, p` with the register `a` (holding `x`), the immediate `b` and the
predicate fact `(p, c)`. -/
theorem Seg.selp_ri {pc d a p : Nat} {x : BitVec 64} {b : Int} {c : Bool}
    {F : List (Nat × Value)}
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.selp, .int .b 32, false, [some d], [.reg a, .imm b, .reg p]⟩⟩)
    (ha : (a, Value.bits 32 x) ∈ F) (hp : (p, Value.pred c) ∈ F) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.selp, .int .b 32, false, [some d],
        [.reg a, .imm b, .reg p]⟩) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (pc + 1) ((d, .bits 32 (sel c x (i32 b))) :: F) := by
  intro t h
  refine ⟨_, ?_, At.set h hd⟩
  have hx := holds_mem h.2.2.2.2 ha
  have hr := holds_mem h.2.2.2.2 hp
  cases c <;>
  simp [run, tauStep, out, h.2.2.2.1, h.1, hc, guardHolds, Op.isLocal, Op.varyingSregs,
    Opnd.varying?, List.filterMap, hA.exec, execLocalRule_of_none (hL t h.1),
    execLocal_selp (i := ⟨.selp, .int .b 32, false, [some d], [.reg a, .imm b, .reg p]⟩) rfl,
    execMove, DType.width, readReg, hx, hr, readValue, readBits, Value.bytes, bind, Except.bind,
    pure, Except.pure, sel, i32]

end
end PTX.Flow
