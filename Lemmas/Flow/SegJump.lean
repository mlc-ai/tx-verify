-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegChain
public import Lemmas.Flow.SegFree

@[expose] public section

/-! # An unconditional branch as a piece

A proof tool, generic over the kernel (promoted from tml-fa4's `Proof2/Softmax/StepsPw1.lean`):
`seg_jmp`, an unguarded `bra` as one step to its target that keeps every fact (a failed poll
returning to the poll, say), given that no assumption gives the branch a rule or takes a segment
at its position. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {L : Launch} {g : Nat}

/-- **An unconditional branch**: one step to the target, keeping every fact. -/
theorem seg_jmp {K : Kernel} {A : List Assumption} {pc target : Nat} {uni : Bool}
    {F : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, .bra target uni⟩)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc) : Seg K A L g 1 pc F target F := by
  intro t h
  refine ⟨{t with pc := target}, ?_, rfl, h.2⟩
  simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, pure, Except.pure, hA.exec,
    execLocalRule_of_none (hL t h.1), execLocal, Op.rule, execBranch, Op.isLocal]

end
end PTX.Flow
