-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SegSym

@[expose] public section

/-! # One-step segment pieces: a skipped guard, a negated branch, `brx.idx`

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/SegPieces.lean`, whose
source is the old tree's `WorkerBase`). A guarded instruction whose guard fact is false is skipped
(`Seg.guardSkip`), a branch under the negation of a predicate fact goes to its target or falls
through (`Seg.braNot`), and an unguarded `brx.idx` on a register fact takes its table's entry
(`Seg.brxIdx`); every fact is kept. The names differ from the old Inkling `WorkerBase`'s
(`Seg.skip`, `Seg.bra_neg`, `Seg.brx` in `PTX.Flow`), so a module may import both. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A guarded instruction whose guard is false is skipped: one step, every fact kept. -/
theorem run_guardSkip {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc p : Nat} {neg : Bool} {op : Op} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨some (p, neg), op⟩) (pick : Bool) (h : At t pc F)
    (hp : t.regs p = some (.pred pick)) (hg : (pick != neg) = false) :
    ∃ u, run K A L g 1 t = some u ∧ At u (pc + 1) F := by
  refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
  simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, hg, bind, Except.bind,
    pure, Except.pure]

/-- A branch under the negation of a predicate fact keeps every register fact. -/
theorem run_braNot {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc target p : Nat} {F : List (Nat × Value)} {uni : Bool}
    (hc : K.code[pc]? = some ⟨some (p, true), .bra target uni⟩) (pick : Bool) (h : At t pc F)
    (hp : t.regs p = some (.pred pick))
    (hL : ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    ∃ u, run K A L g 1 t = some u ∧ At u (if pick then pc + 1 else target) F := by
  cases pick with
  | true =>
    exact run_guardSkip hc true h hp rfl
  | false =>
    refine ⟨{t with pc := target}, ?_, rfl, h.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind, pure,
      Except.pure, hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, execBranch, Op.isLocal]

/-- An unguarded `brx.idx` on a register holding a 32-bit word takes the entry of its table at
the word's index; every register fact is kept. -/
theorem run_brxIdx {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {pc r target k : Nat} {targets : List Nat} {uni : Bool} {F : List (Nat × Value)}
    {x : BitVec 64}
    (hc : K.code[pc]? = some ⟨none, .brx (.reg r) targets uni⟩) (h : At t pc F)
    (hp : t.regs r = some (.bits 32 x)) (hk : (truncBits 32 x).toNat = k)
    (ht : targets[k]? = some target)
    (hL : ∀ a ∈ A, a.localRule L g t (.brx (.reg r) targets uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    ∃ u, run K A L g 1 t = some u ∧ At u target F := by
  refine ⟨{t with pc := target}, ?_, rfl, h.2⟩
  simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind, pure,
    Except.pure, hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, execBranch, Op.isLocal,
    readBits, hk, ht]

namespace Seg
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A guarded instruction whose guard fact is false, as a one-step piece. -/
theorem guardSkip {pc p : Nat} {neg pick : Bool} {op : Op} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨some (p, neg), op⟩) (hp : (p, Value.pred pick) ∈ F)
    (hg : (pick != neg) = false) : Seg K A L g 1 pc F (pc + 1) F :=
  fun _ h => run_guardSkip hc pick h (holds_mem h.2.2.2.2 hp) hg

/-- A branch under the negation of a predicate fact, as a one-step piece. -/
theorem braNot {pc target p : Nat} {uni pick : Bool} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨some (p, true), .bra target uni⟩)
    (hp : (p, Value.pred pick) ∈ F)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (if pick then pc + 1 else target) F :=
  fun t h => run_braNot hc pick h (holds_mem h.2.2.2.2 hp) (hL t h.1) hA

/-- An unguarded `brx.idx` on a register fact holding a 32-bit word, as a one-step piece. -/
theorem brxIdx {pc r target k : Nat} {targets : List Nat} {uni : Bool} {F : List (Nat × Value)}
    {x : BitVec 64} (hc : K.code[pc]? = some ⟨none, .brx (.reg r) targets uni⟩)
    (hp : (r, Value.bits 32 x) ∈ F) (hk : (truncBits 32 x).toNat = k)
    (ht : targets[k]? = some target)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.brx (.reg r) targets uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F target F :=
  fun t h => run_brxIdx hc h (holds_mem h.2.2.2.2 hp) hk ht (hL t h.1) hA

end Seg

end
end PTX.Flow
