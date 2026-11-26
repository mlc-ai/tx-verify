-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQOps
public import Lemmas.Flow.SegJump

@[expose] public section

/-! # An unconditional branch as a strict piece

`SegQ.jmp`: an unguarded `bra` is one step to its target that keeps every register, so the tags of
the target's table are those of the branch's (`tagsIn`). A failed poll returns to the poll this
way. -/

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **An unconditional branch under the tag invariant.** -/
theorem SegQ.jmp {qt : Nat → Env} {pc target : Nat} {uni : Bool} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .bra target uni⟩)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc) (hq : tagsIn (qt target) (qt pc) = true) :
    SegQ K A L g (QT qt) pc F target F := by
  intro t ht hQ
  have hr : run K A L g 1 t = some { t with pc := target } := by
    simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, pure, Except.pure, hA.exec,
      execLocalRule_of_none (hL t ht.1), execLocal, Op.rule, execBranch, Op.isLocal]
  refine ⟨{ t with pc := target }, run_rtg hr, ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, ?_⟩
  have hQ' : Typed (qt pc) t := by simpa [QT, ht.1] using hQ
  intro r tg h
  exact typed_of_tagsIn hq hQ' r tg h

end PTX.Flow.Havoc
