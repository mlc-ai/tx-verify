-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.BranchU

@[expose] public section

/-! # A branch on a predicate the facts do not state

`SegU.branch_join`: a guarded branch on a predicate register whose value the control facts do
not name (a data predicate) is crossed when both of its sides reach the same endpoint with the
same facts. A register that does not hold a predicate faults the guard, and the thread is dead. -/

namespace PTX.Flow.SegU
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem branch_join {pc p target c : Nat} {uni : Bool} {F G : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hT : SegU K A L g target F c G) (hN : SegU K A L g (pc + 1) F c G) :
    SegU K A L g pc F c G := by
  intro t ht
  obtain ⟨hP, hS0, hAc, hFl, hR⟩ := ht
  have hc' : K.code[t.pc]? = some ⟨some (p, false), .bra target uni⟩ := hP ▸ hc
  cases hp : t.regs p with
  | none =>
    exact .inr (Machine.dead_of_ub (f := .uninitialized)
      (by simp [out, hFl, hc', guardHolds, readReg, hp, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw]))
  | some v =>
    cases v with
    | pred b =>
      have h' : At t pc ((p, .pred b) :: F) := ⟨hP, hS0, hAc, hFl, hp, hR⟩
      cases b
      · exact SegU.comp (SegU.branch false hc hL hA) hN t h'
      · exact SegU.comp (SegU.branch true hc hL hA) hT t h'
    | _ =>
      exact .inr (Machine.dead_of_ub (f := .typeMismatch)
        (by simp [out, hFl, hc', guardHolds, readReg, hp, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw, Except.pure, pure]))

end PTX.Flow.SegU
