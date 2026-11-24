-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-! # Static facts of a program, computed in Lean

A proof tool. Facts about the decoded program that a kernel declares (the intervals of its roles
and their exits, its sites, the absence of an instruction class in a role) are `Bool` folds over
`K.code`, evaluated by the kernel (`kernel_rfl`, about two seconds per whole-program fact on nine
thousand instructions). Nothing is generated and nothing is trusted.

* `closedFrom R X 0 code`: every instruction in the region `R` (half-open intervals) other than
  the declared exits `X` continues only inside `R`;
* `sitesFrom R 0 code`: the event instructions of `R`, as program counters (to compare with a
  role's site table);
* `classFreeFrom R p 0 code`: no instruction of `R` satisfies `p`.

The facts are about the code's control-flow graph; that a thread at a site of `R` fires its next
event in `R` or at a declared exit follows for a thread followed by a glued machine
(`Code.glue_sound`), so no soundness theorem for `closedFrom` is needed by the library (plan risk
R9). -/

namespace PTX.CodeCheck
open PTX

/-- The program counters at which control can continue after the instruction at `pc`. -/
def succPcs (pc : Nat) (ins : Instr) : List Nat :=
  match ins.op with
  | .bra target _ => if ins.guard.isSome then [target, pc + 1] else [target]
  | .brx _ targets _ => if ins.guard.isSome then (pc + 1) :: targets else targets
  | .ret | .exit | .trap => if ins.guard.isSome then [pc + 1] else []
  | _ => [pc + 1]

/-- `pc` lies in one of the half-open intervals of `R`. -/
def inRegion (R : List (Nat × Nat)) (pc : Nat) : Bool := R.any fun r => r.1 ≤ pc && pc < r.2

/-- Every instruction of the region other than the declared exits `X` continues in the region. -/
def closedFrom (R : List (Nat × Nat)) (X : List Nat) : Nat → List Instr → Bool
  | _, [] => true
  | pc, ins :: rest =>
    (!(inRegion R pc && !X.contains pc) || (succPcs pc ins).all (inRegion R)) &&
      closedFrom R X (pc + 1) rest

/-- The event instructions of a region, as program counters. -/
def sitesFrom (R : List (Nat × Nat)) : Nat → List Instr → List Nat
  | _, [] => []
  | pc, ins :: rest =>
    if inRegion R pc && !ins.op.isLocal then pc :: sitesFrom R (pc + 1) rest
    else sitesFrom R (pc + 1) rest

/-- No instruction of the region satisfies `p`. -/
def classFreeFrom (R : List (Nat × Nat)) (p : Instr → Bool) : Nat → List Instr → Bool
  | _, [] => true
  | pc, ins :: rest => !(inRegion R pc && p ins) && classFreeFrom R p (pc + 1) rest

/-- An instruction of a class-free region is not of the class. -/
theorem classFree_get {R : List (Nat × Nat)} {p : Instr → Bool} :
    ∀ {base : Nat} {code : List Instr}, classFreeFrom R p base code = true →
      ∀ {i : Nat} {ins : Instr}, code[i]? = some ins → inRegion R (base + i) = true →
        p ins = false
  | _, [], _, _, _, h, _ => by simp at h
  | base, ins0 :: rest, hc, i, ins, h, hr => by
    simp only [classFreeFrom, Bool.and_eq_true, Bool.not_eq_true'] at hc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [Nat.add_zero] at hr
      simpa [hr] using hc.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      exact classFree_get hc.2 h (by rwa [show base + 1 + i = base + (i + 1) by omega])

/-- An instruction of a closed region other than an exit continues in the region. -/
theorem closed_get {R : List (Nat × Nat)} {X : List Nat} :
    ∀ {base : Nat} {code : List Instr}, closedFrom R X base code = true →
      ∀ {i : Nat} {ins : Instr}, code[i]? = some ins → inRegion R (base + i) = true →
        X.contains (base + i) = false → ∀ q ∈ succPcs (base + i) ins, inRegion R q = true
  | _, [], _, _, _, h, _, _ => by simp at h
  | base, ins0 :: rest, hc, i, ins, h, hr, hx => by
    simp only [closedFrom, Bool.and_eq_true, Bool.or_eq_true] at hc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [Nat.add_zero] at hr hx
      rcases hc.1 with h1 | h1
      · rw [hr, hx] at h1; cases h1
      · intro q hq
        exact List.all_eq_true.mp h1 q hq
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have e : base + (i + 1) = base + 1 + i := by omega
      rw [e] at hr hx ⊢
      exact closed_get hc.2 h hr hx

end PTX.CodeCheck
