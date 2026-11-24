-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SegSym
public import Lemmas.Flow.Arith32

/-! # The role hooks of a walk, and `scmpi` as the code's `setp`

`sym_rule` (a rule applies under the facts at hand, its remaining condition being a premise the
role proves), `sym_decide_rw` (a branch's predicate matches a hypothesis only after the machine's
abbreviations are unfolded) and `sym_fault` are `macro_rules` hooks: they fail by default, with a
message naming the missing rule, and a role replaces them in its own namespace. Checked here: the
default failure, that a scoped rule is consumed where the hook is tried, and that
`DeadFrom.of_step`/`of_step_local_error` compose the walk's fault (one instruction) with a step the
walk cannot compute (`DeadFrom.of_seg` + `Seg.segStep`).

`scmpi_eq_setp` is the `rfl` form of a `setp` with an immediate: the walk recomputes the comparison
by Core's rule and writes `truncBits` out, so a machine's `scmpi` abbreviation and the walk's term
differ only by the expansion of `r32`/`i32` (a large immediate's `BitVec.ofInt` can outlast
`cheapDefEq`'s heartbeat limit). -/

namespace PTX.Tests.SymHooks
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

/-- The hooks fail by default, naming what a role has to supply. -/
example : True := by
  fail_if_success sym_rule
  fail_if_success sym_decide_rw
  fail_if_success sym_fault
  trivial

/- A role replaces a hook with `macro_rules` (in its own namespace, `scoped` where the modes
matter); here each role rule proves a goal the walk could not: the premise a rule leaves open, a
decision that only a rewrite of the machine's abbreviation gives, and the fault of a float step. -/
macro_rules
  | `(tactic| sym_rule) => `(tactic| (exact ⟨⟩))
  | `(tactic| sym_decide_rw) => `(tactic| (exact le_refl 5))
  | `(tactic| sym_fault) => `(tactic| (exact ⟨⟩))

/-- With the role's rules in place the hooks are consumed where the walk tries them. -/
example : True := by sym_rule

example : 5 ≤ 5 := by sym_decide_rw

example : True := by sym_fault

/-- The combination a `cvt` + `mul.bf16x2` sequence takes: a step whose value no rule gives, then
the fault of the instruction that consumes it (`pairValue = none` in the kernel's terms). -/
example {K : Kernel} {A : List Assumption} {L : Launch} {g s b : Nat} {op op' : Op}
    {F H : List (Nat × Value)}
    (hc : K.code[s]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hstep : ∀ R cf, Holds R F → ∃ t' : TState,
      execLocalA A L g ⟨s, R, cf, 0, [], none⟩ op = .ok t' ∧ t'.pc = b ∧ t'.sub = 0 ∧
        t'.acc = [] ∧ t'.fault = none ∧ Holds t'.regs H)
    (hc' : K.code[b]? = some ⟨none, op'⟩) (hl' : op'.isLocal = true)
    (hex : ∀ R cf, Holds R H → ∃ f, execLocalA A L g ⟨b, R, cf, 0, [], none⟩ op' = .error f) :
    DeadFrom K A L g s F :=
  DeadFrom.of_step_local_error hc hl hstep hc' hl' hex

/-- `scmpi` and the code's `setp` with an immediate are the same term by `rfl`. -/
example (x : BitVec 64) : scmpi .lt .s x 64
    = compare .lt .s 32 (truncBits 32 x) (truncBits 32 (BitVec.ofInt 64 64)) :=
  PTX.Flow.Arith32.scmpi_eq_setp .lt .s x 64

/-- Which is the comparison the walk computes, so a decision on the machine's abbreviation is the
walk's (`cheapDefEq` on the two terms is what can time out). -/
example (x : BitVec 64) : (scmpi .lt .s x 64 = true) = (compare .lt .s 32 (truncBits 32 x)
    (truncBits 32 (BitVec.ofInt 64 64)) = true) := by
  rw [PTX.Flow.Arith32.scmpi_eq_setp]

end PTX.Tests.SymHooks
