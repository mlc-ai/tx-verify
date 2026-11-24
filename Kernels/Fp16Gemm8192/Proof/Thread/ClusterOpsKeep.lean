-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterOps

@[expose] public section

/-! # The roles' steps keep or count the cluster operations

A role's step on an event that is no cluster operation keeps the count, and a cluster operation
counts one more (`cl_ops_role`, for `clOp_step` in `Thread/ClusterOpsStep.lean`); the consumer's
event that is no cluster operation is here (`clOp_keep_cons`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option hygiene false in
/-- One role's step on an event that is no cluster operation, for `clOp_step`: its next state
`d''` (from `nextOf`) keeps the count; `fl` unfolds the role's `next` (with hygiene off, the names
are those of the caller). -/
macro "cl_ops_keep " nextOf:ident " [" fl:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  obtain ⟨d'', hn', rfl⟩ := $nextOf hn
  change kernel.code[site.pc]? = some ins at hc
  cases site
  case exitArrive =>
    exfalso
    code_at hc
    subst hc
    simp [isCluster, hcl _ rfl] at ha
  case exitWait =>
    exfalso
    code_at hc
    subst hc
    simp [isCluster, hcl _ rfl] at ha
  all_goals simp only [$fl,*] at hn'
  all_goals clear hc hf hcl
  clc_sweep hn'
  all_goals simp only [ThreadD.clOps]))

set_option hygiene false in
/-- One role's cluster operation step, for `clOp_step`: an event that is no cluster operation
keeps the count (`cl_ops_keep`), and a cluster operation, at the role's exit arrival or wait,
counts one more. -/
macro "cl_ops_role " nextOf:ident " [" fl:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  cases ha : isCluster e
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    cl_ops_keep $nextOf [$fl,*]
  · simp only [↓reduceIte]
    have hat := (clOp_event hc hf ha).2
    obtain ⟨d'', hn', rfl⟩ := $nextOf hn
    simp only [ThreadD.AtCluster] at hat
    rcases hat with rfl | rfl
    all_goals simp only [$fl,*, Option.some.injEq] at hn'
    all_goals clc_sweep hn'
    all_goals simp [ThreadD.clOps]))

set_option maxHeartbeats 8000000 in
/-- The consumer's event that is no cluster operation keeps the count. -/
theorem clOp_keep_cons {c : Consumer.D} {d' : ThreadD} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[(code L g).pc (.inr (.cons c))]? = some ins)
    (hf : Fires ((code L g).pc (.inr (.cons c))) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next (.inr (.cons c)) e = some (some d')) (ha : isCluster e = false) :
    d'.clOps = ThreadD.clOps (.inr (.cons c)) := by
  have hcl : ∀ (cop : ClusterOp), ins.op = .cluster cop → e.kind = .cluster cop := by
    intro cop hop
    rw [hop] at hf
    simp only [eventTmpl, Fires] at hf
    rw [hf.1]
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  symm
  cl_ops_keep next_of_cons [Consumer.next]

end
end PTX.Kernels.Fp16Gemm8192.Proof
