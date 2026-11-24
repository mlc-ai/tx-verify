-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterOpsKeep

@[expose] public section

/-! # A step counts the cluster operations

The step of the cluster operation count (`clOp_step`), by role: the prologue's here, the roles' in
this file and the consumer's in `Thread/ClusterOps.lean`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- The loader's step counts the cluster operations. -/
theorem clOp_step_loader {x : Loader.D} {d' : ThreadD} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event}
    (hc : kernel.code[(code L g).pc (.inr (.loader x))]? = some ins)
    (hf : Fires ((code L g).pc (.inr (.loader x))) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next (.inr (.loader x)) e = some (some d'))
    (hq : clOps pre = ThreadD.clOps (.inr (.loader x))) :
    clOps (pre ++ [e]) = d'.clOps := by
  have hsnoc : clOps (pre ++ [e]) = clOps pre + (if isCluster e then 1 else 0) := by
    simp [clOps, List.countP_append]
  rw [hsnoc, hq]
  have hcl : ∀ (cop : ClusterOp), ins.op = .cluster cop → e.kind = .cluster cop := by
    intro cop hop
    rw [hop] at hf
    simp only [eventTmpl, Fires] at hf
    rw [hf.1]
  obtain ⟨site, m, n, q, cp, r, x⟩ := x
  cl_ops_role next_of_loader [Loader.next, Loader.endOfTrip]

set_option maxHeartbeats 8000000 in
/-- The MMA thread's step counts the cluster operations. -/
theorem clOp_step_mma {x : Mma.D} {d' : ThreadD} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event}
    (hc : kernel.code[(code L g).pc (.inr (.mma x))]? = some ins)
    (hf : Fires ((code L g).pc (.inr (.mma x))) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next (.inr (.mma x)) e = some (some d'))
    (hq : clOps pre = ThreadD.clOps (.inr (.mma x))) :
    clOps (pre ++ [e]) = d'.clOps := by
  have hsnoc : clOps (pre ++ [e]) = clOps pre + (if isCluster e then 1 else 0) := by
    simp [clOps, List.countP_append]
  rw [hsnoc, hq]
  have hcl : ∀ (cop : ClusterOp), ins.op = .cluster cop → e.kind = .cluster cop := by
    intro cop hop
    rw [hop] at hf
    simp only [eventTmpl, Fires] at hf
    rw [hf.1]
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := x
  cl_ops_role next_of_mma [Mma.next, Mma.endOfTrip]

set_option maxHeartbeats 8000000 in
/-- The scheduler's step counts the cluster operations. -/
theorem clOp_step_sched {x : Scheduler.D} {d' : ThreadD} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event}
    (hc : kernel.code[(code L g).pc (.inr (.sched x))]? = some ins)
    (hf : Fires ((code L g).pc (.inr (.sched x))) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next (.inr (.sched x)) e = some (some d'))
    (hq : clOps pre = ThreadD.clOps (.inr (.sched x))) :
    clOps (pre ++ [e]) = d'.clOps := by
  have hsnoc : clOps (pre ++ [e]) = clOps pre + (if isCluster e then 1 else 0) := by
    simp [clOps, List.countP_append]
  rw [hsnoc, hq]
  have hcl : ∀ (cop : ClusterOp), ins.op = .cluster cop → e.kind = .cluster cop := by
    intro cop hop
    rw [hop] at hf
    simp only [eventTmpl, Fires] at hf
    rw [hf.1]
  obtain ⟨site, ap, cp, r, x⟩ := x
  cl_ops_role next_of_sched [Scheduler.next, Scheduler.loopHead]

set_option maxHeartbeats 8000000 in
/-- **A step counts the cluster operations.** -/
theorem clOp_step {d d' : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next d e = some (some d')) (hq : clOps pre = d.clOps) :
    clOps (pre ++ [e]) = d'.clOps := by
  rcases d with ⟨site, w⟩ | (l | m | s | c)
  rotate_left
  · exact clOp_step_loader hc hf hn hq
  · exact clOp_step_mma hc hf hn hq
  · exact clOp_step_sched hc hf hn hq
  · have hsnoc : clOps (pre ++ [e]) = clOps pre + (if isCluster e then 1 else 0) := by
      simp [clOps, List.countP_append]
    rw [hsnoc, hq]
    cases ha : isCluster e
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact (clOp_keep_cons hc hf hn ha).symm
    · simp only [↓reduceIte]
      exact (clOp_fire_cons hc hf hn ha).symm
  have hA := clOp_site hc hf
  have hsnoc : clOps (pre ++ [e]) = clOps pre + (if isCluster e then 1 else 0) := by
    simp [clOps, List.countP_append]
  rw [hsnoc, hq]
  have hcl : ∀ (cop : ClusterOp), ins.op = .cluster cop → e.kind = .cluster cop := by
    intro cop hop
    rw [hop] at hf
    simp only [eventTmpl, Fires] at hf
    rw [hf.1]
  change Prologue.next L g ⟨site, w⟩ e = some (some d') at hn
  change kernel.code[site.pc]? = some ins at hc
  change isCluster e = true → (site.pc = Flow.clusterArrive_0 ∨ site.pc = Flow.clusterWait_0 ∨
    site.pc = Flow.clusterArrive_1 ∨ site.pc = Flow.clusterWait_1) at hA
  cases ha : isCluster e
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    cases site
    case arrive =>
      exfalso
      code_at hc
      subst hc
      simp [isCluster, hcl _ rfl] at ha
    case wait =>
      exfalso
      code_at hc
      subst hc
      simp [isCluster, hcl _ rfl] at ha
    all_goals simp only [Prologue.next, Prologue.afterInits, Prologue.afterElect,
      Prologue.schedStart, Prologue.mmaStart, Prologue.loaderStart, Prologue.loaderIdle] at hn
    all_goals clear hc hf hcl hA
    clc_sweep hn
    all_goals simp only [ThreadD.clOps] at hq ⊢
  · have hp := hA ha
    cases site
    case arrive =>
      simp only [Prologue.next, Option.some.injEq] at hn
      subst hn
      simp [ThreadD.clOps] at hq ⊢
    case wait =>
      simp only [Prologue.next, Prologue.consStart] at hn
      clc_sweep hn
      all_goals simp [ThreadD.clOps] at hq ⊢
    all_goals exfalso
    all_goals clear * - hp
    all_goals revert hp
    all_goals simp only [Prologue.Site.pc]
    all_goals decide +revert

end
end PTX.Kernels.Fp16Gemm8192.Proof
