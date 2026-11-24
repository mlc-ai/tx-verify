-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutFacts
public import Kernels.Fp16Gemm8192.Proof.Thread.ClusterDefs

@[expose] public section

/-! # Each thread's cluster barrier operations

Every thread makes four cluster barrier operations: the prologue's arrival and wait and the exit's
(decided on the code). A step counts them (`clOp_step`): a cluster operation is the state's count's
operation (`clOp_event`), at a cluster site, and every other event keeps the count. The run
invariant is `ClInv` (`Thread/ClusterCount.lean`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Whether an instruction is a cluster barrier operation. -/
def clOpOp : Op → Bool
  | .cluster _ => true
  | _ => false

/-- The kernel's cluster barrier operations are the prologue's and the exit's arrival and wait
(decided on the code). -/
theorem kernel_clOp_pcs : OpPcs kernel.code clOpOp
    [Flow.clusterArrive_0, Flow.clusterWait_0, Flow.clusterArrive_1, Flow.clusterWait_1] = true :=
  OpPcsFast.opPcs (by decide +kernel)

/-- A cluster barrier operation fires at one of the four cluster sites. -/
theorem clOp_site {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) (h : isCluster e = true) :
    (code L g).pc d = Flow.clusterArrive_0 ∨ (code L g).pc d = Flow.clusterWait_0 ∨
      (code L g).pc d = Flow.clusterArrive_1 ∨ (code L g).pc d = Flow.clusterWait_1 := by
  unfold isCluster at h
  split at h
  · rename_i cop hk
    have hop := fires_cluster_op hf hk
    have hpc := OpPcs.mem kernel_clOp_pcs hc (by rw [hop]; rfl)
    simpa using hpc
  · cases h

/-- An element of an array none of whose elements, nor the default, is a cluster site, is no
cluster site. -/
theorem getD_not_cluster {A : Array Nat} {j : Nat}
    (hA : ∀ x ∈ A.toList, ¬ (x = Flow.clusterArrive_0 ∨ x = Flow.clusterWait_0 ∨
      x = Flow.clusterArrive_1 ∨ x = Flow.clusterWait_1))
    (h : A.getD j 0 = Flow.clusterArrive_0 ∨ A.getD j 0 = Flow.clusterWait_0 ∨
      A.getD j 0 = Flow.clusterArrive_1 ∨ A.getD j 0 = Flow.clusterWait_1) : False := by
  unfold Array.getD at h
  split at h
  · exact hA _ (Array.getElem_mem_toList _) h
  · revert h
    decide

/-- At a cluster site, the state's count of cluster operations names that site. -/
theorem clEvent_pc {d : ThreadD}
    (hp : (code L g).pc d = Flow.clusterArrive_0 ∨ (code L g).pc d = Flow.clusterWait_0 ∨
      (code L g).pc d = Flow.clusterArrive_1 ∨ (code L g).pc d = Flow.clusterWait_1) :
    (code L g).pc d = (clEvent d.clOps).pc ∧ d.AtCluster := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals change site.pc = _ ∨ site.pc = _ ∨ site.pc = _ ∨ site.pc = _ at hp
  all_goals (cases site <;> first
    | (exact ⟨rfl, by simp [ThreadD.AtCluster]⟩)
    | (exfalso; revert hp; decide)
    | (exfalso
       simp only [Prologue.Site.pc, Mma.Site.pc, Consumer.Site.pc] at hp
       exact getD_not_cluster (by decide) hp)
    | (exfalso; clear * - hp; revert hp; decide +revert))

/-- A cluster barrier operation is the state's count's operation. -/
theorem clOp_event {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) (h : isCluster e = true) :
    e = clEvent d.clOps ∧ d.AtCluster := by
  obtain ⟨cop, hk⟩ : ∃ cop, e.kind = .cluster cop := by
    unfold isCluster at h
    split at h
    · exact ⟨_, ‹_›⟩
    · cases h
  have hop := fires_cluster_op hf hk
  have he : e = ⟨(code L g).pc d, .cluster cop⟩ := by
    rw [hop] at hf
    simp only [eventTmpl, Fires] at hf
    exact hf.1
  obtain ⟨hpc, hat⟩ := clEvent_pc (clOp_site hc hf h)
  refine ⟨?_, hat⟩
  rw [hpc] at hc he
  rw [he]
  generalize d.clOps = n at hc ⊢
  rcases n with _ | _ | _ | n
  · rw [show (clEvent 0).pc = Flow.clusterArrive_0 from rfl, Flow.code_clusterArrive_0] at hc
    cases hc
    simp only [Op.cluster.injEq] at hop
    subst hop
    rfl
  · rw [show (clEvent 1).pc = Flow.clusterWait_0 from rfl, Flow.code_clusterWait_0] at hc
    cases hc
    simp only [Op.cluster.injEq] at hop
    subst hop
    rfl
  · rw [show (clEvent 2).pc = Flow.clusterArrive_1 from rfl, Flow.code_clusterArrive_1] at hc
    cases hc
    simp only [Op.cluster.injEq] at hop
    subst hop
    rfl
  · rw [show (clEvent (n + 3)).pc = Flow.clusterWait_1 from rfl, Flow.code_clusterWait_1] at hc
    cases hc
    simp only [Op.cluster.injEq] at hop
    subst hop
    rfl

/-- The consumer's cluster operation counts one more. -/
theorem clOp_fire_cons {c : Consumer.D} {d' : ThreadD} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[(code L g).pc (.inr (.cons c))]? = some ins)
    (hf : Fires ((code L g).pc (.inr (.cons c))) (eventTmpl Prod L g t ins.op) e o)
    (hn : (code L g).next (.inr (.cons c)) e = some (some d')) (ha : isCluster e = true) :
    d'.clOps = ThreadD.clOps (.inr (.cons c)) + 1 := by
  have hat := (clOp_event hc hf ha).2
  obtain ⟨d'', hn', rfl⟩ := next_of_cons hn
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  simp only [ThreadD.AtCluster] at hat
  rcases hat with rfl | rfl
  all_goals simp only [Consumer.next, Option.some.injEq] at hn'
  all_goals clc_sweep hn'
  all_goals simp [ThreadD.clOps]

end
end PTX.Kernels.Fp16Gemm8192.Proof
