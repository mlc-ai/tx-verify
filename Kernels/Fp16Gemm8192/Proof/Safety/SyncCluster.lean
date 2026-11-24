-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The `barrier.cluster` clauses of `AlignedMismatch`, from the thread facts

The cluster barrier operations of a thread are its state's (`ThreadFacts.cl_ops`): the `n`-th
one is `clEvent n`, whichever thread it is. Two lanes' operations at equal ordinals are therefore
the same event, with the same source line and qualifiers. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A cluster barrier event is not undefined behaviour. -/
theorem cluster_not_ub {e : Event} (h : isCluster e = true) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  simp [isCluster] at h

/-- A state at a cluster barrier operation has made fewer than four of them. -/
theorem clOps_lt_of_atCluster {d : ThreadD} (h : d.AtCluster) : d.clOps < 4 := by
  rcases d with p | r
  · rcases h with h | h <;> simp [ThreadD.clOps, h]
  · rcases r with l | m | s | c <;> rcases h with h | h <;> simp [ThreadD.clOps, h]

/-- Lanes at equal ordinals of the cluster barrier operations perform the same operation. -/
theorem no_cluster_mismatch (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ¬ AlignedClass.cluster.Divergent L kernel X ∧ ¬ AlignedClass.cluster.Exited L kernel X := by
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  swap
  · obtain ⟨⟨g, i⟩, ⟨h, j⟩, k, pc, op, -, he, -, hk, ⟨⟨pcx, hx⟩, hle⟩⟩ :=
      (AlignedClass.exited_cluster_iff L).mp hd
    -- no thread exits short of a cluster barrier operation: each exits after all four
    have hg := Frame.lt_of_get hX he
    have hce : isCluster ⟨pc, .cluster op⟩ = true := rfl
    obtain ⟨d, hd⟩ := Frame.event_state ht.sound hX ht.tracked he (cluster_not_ub hce)
    obtain ⟨hn, hev⟩ := ht.cl_ops hg hd
    obtain ⟨-, hat⟩ := (hev _ he).1 hce
    have hlt : d.clOps < 4 := clOps_lt_of_atCluster hat
    have hk' : k = d.clOps := by rw [← hn]; exact hk.symm
    have hh := Frame.lt_of_get hX hx
    obtain ⟨d', hd'⟩ := Frame.event_state ht.sound hX ht.tracked hx nofun
    obtain ⟨hn', hev'⟩ := ht.cl_ops hh hd'
    have h4 := (hev' _ hx).2 rfl
    have : clOps ((X.tr h).take j) ≤ (X.tr h).countP isCluster :=
      (List.take_sublist _ _).countP_le
    dsimp only at hle
    omega
  obtain ⟨g, h, i, j, pc, pc', op, op', -, he, hf, hcount, -, hne⟩ :=
    (AlignedClass.divergent_cluster_iff L).mp hd
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX hf
  have hce : isCluster ⟨pc, .cluster op⟩ = true := rfl
  have hcf : isCluster ⟨pc', .cluster op'⟩ = true := rfl
  obtain ⟨d, hd⟩ := Frame.event_state ht.sound hX ht.tracked he (cluster_not_ub hce)
  obtain ⟨d', hd'⟩ := Frame.event_state ht.sound hX ht.tracked hf (cluster_not_ub hcf)
  obtain ⟨hn, hev⟩ := ht.cl_ops hg hd
  obtain ⟨hn', hev'⟩ := ht.cl_ops hh hd'
  obtain ⟨hceq, -⟩ := (hev _ he).1 hce
  obtain ⟨hceq', -⟩ := (hev' _ hf).1 hcf
  have hops : d.clOps = d'.clOps := by rw [← hn, ← hn']; exact hcount
  rw [hops] at hceq
  have hev2 : (⟨pc, .cluster op⟩ : Event) = ⟨pc', .cluster op'⟩ := hceq.trans hceq'.symm
  cases hev2
  exact hne.elim (fun h => h rfl) (fun h => h rfl)

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
