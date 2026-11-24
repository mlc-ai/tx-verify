-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Protocol.ClusterLaneCount

@[expose] public section

/-! # The lanes of the cluster barrier, and `ClusterFault`

The cluster barrier object lets a lane arrive again without a wait, so the alternation of a lane's
records comes from the program. Each thread's `n`-th cluster operation is `clEvent n`
(`ThreadFacts.cl_ops`): arrivals at `n = 0, 2`, waits at `n = 1, 3` (`ops_alternate`). From the
program's alternation the library gives the lanes' (`ClusterLanes.alt_of_ops`): an arrival record
of a lane comes after an even number of the lane's records and a wait record after an odd number
(`cluster_alt`), and neither collective faults (`no_cluster_fault`,
`ClusterLanes.no_fault_of_ops`). This file sits at the top of the proof tree, outside the
layer order: the safety root and the progress layer both use it. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX ClusterBarrier ClusterLanes ClusterPhase

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A state at a cluster operation has made at most three. -/
theorem clOps_le_of_atCluster {d : ThreadD} (h : d.AtCluster) : d.clOps ≤ 3 := by
  rcases d with ⟨site, w⟩ | (⟨site, m, n, q, cp, r, x⟩ | ⟨site, w, q, fp, ap, cp, r, x⟩ |
      ⟨site, ap, cp, r, x⟩ | ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩)
  all_goals simp only [ThreadD.AtCluster] at h
  all_goals rcases h with rfl | rfl <;> simp [ThreadD.clOps]

/-- A thread's cluster operation at position `k` is every thread's operation of its count. -/
theorem cl_event (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g k pc : Nat}
    {op : ClusterOp} (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .cluster op⟩) :
    ((X.tr g).take k).countP isCluster ≤ 3 ∧
      (⟨pc, .cluster op⟩ : Event) = clEvent (((X.tr g).take k).countP isCluster) := by
  obtain ⟨d, hd⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨hn, hev⟩ := ht.cl_ops hg hd
  obtain ⟨heq, hat⟩ := (hev _ he).1 rfl
  change clOps _ ≤ 3 ∧ _ = clEvent (clOps _)
  rw [hn]
  exact ⟨clOps_le_of_atCluster hat, heq⟩

theorem clEvent_arrive_even {k pc : Nat} {rel al : Bool} (hk : k ≤ 3)
    (h : (⟨pc, .cluster (.arrive rel al)⟩ : Event) = clEvent k) : k % 2 = 0 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    first | rfl | simp [clEvent] at h

theorem clEvent_wait_odd {k pc : Nat} {al : Bool} (hk : k ≤ 3)
    (h : (⟨pc, .cluster (.wait al)⟩ : Event) = clEvent k) : k % 2 = 1 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    first | rfl | simp [clEvent] at h

/-- **The kernel's cluster operations alternate**: each thread's `n`-th operation is
`clEvent n`, an arrival for even `n` and a wait for odd `n`. -/
theorem ops_alternate (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    OpsAlternate X := by
  intro g k pc op he
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨h3, h4⟩ := cl_event hX ht hg he
  cases op with
  | arrive rel al => exact clEvent_arrive_even h3 h4
  | wait al => exact clEvent_wait_odd h3 h4

/-- **A lane's records alternate**: its arrival records come after an even number of its records
and its wait records after an odd number. -/
theorem cluster_alt (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c x : Nat}
    (hc : c < L.nclusters) (hx : x < L.block * L.clusterSizeAt c) : Alt x (X.clusters c) :=
  alt_of_ops hX.cluster (ClusterBlocking.of_consistent hX) hX.object (ops_alternate hX ht) hc hx

/-- **No cluster barrier collective of the kernel faults.** -/
theorem no_cluster_fault (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ¬ ClusterFault L X :=
  no_fault_of_ops hX.cluster (ClusterBlocking.of_consistent hX) hX.object (ops_alternate hX ht)

end

end PTX.Kernels.Fp16Gemm8192.Proof
