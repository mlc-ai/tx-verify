-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Support.Geometry
public import Kernels.Fp16Gemm8192.Spec

@[expose] public section

/-! # The launch's cluster layout as the threads see it

Every thread lies in a CTA of the grid, and `mapa` to rank 0 gives the cluster leader's copy
of an address: the cluster of a CTA `c` is the pair `2 * (c / 2)`, `2 * (c / 2) + 1`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX

theorem cta_lt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) : g / L.block < L.grid := by
  unfold Launch.threads at hg
  rw [hpre.block] at hg ⊢
  omega

/-- The cluster of CTA `c` is the pair `c / 2`. -/
theorem clusterOfCta_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (c : Nat) :
    L.clusterOfCta c = c / 2 := by
  rw [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]

/-- The rank of CTA `c` in its cluster is its low bit. -/
theorem rankOfCta_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (c : Nat) :
    L.rankOfCta c = c % 2 := by
  rw [Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, hpre.cluster]

/-- Cluster `k` starts at CTA `2 * k`. -/
theorem clusterStart_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (k : Nat) :
    L.clusterStart k = k * 2 := by
  rw [Launch.oneDim_clusterStart hpre.oneDimLaunch.1, hpre.cluster]

/-- Every cluster has two CTAs. -/
theorem clusterSizeOf_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (c : Nat) : L.clusterSizeOf c = 2 := by
  rw [Launch.oneDim_clusterSizeOf hpre.oneDimLaunch.1, hpre.cluster]

/-- Rank `r < 2` of the cluster of CTA `c` is CTA `c / 2 * 2 + r`. -/
theorem peerCta_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) {c r : Nat}
    (hc : c < L.grid) (hr : r < 2) : L.peerCta c r = some (c / 2 * 2 + r) := by
  have hg := hpre.grid
  have hpeer : c / 2 * 2 + r < L.grid := by omega
  simp [Launch.peerCta, clusterStart_eq hpre, clusterOfCta_eq hpre, clusterSizeOf_eq hpre, hc, hr,
    hpeer]

/-- `mapa` to rank 0: the cluster leader's copy of the address. -/
theorem map_zero {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (a : Nat) :
    L.mapShared (g / L.block) 0 ⟨.shared, g / L.block, a⟩ =
      some ⟨.shared, 2 * ((g / L.block) / 2), a⟩ := by
  have hcta := cta_lt hpre hg
  have hdim := hpre.oneDimLaunch.1
  have hstart : L.clusterStart (L.clusterOfCta (g / L.block)) = 2 * ((g / L.block) / 2) := by
    rw [Launch.oneDim_clusterStart hdim, Launch.oneDim_clusterOfCta hdim, hpre.cluster,
      Nat.mul_comm]
  have hsize : 0 < L.clusterSizeOf (g / L.block) := by
    rw [Launch.oneDim_clusterSizeOf hdim, hpre.cluster]
    decide
  have hpeer : 2 * ((g / L.block) / 2) < L.grid := by
    rw [hpre.grid] at hcta ⊢
    omega
  simp [Launch.mapShared, Launch.peerCta, hcta, hsize, hpeer, hstart]

end PTX.Kernels.Fp16Gemm8192.Proof
