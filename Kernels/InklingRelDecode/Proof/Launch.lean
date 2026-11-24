-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaIssue
public import Lemmas.Cluster.Unit

@[expose] public section

/-! # The launch facts the roles share

The kernel launches a grid of `(num_splits, 2, batch)` CTAs, each in a cluster of its own
(`Pre.gridShape`, `Pre.clusterNctaid`, `Pre.clusterPlaces`). Every CTA is therefore the CTA of
rank zero of its own cluster, which is what a `cta_group::1` Tensor Memory instruction needs
(`Mma.OneCta`), and what the exit and the deallocation take for granted. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The clusters of the kernel's launch are one CTA each. -/
theorem clusterPlaces_unit (hpre : Pre P L mem0) :
    ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩ := by
  intro k
  rw [hpre.clusterPlaces, hpre.clusterNctaid]
  rfl

/-- Every thread of the kernel's launch is in a CTA that is the only CTA of its cluster. -/
theorem oneCta (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) : Mma.OneCta L g := by
  have hblock : 0 < L.block := by rw [hpre.block]; omega
  have hgt : g / L.block < L.grid := by
    rw [Launch.threads] at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  have hcn : g / L.block < L.nclusters := by rw [hpre.nclusters]; exact hgt
  have hrank := Launch.rankOfCta_unit (clusterPlaces_unit hpre) hcn
  exact ⟨g / L.block, by rw [hrank]; exact Launch.peerCta_unit (clusterPlaces_unit hpre) hcn hgt⟩

end
end PTX.Kernels.InklingRelDecode.Proof
