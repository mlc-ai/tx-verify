-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.Cluster

@[expose] public section

/-! # Clusters of one CTA

In a launch whose clusters all have the shape `(1, 1, 1)` every CTA is a cluster of its own: its
cluster number is its CTA number, its rank is zero, and the CTA of rank zero of its cluster is
itself. These are instances of the `locate` reading (PROG-CLUSTER, EXT-CLUSTER-RANK) with a
cluster size of one, not new readings. -/

namespace PTX

noncomputable section

variable {L : Launch}

/-- With one-CTA clusters, the CTA at flat offset `c` after the first `k` clusters is in cluster
`k + c` with rank zero. -/
theorem Launch.locate_unit (hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩) (n k c : Nat)
    (hc : c < n) : L.locate n k c = (k + c, 0) := by
  induction n generalizing k c with
  | zero => exact absurd hc (Nat.not_lt_zero c)
  | succ n ih =>
    have hs' : (L.clusterPlaces k).shape.prod = 1 := by simp [hs k, Dim3.prod]
    simp only [Launch.locate, hs']
    split
    · rename_i hlt
      have hc0 : c = 0 := by omega
      subst hc0
      rfl
    · rename_i hge
      have hc' : c - 1 < n := by omega
      rw [ih (k := k + 1) (c := c - 1) hc']
      have hge1 : 1 ≤ c := by omega
      have : k + 1 + (c - 1) = k + c := by omega
      rw [this]

theorem Launch.clusterSizeAt_unit (hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩) (k : Nat) :
    L.clusterSizeAt k = 1 := by simp [Launch.clusterSizeAt, hs k, Dim3.prod]

theorem Launch.clusterStart_unit (hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩) (k : Nat) :
    L.clusterStart k = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Launch.clusterStart, ih, Launch.clusterSizeAt_unit hs k]

theorem Launch.clusterOfCta_unit (hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩) {cta : Nat}
    (hc : cta < L.nclusters) : L.clusterOfCta cta = cta := by
  simp only [Launch.clusterOfCta]
  rw [Launch.locate_unit hs L.nclusters 0 cta hc]
  omega

theorem Launch.rankOfCta_unit (hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩) {cta : Nat}
    (hc : cta < L.nclusters) : L.rankOfCta cta = 0 := by
  simp only [Launch.rankOfCta]
  rw [Launch.locate_unit hs L.nclusters 0 cta hc]

theorem Launch.clusterSizeOf_unit (hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩) (cta : Nat) :
    L.clusterSizeOf cta = 1 := by
  simp only [Launch.clusterSizeOf]
  exact Launch.clusterSizeAt_unit hs _

/-- A CTA of a one-CTA-cluster launch is the CTA of rank zero of its own cluster. -/
theorem Launch.peerCta_unit (hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩) {cta : Nat}
    (hc : cta < L.nclusters) (hg : cta < L.grid) : L.peerCta cta 0 = some cta := by
  simp only [Launch.peerCta, Launch.clusterOfCta_unit hs hc, Launch.clusterStart_unit hs,
    Launch.clusterSizeOf_unit hs, Nat.add_zero]
  simp [hg]

end
end PTX
