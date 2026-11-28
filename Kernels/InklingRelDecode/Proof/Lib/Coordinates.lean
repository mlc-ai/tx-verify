-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
import Lemmas.Cluster.Unit

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- Coordinates in the kernel's grid of unit clusters, numbered with request fastest. -/
theorem coordinates {Q L m} (hp : Pre Q L m) {c : Nat} (hc : c<L.grid) :
    L.ctaidOf c = ⟨c/(kvHeads*Q.b),c/Q.b%kvHeads,c%Q.b⟩ := by
  have hs : ∀ k, (L.clusterPlaces k).shape = ⟨1,1,1⟩ := by
    intro k
    rw [hp.clusterPlaces,hp.clusterNctaid]
    rfl
  have hcn : c<L.nclusters := hp.nclusters ▸ hc
  simp only [Launch.ctaidOf,Launch.placeOf,Launch.clusterCtaidOf,Launch.clusterOfCta_unit hs hcn,
    Launch.rankOfCta_unit hs hcn,hp.clusterPlaces,hp.clusterNctaid,hp.gridShape,
    ClusterPlace.uniform,Dim3.coord]
  simp

theorem coordinate_bounds {Q L m g} (hp : Pre Q L m) (hg : g<L.threads) :
    let co := L.ctaidOf (g/L.block)
    co.get .x < Q.splits ∧ co.get .y < kvHeads ∧ co.get .z < Q.b := by
  have hc : g/L.block<L.grid := Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads,Nat.mul_comm] using hg)
  dsimp only
  rw [coordinates hp hc]
  refine ⟨Nat.div_lt_of_lt_mul ?_,Nat.mod_lt _ (by decide),Nat.mod_lt _ hp.bPos⟩
  simpa [hp.grid,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hc

end PTX.Kernels.InklingRelDecode.Proof.Lib
