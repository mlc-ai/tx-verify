-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
import Lemmas.Cluster.Unit

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

public theorem iter_admitted {Q : Params} {L : Launch} {m : Mem0} {g : Nat}
    (hp : Pre Q L m) (hg : g < L.threads) :
    Q.numIters ((L.ctaidOf (g/L.block)).get .z) ((L.ctaidOf (g/L.block)).get .x) ≤ 2147483646 := by
  let c := g / L.block
  have hs : ∀ k, (L.clusterPlaces k).shape = ⟨1,1,1⟩ := by
    intro k
    rw [hp.clusterPlaces, hp.clusterNctaid]
    rfl
  have hc : c < L.nclusters := by
    rw [hp.nclusters]
    exact Nat.div_lt_of_lt_mul (by simpa [Launch.threads, Nat.mul_comm] using hg)
  have hz : (L.ctaidOf c).get .z = c % Q.b := by
    simp [Launch.ctaidOf, Launch.placeOf, Launch.clusterCtaidOf, Launch.clusterOfCta_unit hs hc,
      Launch.rankOfCta_unit hs hc, hp.clusterPlaces, hp.clusterNctaid, hp.gridShape,
      ClusterPlace.uniform, Dim3.coord, Dim3.get]
  have hseq := hp.seqRange (c % Q.b) (Nat.mod_lt _ hp.bPos)
  let s := (L.ctaidOf c).get .x
  change Q.numIters ((L.ctaidOf c).get .z) s ≤ _
  rw [hz]
  have hi : Q.numIters (c % Q.b) s < Q.blocks (c % Q.b) + 1 := by
    unfold Params.numIters
    rw [Nat.div_lt_iff_lt_mul hp.splitsPos, Nat.add_one_mul]
    have := Nat.le_mul_of_pos_right (Q.blocks (c % Q.b)) hp.splitsPos
    have := hp.splitsPos
    omega
  unfold Params.blocks at hi
  omega

public theorem iter_range {Q : Params} {L : Launch} {m : Mem0} {g : Nat}
    (hp : Pre Q L m) (hg : g < L.threads) :
    Q.numIters ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x) < 2^31 :=
  lt_of_le_of_lt (iter_admitted hp hg) (by decide)

end PTX.Kernels.InklingRelDecode.Proof.Lib
