-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Core.Source.Decode
public import Core.Sync.Cluster

namespace PTX.Tests.Cluster
noncomputable section

private def launch : Launch := {
  grid := 1024, block := 384, params := fun _ => none, clusterSize := 2
}
private def env : Decode.Env := { classes := [⟨"r".toList, 1, 32⟩], labels := [], params := [] }

example : Decode.op env "mov.u32" [.register "r0", .register "%cluster_ctaid.x"] =
    .ok (.move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.clusterCtaid, some .x⟩]⟩) := rfl
example : SReg.ofName? "%cluster_ctarank" = some ⟨.clusterCtarank, none⟩ := rfl
example : SReg.ofName? "%cluster_nctarank" = some ⟨.clusterNctarank, none⟩ := rfl
example : SReg.ofName? "%cluster_ctaid.y" = some ⟨.clusterCtaid, some .y⟩ := rfl
-- The launch is one-dimensional, so the `.y` component is 0 (THREAD-SREG).
example : launch.OneDim := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
example : sregValue launch 0 ⟨.clusterCtaid, some .y⟩ = some 0 := rfl
example : readBits launch 0 {} 32 (.sreg ⟨.clusterCtaid, some .y⟩) = .ok 0 := rfl

example : sregValue launch (13 * 384) ⟨.clusterCtaid, some .x⟩ = some 1 := rfl
example : sregValue launch (13 * 384) ⟨.clusterCtarank, none⟩ = some 1 := rfl
example : sregValue launch (13 * 384) ⟨.clusterid, some .x⟩ = some 6 := rfl
example : sregValue launch 0 ⟨.nclusterid, some .x⟩ = some 512 := rfl
example : sregValue launch 0 ⟨.clusterNctaid, some .x⟩ = some 2 := rfl

-- These values enter the actual register-read path used by local instructions.
example : readBits launch (13 * 384) {} 32 (.sreg ⟨.clusterCtaid, some .x⟩) =
    .ok (BitVec.ofNat 64 1) := rfl

-- Target rank zero in cluster 6 is CTA 12, not grid CTA 0.
example : launch.peerCta 13 0 = some 12 := rfl
example : launch.peerCta 12 1 = some 13 := rfl
example : launch.peerCta 12 2 = none := rfl
example : launch.peerCta 1024 0 = none := rfl
example : ({ launch with grid := 13 }).peerCta 12 1 = none := rfl

example : launch.mapShared 13 0 ⟨.shared, 13, 64⟩ = some ⟨.shared, 12, 64⟩ := rfl
example : launch.mapShared 13 0 ⟨.shared, 11, 64⟩ = none := rfl
example : launch.mapShared 13 0 ⟨.global, 0, 64⟩ = none := rfl
example : SameCluster launch (12 * 384) (13 * 384) := by unfold SameCluster; decide
example : ¬ SameCluster launch (13 * 384) (14 * 384) := by unfold SameCluster; decide

-- The rules are not specialized to two-CTA kernels.
private def larger : Launch :=
  { grid := 32, block := 384, params := fun _ => none, clusterSize := 8 }
example : larger.peerCta 19 7 = some 23 := rfl
example : sregValue larger (19 * 384) ⟨.clusterCtarank, none⟩ = some 3 := rfl

end
end PTX.Tests.Cluster
