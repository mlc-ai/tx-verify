-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Clc.ClcEffects
public import Core.Source.Decode

/-!
# Launch coordinates (PROG-LAUNCH, PROG-CLUSTER, THREAD-SREG)

A one-dimensional launch has the values of the one-dimensional model; a three-dimensional launch
with three-dimensional clusters numbers its CTAs, clusters and ranks consistently.
-/

namespace PTX.Tests.LaunchCoordinates
noncomputable section

-- These hold for every one-dimensional launch, not only one kernel's shape.
example (L : Launch) (h : L.OneDim) (g : Nat) : sregValue L g ⟨.tid, some .y⟩ = some 0 :=
  ((sregValue_oneDim h g).2.2.2.2.2.2.2.2.2.2 .y (by decide)).1
example (L : Launch) (h : L.OneDim) (g : Nat) : sregValue L g ⟨.ntid, some .z⟩ = some 1 :=
  ((sregValue_oneDim h g).2.2.2.2.2.2.2.2.2.2 .z (by decide)).2.2.2.2.1
example (L : Launch) (h : L.OneDim) (g : Nat) : sregValue L g ⟨.tid, some .x⟩ = some (g % L.block)
:=
  (sregValue_oneDim h g).1
example (L : Launch) (h : L.oneDimLaunch) : L.clusterGridValid :=
  Launch.oneDimLaunch_clusterGridValid h

private def env : Decode.Env := { classes := [⟨"r".toList, 0, 32⟩], labels := [], params := [] }
example : Decode.op env "mov.u32" [.register "r", .register "%tid.y"] =
    .ok (.move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.tid, some .y⟩]⟩) := rfl
example : Decode.op env "mov.u32" [.register "r", .register "%ntid.y"] =
    .ok (.move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.ntid, some .y⟩]⟩) := rfl

/-- A grid of 4x2x2 CTAs in clusters of 2x2x1 CTAs, with CTAs of 4x2x1 threads. -/
private def L3 : Launch := {
  grid := 16, block := 8, params := fun _ => none, clusterSize := 4,
  ntid := ⟨4, 2, 1⟩, nctaid := ⟨4, 2, 2⟩, clusterNctaid := ⟨2, 2, 1⟩ }

example : L3.clusterGridValid := by decide
-- The launch is not one-dimensional, so no one-dimensional kernel's precondition admits it.
example : ¬ L3.oneDimLaunch := fun h => absurd h.1.2.1 (by decide)
example : L3.nclusteridOf 0 = ⟨2, 1, 2⟩ := rfl

-- `%ctaid` of the 16 CTAs covers the grid exactly once.
example : ∀ c < 16, (L3.ctaidOf c).x < 4 ∧ (L3.ctaidOf c).y < 2 ∧ (L3.ctaidOf c).z < 2 := by
  decide
example : ∀ c < 16, ∀ d < 16, L3.ctaidOf c = L3.ctaidOf d → c = d := by decide
-- `%cluster_ctaid` is in the cluster shape, and the rank is its linear index with `x` fastest.
example : ∀ c < 16, (L3.clusterCtaidOf c).x < 2 ∧ (L3.clusterCtaidOf c).y < 2 ∧
    (L3.clusterCtaidOf c).z = 0 := by decide
example : ∀ c < 16, L3.rankOfCta c =
    (L3.clusterCtaidOf c).x + (L3.clusterCtaidOf c).y * 2 := by decide
-- `%ctaid = %clusterid * %cluster_nctaid + %cluster_ctaid` in each dimension.
example : ∀ c < 16, (L3.ctaidOf c).y =
    (L3.clusteridOf c).y * 2 + (L3.clusterCtaidOf c).y := by decide
-- The CTAs of one cluster have the same `%clusterid`, and CTAs of different clusters do not.
example : ∀ c < 16, ∀ d < 16,
    (L3.clusteridOf c = L3.clusteridOf d ↔ L3.clusterOfCta c = L3.clusterOfCta d) := by decide

-- CTA 6 is rank 2 of cluster 1: `%cluster_ctaid = (0, 1, 0)`, `%clusterid = (0, 0, 1)`, so
-- `%ctaid = (0, 1, 1)`.
example : L3.clusterCtaidOf 6 = ⟨0, 1, 0⟩ := rfl
example : L3.clusteridOf 6 = ⟨0, 0, 1⟩ := rfl
example : L3.ctaidOf 6 = ⟨0, 1, 1⟩ := rfl
-- Thread 5 of CTA 6: `%tid = (1, 1, 0)`, lane 5.
example : sregValue L3 (6 * 8 + 5) ⟨.tid, some .x⟩ = some 1 := rfl
example : sregValue L3 (6 * 8 + 5) ⟨.tid, some .y⟩ = some 1 := rfl
example : sregValue L3 (6 * 8 + 5) ⟨.tid, some .z⟩ = some 0 := rfl
example : sregValue L3 (6 * 8 + 5) ⟨.ctaid, some .y⟩ = some 1 := rfl
example : sregValue L3 (6 * 8 + 5) ⟨.ctaid, some .z⟩ = some 1 := rfl
example : sregValue L3 (6 * 8 + 5) ⟨.clusterid, some .z⟩ = some 1 := rfl
example : sregValue L3 (6 * 8 + 5) ⟨.clusterCtaid, some .y⟩ = some 1 := rfl
example : sregValue L3 (6 * 8 + 5) ⟨.clusterCtarank, none⟩ = some 2 := rfl
example : sregValue L3 0 ⟨.clusterNctarank, none⟩ = some 4 := rfl
example : sregValue L3 0 ⟨.nclusterid, some .z⟩ = some 2 := rfl
example : sregValue L3 0 ⟨.clusterNctaid, some .y⟩ = some 2 := rfl
example : sregValue L3 0 ⟨.nctaid, some .x⟩ = some 4 := rfl
example : sregValue L3 (6 * 8 + 5) ⟨.laneid, none⟩ = some 5 := rfl
-- Peers through the rank: rank 3 of CTA 6's cluster is CTA 7, `%ctaid = (1, 1, 1)`.
example : L3.peerCta 6 3 = some 7 := by decide
example : L3.ctaidOf 7 = ⟨1, 1, 1⟩ := rfl
example : L3.peerCta 6 4 = none := by decide
-- The CTA pair of rank 2 (`cta_group::2`) is ranks 2 and 3 of the same cluster.
example : L3.rankOfCta 6 / 2 = L3.rankOfCta 7 / 2 ∧ L3.clusterOfCta 6 = L3.clusterOfCta 7 := by
  decide
-- A first CTA of a canceled cluster: cluster 3 starts at CTA 12, `%ctaid = (2, 0, 1)`.
example : L3.ctaidOf (3 * 4) = ⟨2, 0, 1⟩ := rfl

/-- A grid of 8 CTAs with regular clusters of 2 and preferred clusters of 4, placed as one
preferred cluster (CTAs `0`–`3`) and two regular clusters (`4`–`5`, `6`–`7`). -/
private def LM : Launch := {
  grid := 8, block := 64, params := fun _ => none, clusterSize := 2,
  preferredNctaid := ⟨4, 1, 1⟩, nclusters := 3,
  clusterPlaces := fun k => match k with
    | 0 => ⟨⟨0, 0, 0⟩, ⟨4, 1, 1⟩, ⟨0, 0, 0⟩, ⟨3, 1, 1⟩⟩
    | 1 => ⟨⟨4, 0, 0⟩, ⟨2, 1, 1⟩, ⟨1, 0, 0⟩, ⟨3, 1, 1⟩⟩
    | _ => ⟨⟨6, 0, 0⟩, ⟨2, 1, 1⟩, ⟨2, 0, 0⟩, ⟨3, 1, 1⟩⟩ }

example : LM.clusterGridValid := by decide
example : ¬ LM.oneDimLaunch := fun h => absurd (congrFun h.1.2.2.2.2.2 0) (by decide)
-- The placement must tile the grid: two preferred clusters overlapping at CTA 2 are rejected.
example : ¬ { LM with clusterPlaces := fun k => match k with
    | 0 => ⟨⟨0, 0, 0⟩, ⟨4, 1, 1⟩, ⟨0, 0, 0⟩, ⟨3, 1, 1⟩⟩
    | 1 => ⟨⟨2, 0, 0⟩, ⟨4, 1, 1⟩, ⟨1, 0, 0⟩, ⟨3, 1, 1⟩⟩
    | _ => ⟨⟨6, 0, 0⟩, ⟨2, 1, 1⟩, ⟨2, 0, 0⟩, ⟨3, 1, 1⟩⟩ }.clusterGridValid := by decide
-- A cluster of a third shape is rejected.
example : ¬ { LM with nclusters := 4, clusterPlaces := fun k => match k with
    | 0 => ⟨⟨0, 0, 0⟩, ⟨4, 1, 1⟩, ⟨0, 0, 0⟩, ⟨4, 1, 1⟩⟩
    | 1 => ⟨⟨4, 0, 0⟩, ⟨2, 1, 1⟩, ⟨1, 0, 0⟩, ⟨4, 1, 1⟩⟩
    | 2 => ⟨⟨6, 0, 0⟩, ⟨1, 1, 1⟩, ⟨2, 0, 0⟩, ⟨4, 1, 1⟩⟩
    | _ => ⟨⟨7, 0, 0⟩, ⟨1, 1, 1⟩, ⟨3, 0, 0⟩, ⟨4, 1, 1⟩⟩ }.clusterGridValid := by decide

-- Clusters, ranks and sizes of each CTA's own cluster.
example : (List.range 8).map LM.clusterOfCta = [0, 0, 0, 0, 1, 1, 2, 2] := by decide
example : (List.range 8).map LM.rankOfCta = [0, 1, 2, 3, 0, 1, 0, 1] := by decide
example : (List.range 8).map LM.clusterSizeOf = [4, 4, 4, 4, 2, 2, 2, 2] := by decide
example : ∀ c < 8, (LM.ctaidOf c).x = c := by decide
-- Special registers of thread 0 of CTA 3 (preferred cluster) and of CTA 5 (regular cluster).
example : sregValue LM (3 * 64) ⟨.clusterCtarank, none⟩ = some 3 := by decide
example : sregValue LM (3 * 64) ⟨.clusterNctarank, none⟩ = some 4 := by decide
example : sregValue LM (3 * 64) ⟨.clusterNctaid, some .x⟩ = some 4 := by decide
example : sregValue LM (3 * 64) ⟨.clusterCtaid, some .x⟩ = some 3 := by decide
example : sregValue LM (3 * 64) ⟨.ctaid, some .x⟩ = some 3 := by decide
example : sregValue LM (5 * 64) ⟨.clusterCtarank, none⟩ = some 1 := by decide
example : sregValue LM (5 * 64) ⟨.clusterNctarank, none⟩ = some 2 := by decide
example : sregValue LM (5 * 64) ⟨.clusterNctaid, some .x⟩ = some 2 := by decide
example : sregValue LM (5 * 64) ⟨.clusterid, some .x⟩ = some 1 := by decide
example : sregValue LM (5 * 64) ⟨.ctaid, some .x⟩ = some 5 := by decide
-- Peers through the own cluster's rank: rank 3 exists in the preferred cluster only.
example : LM.peerCta 1 3 = some 3 := by decide
example : LM.peerCta 5 0 = some 4 := by decide
example : LM.peerCta 5 3 = none := by decide
-- CTA pairs (`cta_group::2`): ranks 2 and 3 of the preferred cluster, ranks 0 and 1 of a regular
-- one; CTAs 3 and 4 are in different clusters.
example : LM.rankOfCta 2 / 2 = LM.rankOfCta 3 / 2 ∧ LM.clusterOfCta 2 = LM.clusterOfCta 3 := by
  decide
example : LM.rankOfCta 6 / 2 = LM.rankOfCta 7 / 2 ∧ LM.clusterOfCta 6 = LM.clusterOfCta 7 := by
  decide
example : LM.clusterOfCta 3 ≠ LM.clusterOfCta 4 := by decide
-- Cluster launch control: a canceled regular cluster reports its first CTA `(6, 0, 0)`, a canceled
-- preferred cluster `(0, 0, 0)`; both are valid tasks.
example : Clc.ValidTask LM 2 ∧ Clc.ValidTask LM 0 := by unfold Clc.ValidTask; decide
example : ¬ Clc.ValidTask LM 3 := by unfold Clc.ValidTask; decide
private theorem first2 : LM.ctaidOf (LM.clusterStart 2) = ⟨6, 0, 0⟩ := by decide
private theorem first0 : LM.ctaidOf (LM.clusterStart 0) = ⟨0, 0, 0⟩ := by decide
example (i : EvId) : Clc.responseOf LM i (some 2) =
    ⟨Clc.requestId i, some (BitVec.ofNat 32 6, BitVec.ofNat 32 0, BitVec.ofNat 32 0)⟩ := by
  simp only [Clc.responseOf, Option.map_some, first2]
example (i : EvId) : Clc.responseOf LM i (some 0) =
    ⟨Clc.requestId i, some (BitVec.ofNat 32 0, BitVec.ofNat 32 0, BitVec.ofNat 32 0)⟩ := by
  simp only [Clc.responseOf, Option.map_some, first0]
-- The CTAs of the canceled preferred cluster are CTAs 0 to 3.
example : (List.range 8).filter (fun c => LM.clusterOfCta c == 0) = [0, 1, 2, 3] := by decide

-- A thread of the three-dimensional launch runs `mov.u32 r0, %ctaid.z; exit`.
private def ctaidZ : Kernel := {
  name := "ctaidZ", params := [], code := [
    { op := .move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.ctaid, some .z⟩]⟩ },
    { op := .exit }] }

example : Produces ctaidZ [] L3 (6 * 8 + 5) [⟨1, .exit⟩] :=
  ⟨none, .last (.single rfl) ⟨.exit, rfl, rfl, rfl⟩⟩
example : out ctaidZ [] L3 (6 * 8 + 5) {} = .tau (next (setReg {} 0 (.bits 32 1))) := rfl

end
end PTX.Tests.LaunchCoordinates
