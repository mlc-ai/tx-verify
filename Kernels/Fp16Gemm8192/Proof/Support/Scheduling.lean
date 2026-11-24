-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcOwnership
public import Lemmas.Clc.ClcExecution
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! CLC ownership and finite task accounting for the unchanged production launch.

These theorems concern the scheduler arbitration and the identity encoded in its
responses. They do not assert that a worker has computed a claimed output tile.
In particular, no failed response is treated as proof that the grid is exhausted.
-/
namespace PTX.Kernels.Fp16Gemm8192
open PTX
noncomputable section

/-- The frozen launch has 1024 CTAs, in pairs, hence 512 logical cluster tasks. The launch
condition is needed because `Clc.ValidTask` also requires the cluster placement
(`Launch.clusterGridValid`) and the CTA coordinates of a cluster's first CTA. -/
theorem clc_valid_task_iff {L : Launch} (hlaunch : L.oneDimLaunch) (hgrid : L.grid = 1024)
    (hcluster : L.clusterSize.val = 2) {task : Nat} :
    Clc.ValidTask L task ↔ task < 512 := by
  have hcgv := Launch.oneDimLaunch_clusterGridValid hlaunch
  rw [Clc.validTask_oneDim hlaunch.1, hgrid, hcluster]
  simp only [hcgv, true_and]
  omega

end
end PTX.Kernels.Fp16Gemm8192
