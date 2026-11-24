-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Regs
public import Core.Sync.Cluster

@[expose] public section

/-! # Launch facts under explicit parameters

`seg_sym` runs segments under `explicitParams L ps` (the launch with the role's parameters
written out), so a value the code reads from a special register is stated on that launch. Only the
parameters differ, so the CTA index and the block are `L`'s; a kernel rewrites its tables' and
decision lemmas' terms with these. -/

namespace PTX.Proof

theorem explicitParams_locate (L : Launch) (ps : List (String × Nat)) :
    ∀ n k c, (explicitParams L ps).locate n k c = L.locate n k c
  | 0, k, c => by simp only [Launch.locate, explicitParams]
  | n + 1, k, c => by
    simp only [Launch.locate, explicitParams_locate L ps n]
    rfl

/-- The CTA index under a launch with explicit parameters is the launch's. -/
theorem explicitParams_ctaidOf (L : Launch) (ps : List (String × Nat)) (c : Nat) :
    (explicitParams L ps).ctaidOf c = L.ctaidOf c := by
  simp only [Launch.ctaidOf, Launch.placeOf, Launch.clusterCtaidOf, Launch.rankOfCta,
    Launch.clusterOfCta, explicitParams_locate]
  rfl

theorem explicitParams_block (L : Launch) (ps : List (String × Nat)) :
    (explicitParams L ps).block = L.block := rfl

end PTX.Proof
