-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierRoundHistory

namespace PTX
noncomputable section
private def launch : Launch := { grid := 16, block := 128, params := fun _ => none, sharedBase := 0,
                                 clusterSize := ⟨8, by decide⟩ }
private def sm (cta : Nat) : Loc := ⟨.shared, cta, 128⟩

-- The issuer can copy to a different pair in its cluster.
example : TensorRoute launch 0 true .two (sm 6) (sm 7) := by decide
example : TensorRoute launch 0 true .two (sm 7) (sm 6) := by decide
example : TensorRoute launch 0 true .two (sm 6) (sm 6) := by decide
example : ¬ TensorRoute launch 0 true .two (sm 1) (sm 2) := by decide
example : ¬ TensorRoute launch 0 true .two (sm 6) (sm 0) := by decide
example : ¬ TensorRoute launch 0 true .two (sm 6) (sm 14) := by decide
example : ¬ TensorRoute launch 0 true .one (sm 6) (sm 7) := by decide
example : TensorRoute launch 0 true .one (sm 6) (sm 6) := by decide
example : ¬ TensorRoute launch 0 false .two (sm 0) (sm 1) := by decide
example : TensorRoute launch 0 false .two (sm 0) (sm 0) := by decide
-- Cluster-relative pairing also works away from cluster zero.
example : TensorRoute launch 8 true .two (sm 14) (sm 15) := by decide

end
end PTX
