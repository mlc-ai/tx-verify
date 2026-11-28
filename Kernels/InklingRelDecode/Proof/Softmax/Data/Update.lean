-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Alpha
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Rescale

@[expose] public section

/-! # The round's registers as the rescale run leaves them -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section
variable {L : Launch}

theorem dFS_round {s : Site} (hr : inRound s = true) (v : Vals) (h1 : s ≠ .waitLdO)
    (h2 : s ≠ .bar24) (h3 : s ≠ .stO) :
    dFS L s v = [(498, scaleW L), (1914, v.m)] ++ alphaFacts L v := by
  cases s <;> simp_all [dFS, inRound]

/-- The round's facts are among the facts of every site of the round. -/
theorem round_sub {s : Site} (hr : inRound s = true) (v : Vals) :
    ∀ x ∈ [(498, scaleW L), (1914, v.m)] ++ alphaFacts L v, x ∈ dFS L s v := by
  by_cases h1 : s = .waitLdO
  · subst h1; exact round_sub_rs0 v
  by_cases h2 : s = .bar24 ∨ s = .stO
  · rcases h2 with rfl | rfl <;> exact round_sub_rs2 v
  rw [dFS_round hr v h1 (fun h => h2 (.inl h)) (fun h => h2 (.inr h))]
  exact fun _ h => h

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
