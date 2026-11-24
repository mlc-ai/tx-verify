-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Values

@[expose] public section

/-! # `row_sum`: no undefined behaviour

A thread faults only after a read of bytes other than the launch content, and every read returns
the launch content. -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

theorem no_ub (hpre : Pre L A B M K x mem0) (htf : ThreadFacts L A B M K x X)
    (hX : Consistent L kernel Prod mem0 X) : ¬ HasUb X := by
  rintro ⟨e, pc, f, he⟩
  rcases (event_cases htf hX he).2 with ⟨-, -, _, he'⟩ | ⟨-, -, _, -, -, he'⟩ | he' |
      ⟨_, _, -, -, bs, h0, hbad⟩
  · simp [rdE] at he'
  · simp [wrE] at he'
  · simp [exE] at he'
  · exact hbad (read_bytes hpre htf hX ⟨Flow.load_0, by unfold rdE at h0; exact h0⟩)

end
end PTX.Kernels.RowSum.Proof
