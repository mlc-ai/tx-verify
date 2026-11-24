-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderLoop

@[expose] public section

/-! Definitions and helper facts of `LoaderSteps`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The predicate of the rank branch after block `b`'s last load. -/
def rankPred : Fin 8 → Nat
  | 0 => 26 | 1 => 27 | 2 => 28 | 3 => 29
  | 4 => 30 | 5 => 31 | 6 => 32 | 7 => 33

/-- The rank branch three instructions after each block's last load skips the arrival. -/
theorem code_rank : ∀ b : Fin 8, kernel.code[(Site.load b 2).pc + 3]? =
    some ⟨some (rankPred b, false), .bra ((Site.arrive b).pc + 1) false⟩
  | 0 => Flow.code_142
  | 1 => Flow.code_171
  | 2 => Flow.code_200
  | 3 => Flow.code_229
  | 4 => Flow.code_257
  | 5 => Flow.code_285
  | 6 => Flow.code_313
  | 7 => Flow.code_341

/-- The end-of-trip branch on whether the trip was the last of the task. -/
theorem code_trip : kernel.code[(Site.arrive 7).pc + 3]? =
    some ⟨some (34, false), .bra ((Site.wait 0).pc - 4) false⟩ := by
  rw [show (Site.arrive 7).pc + 3 = 346 from rfl, show (Site.wait 0).pc - 4 = 115 from rfl]
  exact Flow.code_346

/-- Facts at `pc'` follow from facts at `pc` when every register live at `pc'` is live at `pc`. -/
theorem factsAt_mono {L : Launch} {g pc pc' : Nat} {d : D} {R : Nat → Option Value}
    (h : Holds R (factsAt L g pc d)) (hsub : (Flow.live pc').all (· ∈ Flow.live pc) = true) :
    Holds R (factsAt L g pc' d) :=
  Flow.holds_factsFrom_mono h (by simpa only [List.all_eq_true, decide_eq_true_eq] using hsub)

theorem trip_branch_fact (L : Launch) (g : Nat) (d : D) :
    (34, Value.pred (decide (d.q ≠ 128))) ∈ factsAt L g ((Site.arrive 7).pc + 3) d :=
  List.mem_map.mpr ⟨34, by table_decide, by simp only [valueOf, extra, List.lookup_cons,
    Nat.reduceBEq, Option.getD_some]⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
