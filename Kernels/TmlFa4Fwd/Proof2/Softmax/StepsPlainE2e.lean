-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainE2d

@[expose] public section

/-! # A plain round's exponent stretch: the composition, the later sites

The software `exp2` sites at pcs 7154, 7175, 7232, 7253, 7286 and 7307, each from the facts
before it (the previous run's end facts with the constants and control facts, or the previous
site's) to the lookup list with its outputs in front (`pS…`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

abbrev pqL8 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  swOut (lookupD (pqL7 p L g v)) 5614 5615 5170 5173 ++ (pqL7 p L g v)

theorem pS7307 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7307
    (pqL7 p L g v) 7328 (pqL8 p L g v) := by
  have h := sw7307 L g (lookupD (pqL7 p L g v)) ((pqL7 p L g v).map Prod.fst)
    ((pqL8 p L g v).map Prod.fst)
    (by have := kin (expoP3_ok hp v).2 5614 (by kd_tac); exact this)
    (by have := kin (expoP3_ok hp v).2 5615 (by kd_tac); exact this)
    (mem_of_contains (r := 5614) (l := (pqL7 p L g v).map Prod.fst) (by kernel_rfl))
    (mem_of_contains (r := 5615) (l := (pqL7 p L g v).map Prod.fst) (by kernel_rfl))
    ⟨cst_of (by kernel_rfl), by kernel_rfl⟩ (cov_of (by kernel_rfl))
  refine ⟨1, h.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_⟩
  · rw [show factsFrom ((pqL7 p L g v).map Prod.fst) (valueEx (lookupD (pqL7 p L g v)) []) =
      (pqL7 p L g v) by kernel_rfl]
    exact hR
  · rw [show factsFrom ((pqL8 p L g v).map Prod.fst)
      (valueEx (lookupD (pqL7 p L g v)) (segValsY mt7307 CuteSlot.y0 CuteSlot.y1
        (laneR (lookupD (pqL7 p L g v) 5614)) (laneR (lookupD (pqL7 p L g v) 5615)) ++ [])) =
      pqL8 p L g v by kernel_rfl] at hR
    exact hR



end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
