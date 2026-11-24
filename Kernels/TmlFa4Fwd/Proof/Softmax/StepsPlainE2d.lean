-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE2b
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE1b
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainSw
import Tactics.KernelRfl

@[expose] public section

/-! # A plain round's exponent stretch: the composition, the later sites

The software `exp2` sites at pcs 7154, 7175, 7232, 7253, 7286 and 7307, each from the facts
before it (the previous run's end facts with the constants and control facts, or the previous
site's) to the lookup list with its outputs in front (`pS…`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

abbrev pqL7 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  swOut (lookupD (pH6 p L g v)) 5612 5613 5164 5167 ++ (pH6 p L g v)

theorem pS7286 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7286
    (pH6 p L g v) 7307 (pqL7 p L g v) := by
  have h := sw7286 L g (lookupD (pH6 p L g v)) ((pH6 p L g v).map Prod.fst)
    ((pqL7 p L g v).map Prod.fst)
    (by have := kin (expoP3_ok hp v).2 5612 (by kd_tac); exact this)
    (by have := kin (expoP3_ok hp v).2 5613 (by kd_tac); exact this)
    (mem_of_contains (r := 5612) (l := (pH6 p L g v).map Prod.fst) (by kernel_rfl))
    (mem_of_contains (r := 5613) (l := (pH6 p L g v).map Prod.fst) (by kernel_rfl))
    ⟨cst_of (by kernel_rfl), by kernel_rfl⟩ (cov_of (by kernel_rfl))
  refine ⟨1, h.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_⟩
  · rw [show factsFrom ((pH6 p L g v).map Prod.fst) (valueEx (lookupD (pH6 p L g v)) []) =
      (pH6 p L g v) by kernel_rfl]
    exact hR
  · rw [show factsFrom ((pqL7 p L g v).map Prod.fst)
      (valueEx (lookupD (pH6 p L g v)) (segValsY mt7286 CuteSlot.y0 CuteSlot.y1
        (laneR (lookupD (pH6 p L g v) 5612)) (laneR (lookupD (pH6 p L g v) 5613)) ++ [])) =
      pqL7 p L g v by kernel_rfl] at hR
    exact hR


end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
