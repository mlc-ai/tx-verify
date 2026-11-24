-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE2b
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE1
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

abbrev pqL5 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  swOut (lookupD (pH4 p L g v)) 5596 5597 5152 5155 ++ (pH4 p L g v)

theorem pS7232 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7232
    (pH4 p L g v) 7253 (pqL5 p L g v) := by
  have h := sw7232 L g (lookupD (pH4 p L g v)) ((pH4 p L g v).map Prod.fst)
    ((pqL5 p L g v).map Prod.fst)
    (by have := kin (expoP2_ok hp v).2 5596 (by kd_tac); exact this)
    (by have := kin (expoP2_ok hp v).2 5597 (by kd_tac); exact this)
    (mem_of_contains (r := 5596) (l := (pH4 p L g v).map Prod.fst) (by kernel_rfl))
    (mem_of_contains (r := 5597) (l := (pH4 p L g v).map Prod.fst) (by kernel_rfl))
    ⟨cst_of (by kernel_rfl), by kernel_rfl⟩ (cov_of (by kernel_rfl))
  refine ⟨1, h.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_⟩
  · rw [show factsFrom ((pH4 p L g v).map Prod.fst) (valueEx (lookupD (pH4 p L g v)) []) =
      (pH4 p L g v) by kernel_rfl]
    exact hR
  · rw [show factsFrom ((pqL5 p L g v).map Prod.fst)
      (valueEx (lookupD (pH4 p L g v)) (segValsY mt7232 CuteSlot.y0 CuteSlot.y1
        (laneR (lookupD (pH4 p L g v) 5596)) (laneR (lookupD (pH4 p L g v) 5597)) ++ [])) =
      pqL5 p L g v by kernel_rfl] at hR
    exact hR

abbrev pqL6 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  swOut (lookupD (pqL5 p L g v)) 5598 5599 5158 5161 ++ (pqL5 p L g v)

theorem pS7253 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7253
    (pqL5 p L g v) 7274 (pqL6 p L g v) := by
  have h := sw7253 L g (lookupD (pqL5 p L g v)) ((pqL5 p L g v).map Prod.fst)
    ((pqL6 p L g v).map Prod.fst)
    (by have := kin (expoP2_ok hp v).2 5598 (by kd_tac); exact this)
    (by have := kin (expoP2_ok hp v).2 5599 (by kd_tac); exact this)
    (mem_of_contains (r := 5598) (l := (pqL5 p L g v).map Prod.fst) (by kernel_rfl))
    (mem_of_contains (r := 5599) (l := (pqL5 p L g v).map Prod.fst) (by kernel_rfl))
    ⟨cst_of (by kernel_rfl), by kernel_rfl⟩ (cov_of (by kernel_rfl))
  refine ⟨1, h.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_⟩
  · rw [show factsFrom ((pqL5 p L g v).map Prod.fst) (valueEx (lookupD (pqL5 p L g v)) []) =
      (pqL5 p L g v) by kernel_rfl]
    exact hR
  · rw [show factsFrom ((pqL6 p L g v).map Prod.fst)
      (valueEx (lookupD (pqL5 p L g v)) (segValsY mt7253 CuteSlot.y0 CuteSlot.y1
        (laneR (lookupD (pqL5 p L g v) 5598)) (laneR (lookupD (pqL5 p L g v) 5599)) ++ [])) =
      pqL6 p L g v by kernel_rfl] at hR
    exact hR


end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
