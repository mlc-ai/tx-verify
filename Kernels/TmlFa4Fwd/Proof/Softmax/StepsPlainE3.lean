-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE2c
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE2e
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE1b
import Lemmas.Flow.RunFrame
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # A plain round's exponent stretch: the composition, the later runs

Runs 2 to 4, each from the facts after the sites before it, framed with the constants and the
control facts (`pR2` … `pR4`), and the whole stretch from pc 6892 to the first P store
(`expoP_seg`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}


/-- **Run 2** (pcs 7196 to 7231). -/
theorem pR2 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7196
    (pqL4 p L g v) 7232 (pH4 p L g v) := by
  have hfr := SegD.frame (H := cHP p L g v) Gen.rulesFrame
    (Gen.expoP2_run L g (lookupD (expoPS3 p v))) rfl (by kernel_rfl) (by kernel_rfl)
    (Gen.segFree_range (by kernel_rfl))
  refine seg_of_segD (hfr.weaken_start fun R hR => ?_) (expoP2_ok hp v).1
  have hH : Holds R (cHP p L g v) := by
    have h := holds_lookupD (keys := (cHP p L g v).map Prod.fst) hR (by kernel_rfl)
    rw [show factsFrom ((cHP p L g v).map Prod.fst) (lookupD (pqL4 p L g v)) = cHP p L g v by
      kernel_rfl] at h
    exact h
  refine (holds_append _ _ _).mpr ⟨?_, hH⟩
  rw [expoP2_facts0_eq, show factsFrom ((Gen.expoP2_facts0 (lookupD (expoPS3 p v))).map Prod.fst)
      (lookupD (expoPS3 p v)) = factsFrom ((Gen.expoP2_facts0 (lookupD (expoPS3 p v))).map
        Prod.fst) (lookupD (pqL4 p L g v)) by kernel_rfl]
  exact holds_lookupD hR (by kernel_rfl)

/-- **Run 3** (pcs 7274 to 7285). -/
theorem pR3 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7274
    (pqL6 p L g v) 7286 (pH6 p L g v) := by
  have hfr := SegD.frame (H := cHP p L g v) Gen.rulesFrame
    (Gen.expoP3_run L g (lookupD (expoPS5 p v))) rfl (by kernel_rfl) (by kernel_rfl)
    (Gen.segFree_range (by kernel_rfl))
  refine seg_of_segD (hfr.weaken_start fun R hR => ?_) (expoP3_ok hp v).1
  have hH : Holds R (cHP p L g v) := by
    have h := holds_lookupD (keys := (cHP p L g v).map Prod.fst) hR (by kernel_rfl)
    rw [show factsFrom ((cHP p L g v).map Prod.fst) (lookupD (pqL6 p L g v)) = cHP p L g v by
      kernel_rfl] at h
    exact h
  refine (holds_append _ _ _).mpr ⟨?_, hH⟩
  rw [expoP3_facts0_eq, show factsFrom ((Gen.expoP3_facts0 (lookupD (expoPS5 p v))).map Prod.fst)
      (lookupD (expoPS5 p v)) = factsFrom ((Gen.expoP3_facts0 (lookupD (expoPS5 p v))).map
        Prod.fst) (lookupD (pqL6 p L g v)) by kernel_rfl]
  exact holds_lookupD hR (by kernel_rfl)

/-- **Run 4** (pcs 7328 to 7415). -/
theorem pR4 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7328
    (pqL8 p L g v) 7416 (expoPE p v ++ cHP p L g v) := by
  have hfr := SegD.frame (H := cHP p L g v) Gen.rulesFrame
    (Gen.expoP4_run L g (lookupD (expoPS7 p v))) rfl (by kernel_rfl) (by kernel_rfl)
    (Gen.segFree_range (by kernel_rfl))
  refine seg_of_segD (hfr.weaken_start fun R hR => ?_) (expoP4_ok hp v).1
  have hH : Holds R (cHP p L g v) := by
    have h := holds_lookupD (keys := (cHP p L g v).map Prod.fst) hR (by kernel_rfl)
    rw [show factsFrom ((cHP p L g v).map Prod.fst) (lookupD (pqL8 p L g v)) = cHP p L g v by
      kernel_rfl] at h
    exact h
  refine (holds_append _ _ _).mpr ⟨?_, hH⟩
  rw [expoP4_facts0_eq, show factsFrom ((Gen.expoP4_facts0 (lookupD (expoPS7 p v))).map Prod.fst)
      (lookupD (expoPS7 p v)) = factsFrom ((Gen.expoP4_facts0 (lookupD (expoPS7 p v))).map
        Prod.fst) (lookupD (pqL8 p L g v)) by kernel_rfl]
  exact holds_lookupD hR (by kernel_rfl)

/-- **The plain round's exponent stretch** (pcs 6892 to 7415). -/
theorem expoP_seg (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 6892
    (factsD p L g ⟨.narr .plain, v, 0, []⟩) 7416 (expoPE p v ++ cHP p L g v) :=
  Seg.comp_ex (pA0 hp v) <| Seg.comp_ex (pA1 hp v) <| Seg.comp_ex (pA2 hp v) <|
  Seg.comp_ex (pA3 hp v) <| Seg.comp_ex (pS7154 hp v) <| Seg.comp_ex (pS7175 hp v) <|
  Seg.comp_ex (pR2 hp v) <| Seg.comp_ex (pS7232 hp v) <| Seg.comp_ex (pS7253 hp v) <|
  Seg.comp_ex (pR3 hp v) <| Seg.comp_ex (pS7286 hp v) <| Seg.comp_ex (pS7307 hp v) <|
  pR4 hp v

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
