-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE2
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

/-- A run's end facts with the constants and control facts. -/
abbrev pH2 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  expoPS2 p v ++ cHP p L g v
abbrev pH4 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  expoPS4 p v ++ cHP p L g v
abbrev pH6 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  expoPS6 p v ++ cHP p L g v

/-- A lane input whose kind in a literal kind list is `fl`, `nn` or `ni`. -/
theorem kin {K : List (Nat × Kd)} {G : List (Nat × Value)}
    (h : ∀ r, (kOf K r).Has (lookupD G r)) (r : Nat)
    (hr : kOf K r = .s .fl ∨ kOf K r = .s .nn ∨ kOf K r = .s .ni) :
    (∃ x : ℝ, Assumption.readEReal .f32 (lookupD G r) = some (.ok (x : EReal))) ∨
      lookupD G r = negInf32 := by
  have h := h r
  rcases hr with e | e | e <;> rw [e] at h
  · exact lane_in (k := .fl) rfl h
  · exact lane_in (k := .nn) rfl h
  · exact lane_in (k := .ni) rfl h

abbrev pqL3 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  swOut (lookupD (pH2 p L g v)) 5580 5581 5140 5143 ++ (pH2 p L g v)

theorem pS7154 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7154
    (pH2 p L g v) 7175 (pqL3 p L g v) := by
  have h := sw7154 L g (lookupD (pH2 p L g v)) ((pH2 p L g v).map Prod.fst)
    ((pqL3 p L g v).map Prod.fst)
    (by have := kin (expoP1_ok hp v).2 5580 (by kd_tac); exact this)
    (by have := kin (expoP1_ok hp v).2 5581 (by kd_tac); exact this)
    (mem_of_contains (r := 5580) (l := (pH2 p L g v).map Prod.fst) (by kernel_rfl))
    (mem_of_contains (r := 5581) (l := (pH2 p L g v).map Prod.fst) (by kernel_rfl))
    ⟨cst_of (by kernel_rfl), by kernel_rfl⟩ (cov_of (by kernel_rfl))
  refine ⟨1, h.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_⟩
  · rw [show factsFrom ((pH2 p L g v).map Prod.fst) (valueEx (lookupD (pH2 p L g v)) []) =
      (pH2 p L g v) by kernel_rfl]
    exact hR
  · rw [show factsFrom ((pqL3 p L g v).map Prod.fst)
      (valueEx (lookupD (pH2 p L g v)) (segValsY mt7154 CuteSlot.y0 CuteSlot.y1
        (laneR (lookupD (pH2 p L g v) 5580)) (laneR (lookupD (pH2 p L g v) 5581)) ++ [])) =
      pqL3 p L g v by kernel_rfl] at hR
    exact hR

abbrev pqL4 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  swOut (lookupD (pqL3 p L g v)) 5582 5583 5146 5149 ++ (pqL3 p L g v)

theorem pS7175 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7175
    (pqL3 p L g v) 7196 (pqL4 p L g v) := by
  have h := sw7175 L g (lookupD (pqL3 p L g v)) ((pqL3 p L g v).map Prod.fst)
    ((pqL4 p L g v).map Prod.fst)
    (by have := kin (expoP1_ok hp v).2 5582 (by kd_tac); exact this)
    (by have := kin (expoP1_ok hp v).2 5583 (by kd_tac); exact this)
    (mem_of_contains (r := 5582) (l := (pqL3 p L g v).map Prod.fst) (by kernel_rfl))
    (mem_of_contains (r := 5583) (l := (pqL3 p L g v).map Prod.fst) (by kernel_rfl))
    ⟨cst_of (by kernel_rfl), by kernel_rfl⟩ (cov_of (by kernel_rfl))
  refine ⟨1, h.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_⟩
  · rw [show factsFrom ((pqL3 p L g v).map Prod.fst) (valueEx (lookupD (pqL3 p L g v)) []) =
      (pqL3 p L g v) by kernel_rfl]
    exact hR
  · rw [show factsFrom ((pqL4 p L g v).map Prod.fst)
      (valueEx (lookupD (pqL3 p L g v)) (segValsY mt7175 CuteSlot.y0 CuteSlot.y1
        (laneR (lookupD (pqL3 p L g v) 5582)) (laneR (lookupD (pqL3 p L g v) 5583)) ++ [])) =
      pqL4 p L g v by kernel_rfl] at hR
    exact hR


end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
