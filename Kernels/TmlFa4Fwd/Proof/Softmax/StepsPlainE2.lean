-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE0
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE1b
public import Lemmas.Flow.RunFrame
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainE1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainSw
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # A plain round's exponent stretch: the composition, first part

From the arrival at the correction warps' named barrier (pc 6892) through run 0 and the software
`exp2` sites at pcs 7090 and 7121 to pc 7142. The control facts (`ctlP`, the same registers
throughout the stretch) are carried by `SegD.frame` over the run and inside each site piece's
facts (a site is a segment step, which no frame crosses). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The control registers live through a plain round's exponent stretch. -/
def ctlP : List Nat := [441, 1062, 1069, 1215, 2390, 2535, 5127, 5181, 5183, 5184, 5185, 5187,
  6495, 6497, 7133, 7253, 7254, 7258, 7500, 7501, 7502, 7503, 7506, 8692]

/-- The control facts of the stretch, from the arrival state. -/
abbrev ctlPF (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  factsFrom ctlP (valueOfD p L g ⟨.narr .plain, v, 0, []⟩)

/-- A lane input of kind at most `ni` reads as a real or is `-∞`. -/
theorem lane_in {k : SK} {x : Value} (hk : k.le .ni = true) (h : k.Has x) :
    (∃ r : ℝ, Assumption.readEReal .f32 x = some (.ok (r : EReal))) ∨ x = negInf32 := by
  rcases (SK.mono hk h : SK.ni.Has x) with ⟨-, r, hr⟩ | e
  · exact .inl ⟨r, hr⟩
  · exact .inr e

/-- **Run 0** with the control facts. -/
theorem pA0 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 6892
    (factsD p L g ⟨.narr .plain, v, 0, []⟩) 7090 (expoPS0 p v ++ ctlPF p L g v) := by
  have hfr := SegD.frame (H := ctlPF p L g v) Gen.rulesFrame (Gen.expoP0_run L g (vExpoP p v))
    rfl (by kernel_rfl) (by kernel_rfl) (Gen.segFree_range (by kernel_rfl))
  refine seg_of_segD (hfr.weaken_start fun R hR => ?_) (expoP0_ok hp v).1
  refine (holds_append _ _ _).mpr ⟨?_, holds_sub hR (by kernel_rfl)⟩
  rw [expoP0_facts0_eq, show (Gen.expoP0_facts0 (vExpoP p v)).map Prod.fst = expoP0Keys by
    kernel_rfl, expoP_start]
  exact holds_sub hR (by kernel_rfl)

/-- The facts at pc 7121: the defining site's outputs and constants, run 0's end facts and the
control facts. -/
abbrev pqL1 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  swOut (lookupD (expoPS0 p v)) 5564 5565 5128 5131 ++ cuteConsts ++ expoPS0 p v ++ ctlPF p L g v

/-- The facts at pc 7142: the second site's outputs in front. -/
abbrev pqL2 (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  swOut (lookupD (pqL1 p L g v)) 5566 5567 5134 5137 ++ pqL1 p L g v

theorem k0_at (hp : Pre p L m) (v : V) (r : Nat) (hr : kOf qL7 r = .s .fl ∨ kOf qL7 r = .s .nn ∨
    kOf qL7 r = .s .ni) : (∃ x : ℝ, Assumption.readEReal .f32 (lookupD (expoPS0 p v) r) =
      some (.ok (x : EReal))) ∨ lookupD (expoPS0 p v) r = negInf32 := by
  have h := (expoP0_ok hp v).2 r
  rcases hr with e | e | e <;> rw [e] at h
  · exact lane_in (k := .fl) rfl h
  · exact lane_in (k := .nn) rfl h
  · exact lane_in (k := .ni) rfl h

theorem cov_of {T K1 K2 S : List Nat}
    (h : T.all (fun r => K1.contains r || (!K2.contains r && S.contains r)) = true) :
    ∀ r ∈ T, r ∈ K1 ∨ (r ∉ K2 ∧ r ∈ S) := by
  intro r hr
  have := List.all_eq_true.mp h r hr
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at this
  rcases this with h1 | ⟨h2, h3⟩
  · exact .inl h1
  · refine .inr ⟨fun hm => ?_, h3⟩
    have := List.contains_iff_mem.mpr hm
    rw [h2] at this; cases this

theorem mem_of_contains {r : Nat} {l : List Nat} (h : l.contains r = true) : r ∈ l :=
  List.contains_iff_mem.mp h

/-- The kind of a register in a literal kind list, among `fl`, `nn`, `ni`. -/
macro "kd_tac" : tactic => `(tactic| first
  | exact .inl (by kernel_rfl)
  | exact .inr (.inl (by kernel_rfl))
  | exact .inr (.inr (by kernel_rfl)))

/-- **The defining site at pc 7090.** -/
theorem pA1 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7090
    (expoPS0 p v ++ ctlPF p L g v) 7121 (pqL1 p L g v) := by
  have h := sw7090 L g (lookupD (expoPS0 p v ++ ctlPF p L g v))
    ((expoPS0 p v ++ ctlPF p L g v).map Prod.fst) ((pqL1 p L g v).map Prod.fst)
    (by have := k0_at hp v 5564 (by kd_tac); exact this)
    (by have := k0_at hp v 5565 (by kd_tac); exact this)
    (mem_of_contains (r := 5564) (l := (expoPS0 p v ++ ctlPF p L g v).map Prod.fst)
      (by kernel_rfl))
    (mem_of_contains (r := 5565) (l := (expoPS0 p v ++ ctlPF p L g v).map Prod.fst)
      (by kernel_rfl))
    (cov_of (by kernel_rfl))
  refine ⟨1, h.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_⟩
  · rw [show factsFrom ((expoPS0 p v ++ ctlPF p L g v).map Prod.fst)
      (valueEx (lookupD (expoPS0 p v ++ ctlPF p L g v)) []) = expoPS0 p v ++ ctlPF p L g v by
      kernel_rfl]
    exact hR
  · rw [show factsFrom ((pqL1 p L g v).map Prod.fst)
      (valueEx (lookupD (expoPS0 p v ++ ctlPF p L g v)) (segValsY (swMatch 7090 cuteExp2Define)
        CuteSlot.y0 CuteSlot.y1 (laneR (lookupD (expoPS0 p v ++ ctlPF p L g v) 5564))
        (laneR (lookupD (expoPS0 p v ++ ctlPF p L g v) 5565)) ++ [])) = pqL1 p L g v by
      kernel_rfl] at hR
    exact hR

theorem cst_of {m : SegMatch CuteSlot} {S : List Nat}
    (h : (m.shape.consts.map fun q => m.regOf q.1).all (S.contains ·) = true) :
    ∀ q ∈ m.shape.consts, m.regOf q.1 ∈ S := by
  intro q hq
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h _ (List.mem_map_of_mem hq))

/-- **The reusing site at pc 7121.** -/
theorem pA2 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7121
    (pqL1 p L g v) 7142 (pqL2 p L g v) := by
  have h := sw7121 L g (lookupD (pqL1 p L g v)) ((pqL1 p L g v).map Prod.fst)
    ((pqL2 p L g v).map Prod.fst)
    (by have := k0_at hp v 5566 (by kd_tac); exact this)
    (by have := k0_at hp v 5567 (by kd_tac); exact this)
    (mem_of_contains (r := 5566) (l := (pqL1 p L g v).map Prod.fst) (by kernel_rfl))
    (mem_of_contains (r := 5567) (l := (pqL1 p L g v).map Prod.fst) (by kernel_rfl))
    ⟨cst_of (by kernel_rfl), by kernel_rfl⟩ (cov_of (by kernel_rfl))
  refine ⟨1, h.weaken_start (fun R hR => ?_) |>.weaken_end fun R hR => ?_⟩
  · rw [show factsFrom ((pqL1 p L g v).map Prod.fst) (valueEx (lookupD (pqL1 p L g v)) []) =
      pqL1 p L g v by kernel_rfl]
    exact hR
  · rw [show factsFrom ((pqL2 p L g v).map Prod.fst)
      (valueEx (lookupD (pqL1 p L g v)) (segValsY mt7121 CuteSlot.y0 CuteSlot.y1
        (laneR (lookupD (pqL1 p L g v) 5566)) (laneR (lookupD (pqL1 p L g v) 5567)) ++ [])) =
      pqL2 p L g v by kernel_rfl] at hR
    exact hR

/-- Facts on fewer registers, read from a literal list by lookup. -/
theorem holds_lookupD {R : Nat → Option Value} {F : List (Nat × Value)} {keys : List Nat}
    (hR : Holds R F) (hk : keys.all ((F.map Prod.fst).contains ·) = true) :
    Holds R (factsFrom keys (lookupD F)) := by
  refine holds_of_pointwise fun r hr => ?_
  obtain ⟨x, hx⟩ := lookup_some (List.contains_iff_mem.mp (List.all_eq_true.mp hk r hr))
  rw [lookup_holds hR hx]
  simp only [lookupD, hx, Option.getD_some]

/-- The stretch's constants and control facts, carried over the runs after pc 7121. -/
abbrev cHP (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  cuteConsts ++ ctlPF p L g v

/-- **Run 1** (pcs 7142 to 7153). -/
theorem pA3 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 7142
    (pqL2 p L g v) 7154 (expoPS2 p v ++ cHP p L g v) := by
  have hfr := SegD.frame (H := cHP p L g v) Gen.rulesFrame
    (Gen.expoP1_run L g (lookupD (expoPS1 p v))) rfl (by kernel_rfl) (by kernel_rfl)
    (Gen.segFree_range (by kernel_rfl))
  refine seg_of_segD (hfr.weaken_start fun R hR => ?_) (expoP1_ok hp v).1
  have hH : Holds R (cHP p L g v) := by
    have h := holds_lookupD (keys := (cHP p L g v).map Prod.fst) hR (by kernel_rfl)
    rw [show factsFrom ((cHP p L g v).map Prod.fst) (lookupD (pqL2 p L g v)) = cHP p L g v by
      kernel_rfl] at h
    exact h
  refine (holds_append _ _ _).mpr ⟨?_, hH⟩
  rw [expoP1_facts0_eq, show factsFrom ((Gen.expoP1_facts0 (lookupD (expoPS1 p v))).map Prod.fst)
      (lookupD (expoPS1 p v)) = factsFrom ((Gen.expoP1_facts0 (lookupD (expoPS1 p v))).map
        Prod.fst) (lookupD (pqL2 p L g v)) by kernel_rfl]
  exact holds_lookupD hR (by kernel_rfl)


end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
