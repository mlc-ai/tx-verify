-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsP1
public import Lemmas.Flow.SegJump

@[expose] public section

/-! # The end of the first round: the row sum

The first round's closing poll (`pwend .first`, pc 4874), first part: after a successful poll the
row sum (pcs 4877 to 5005) is the generated run `Gen.rsum1_run` over the exponent stretch's
weights; its value is the number `rs1`, at least `0` (`rsum1_float`), which `afterFirst` records;
`pw1_run` takes a successful poll to pc 5006 with the maximum, `%r170`, the row sum and the
control registers. A failed poll returns to the poll (`seg_jmp`). The walk from pc 5006 into the
next round is open (`DECISIONS.md`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (i32 sub32 addi scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof2.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option seg_sym.decideHeartbeats 40000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The row sum -/

/-- The kinds of the row sum's start values: the 128 weights are reals `≥ 0`. -/
def rsum1K : List (Nat × Kd) := (List.range' 1231 128).map fun r => (r, .s .nn)

theorem rsum1_facts0_eq (V : Nat → Value) :
    Gen.rsum1_facts0 V = factsFrom ((Gen.rsum1_facts0 V).map Prod.fst) V := by
  kernel_rfl

/-- The row sum's items read no role function. -/
macro "fns_okrsum1" : tactic => `(tactic| (
  simp only [kFns, XItem.FnOk, Gen.rsum1_items0, Gen.rsum1_items1, Gen.rsum1_items2,
    Gen.rsum1_items3, Gen.rsum1_items4, and_true, true_and]
  repeat' constructor))

/-- The kinds after each piece of the row sum. -/
@[irreducible] def rL1 : List (Nat × Kd) :=
  kList ((Gen.rsum1_facts1 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rsum1K) Gen.rsum1_items0)
@[irreducible] def rL2 : List (Nat × Kd) :=
  kList ((Gen.rsum1_facts2 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rL1) Gen.rsum1_items1)
@[irreducible] def rL3 : List (Nat × Kd) :=
  kList ((Gen.rsum1_facts3 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rL2) Gen.rsum1_items2)
@[irreducible] def rL4 : List (Nat × Kd) :=
  kList ((Gen.rsum1_facts4 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rL3) Gen.rsum1_items3)
@[irreducible] def rL5 : List (Nat × Kd) :=
  kList ((Gen.rsum1_facts5 fun _ => .pred false).map Prod.fst)
    (kOut (kOf rL4) Gen.rsum1_items4)

theorem rsum1_kok (V : Nat → Value) :
    (kOk (kOf rsum1K) Gen.rsum1_items0 &&
      kNext rsum1K Gen.rsum1_items0 ((Gen.rsum1_facts1 V).map Prod.fst) rL1 &&
      kOk (kOf rL1) Gen.rsum1_items1 &&
      kNext rL1 Gen.rsum1_items1 ((Gen.rsum1_facts2 V).map Prod.fst) rL2 &&
      kOk (kOf rL2) Gen.rsum1_items2 &&
      kNext rL2 Gen.rsum1_items2 ((Gen.rsum1_facts3 V).map Prod.fst) rL3 &&
      kOk (kOf rL3) Gen.rsum1_items3 &&
      kNext rL3 Gen.rsum1_items3 ((Gen.rsum1_facts4 V).map Prod.fst) rL4 &&
      kOk (kOf rL4) Gen.rsum1_items4 &&
      kNext rL4 Gen.rsum1_items4 ((Gen.rsum1_facts5 V).map Prod.fst) rL5) = true := by
  unfold rsum1K
  kernel_rfl

theorem rsum1_chain (V1 : Nat → Value)
    (k0 : ∀ r, (kOf rsum1K r).Has (lookupD (Gen.rsum1_facts0 V1) r)) :
    Gen.rsum1_cond V1 ∧ (∀ r, (kOf rL4 r).Has (lookupD (Gen.rsum1_facts4 V1) r)) ∧
      ∀ r, (kOf rL5 r).Has (lookupD (Gen.rsum1_facts5 V1) r) := by
  have h10 := rsum1_kok V1
  have hn5 := (band_split h10).2
  have h9 := (band_split h10).1
  have hk4 := (band_split h9).2
  have h8 := (band_split h9).1
  have hn4 := (band_split h8).2
  have h7 := (band_split h8).1
  have hk3 := (band_split h7).2
  have h6 := (band_split h7).1
  have hn3 := (band_split h6).2
  have h5 := (band_split h6).1
  have hk2 := (band_split h5).2
  have h4 := (band_split h5).1
  have hn2 := (band_split h4).2
  have h3 := (band_split h4).1
  have hk1 := (band_split h3).2
  have h2 := (band_split h3).1
  have hn1 := (band_split h2).2
  have h1 := (band_split h2).1
  have hk0 := h1
  have hG0 : factsFrom ((Gen.rsum1_facts1 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsum1_facts0 V1)) Gen.rsum1_items0) = Gen.rsum1_facts1 V1 := by
    kernel_rfl
  have hf0 : kFns Gen.rsum1_items0 := by fns_okrsum1
  obtain ⟨c0, k1⟩ := kpiece_lit (L := rsum1K) (L' := rL1) (G := Gen.rsum1_facts1 V1)
    (items := Gen.rsum1_items0) hG0 hk0 k0 hf0 hn1
  have hG1 : factsFrom ((Gen.rsum1_facts2 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsum1_facts1 V1)) Gen.rsum1_items1) = Gen.rsum1_facts2 V1 := by
    kernel_rfl
  have hf1 : kFns Gen.rsum1_items1 := by fns_okrsum1
  obtain ⟨c1, k2⟩ := kpiece_lit (L := rL1) (L' := rL2) (G := Gen.rsum1_facts2 V1)
    (items := Gen.rsum1_items1) hG1 hk1 k1 hf1 hn2
  have hG2 : factsFrom ((Gen.rsum1_facts3 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsum1_facts2 V1)) Gen.rsum1_items2) = Gen.rsum1_facts3 V1 := by
    kernel_rfl
  have hf2 : kFns Gen.rsum1_items2 := by fns_okrsum1
  obtain ⟨c2, k3⟩ := kpiece_lit (L := rL2) (L' := rL3) (G := Gen.rsum1_facts3 V1)
    (items := Gen.rsum1_items2) hG2 hk2 k2 hf2 hn3
  have hG3 : factsFrom ((Gen.rsum1_facts4 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsum1_facts3 V1)) Gen.rsum1_items3) = Gen.rsum1_facts4 V1 := by
    kernel_rfl
  have hf3 : kFns Gen.rsum1_items3 := by fns_okrsum1
  obtain ⟨c3, k4⟩ := kpiece_lit (L := rL3) (L' := rL4) (G := Gen.rsum1_facts4 V1)
    (items := Gen.rsum1_items3) hG3 hk3 k3 hf3 hn4
  have hG4 : factsFrom ((Gen.rsum1_facts5 V1).map Prod.fst)
      (xFinal (lookupD (Gen.rsum1_facts4 V1)) Gen.rsum1_items4) = Gen.rsum1_facts5 V1 := by
    kernel_rfl
  have hf4 : kFns Gen.rsum1_items4 := by fns_okrsum1
  obtain ⟨c4, k5⟩ := kpiece_lit (L := rL4) (L' := rL5) (G := Gen.rsum1_facts5 V1)
    (items := Gen.rsum1_items4) hG4 hk4 k4 hf4 hn5
  exact ⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, k4, k5⟩

theorem rsum1K_has (hp : Pre p L m) (v : V) :
    ∀ q ∈ rsum1K, q.2.Has (lookupD (expoE p L g v) q.1) := by
  intro q hq
  simp only [rsum1K, List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  exact (expo1_ok (g := g) hp v).2.2.1 r hr

theorem rsum1_ok (hp : Pre p L m) (v : V) :
    Gen.rsum1_cond (lookupD (expoE p L g v)) ∧
      (∀ r, (kOf rL4 r).Has (lookupD (Gen.rsum1_facts4 (lookupD (expoE p L g v))) r)) := by
  have k0 : ∀ r, (kOf rsum1K r).Has
      (lookupD (Gen.rsum1_facts0 (lookupD (expoE p L g v))) r) := by
    rw [rsum1_facts0_eq]
    exact kstart (by kernel_rfl) (rsum1K_has hp v)
  obtain ⟨hc, hk, -⟩ := rsum1_chain _ k0
  exact ⟨hc, hk⟩

/-- The sum of two reals `≥ 0` is the number value of a real `≥ 0`. -/
theorem add_float {a b : Value} (ha : SK.nn.Has a) (hb : SK.nn.Has b) :
    ∃ r : ℝ, 0 ≤ r ∧ okVal (.bits 32 0) (floatE (addI false) [a, b]) = .float .f32 r := by
  obtain ⟨-, x, hx0, hx⟩ := ha
  obtain ⟨-, y, hy0, hy⟩ := hb
  refine ⟨x + y, add_nonneg hx0 hy0, ?_⟩
  rw [addE_reads hx hy (addEReal_coe x y), erealValue_coe]
  rfl

/-- The row sum's last item gives a number `≥ 0` (for any start values whose kinds hold). -/
theorem rsum1_float_gen (W : Nat → Value)
    (k4 : ∀ r, (kOf rL4 r).Has (lookupD (Gen.rsum1_facts4 W) r)) :
    ∃ r : ℝ, 0 ≤ r ∧ Gen.rsum1_v5005 W = .float .f32 r := by
  have h0 := k4 3952
  have h1 := k4 3953
  rw [show kOf rL4 3952 = .s .nn by kernel_rfl] at h0
  rw [show kOf rL4 3953 = .s .nn by kernel_rfl] at h1
  exact add_float h0 h1

/-- **The first round's row sum** is the number `rs1`, at least `0`. -/
theorem rsum1_float (hp : Pre p L m) (v : V) :
    Gen.rsum1_v5005 (lookupD (expoE p L g v)) = .float .f32 (rs1 p L g v) ∧
      0 ≤ rs1 p L g v := by
  obtain ⟨r, hr0, e⟩ := rsum1_float_gen _ (rsum1_ok (g := g) hp v).2
  have : rs1 p L g v = r := by unfold rs1; rw [e]; rfl
  rw [this]
  exact ⟨e, hr0⟩

/-! ### The successful poll, to the loop entry -/

theorem lookup_snd {a b : Nat} {x y : Value} {l : List (Nat × Value)} (h : (b == a) = false) :
    ((a, x) :: (b, y) :: l).lookup b = some y := by
  simp [List.lookup, h]

theorem vExpo1_7256 (v : V) : vExpo1 p L g v 7256 = Assumption.erealValue .f32 (foldF p L g v) := by
  unfold vExpo1
  rw [valuesNarr1, List.cons_append, List.cons_append, lookup_snd (by decide), Option.getD_some]

theorem vExpo1_1230 (v : V) : vExpo1 p L g v 1230 = negS p := by
  have hn : (valuesNarr1 p L g v).lookup 1230 = none := by
    rw [List.lookup_eq_none_iff]
    have hk : ((valuesNarr1 p L g v).map Prod.fst).contains 1230 = false := by kernel_rfl
    rintro ⟨a, x⟩ hq
    simp only [bne_iff_ne, ne_eq]
    intro e
    subst e
    have := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Prod.fst) hq)
    rw [hk] at this
    cases this
  unfold vExpo1
  rw [List.lookup_append, hn, Option.none_or]
  rfl

theorem expo1_7256 (V : Nat → Value) : lookupD (Gen.expo1_facts14 V) 7256 = V 7256 := by
  kernel_rfl
theorem expo1_1230 (V : Nat → Value) : lookupD (Gen.expo1_facts14 V) 1230 = V 1230 := by
  kernel_rfl

/-- **From the successful poll to pc 5006**: the branch to the row sum and the row sum; the
maximum, `%r170` and the control registers carried. -/
theorem pw1_run (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 4875
    ((9753, .pred true) :: factsD p L g ⟨.pwend .first, v, 0, []⟩) 5006
    ((7257, .float .f32 (rs1 p L g v)) ::
      ((7256, Assumption.erealValue .f32 (foldF p L g v)) :: (1230, negS p) ::
        factsFrom (ctlLive 5006) (valueOf p L g ⟨.pwend .first, v, 0, []⟩))) := by
  have hb := Seg.bra (K := kernel) (A := Assumptions.all) (L := L) (g := g) (uni := true)
    (pick := true) (F := (9753, .pred true) :: factsD p L g ⟨.pwend .first, v, 0, []⟩)
    Flow.code_4875 (List.mem_cons_self) (fun t _ a ha => by
      simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (Gen.segFree _ (by kernel_rfl))
  have hfr := SegD.frame
    (H := (7256, Assumption.erealValue .f32 (foldF p L g v)) :: (1230, negS p) ::
      factsFrom (ctlLive 5006) (valueOf p L g ⟨.pwend .first, v, 0, []⟩)) Gen.rulesFrame
    (Gen.rsum1_run L g (lookupD (expoE p L g v))) rfl (by kernel_rfl) (by kernel_rfl)
    (Gen.segFree_range (by kernel_rfl))
  have hd : valuesData p L g ⟨.pwend .first, v, 0, []⟩ =
      p1Data p L g (⟨.pwend .first, v, 0, []⟩ : D).v := rfl
  refine Seg.comp_ex ⟨1, hb⟩ (seg_of_segD (hfr.weaken_start ?_ |>.weaken_end ?_)
    (rsum1_ok hp v).1)
  · intro R hR
    have hR' := hR.2
    have hc : Holds R (factsFrom (ctlLive 5006) (valueOf p L g ⟨.pwend .first, v, 0, []⟩)) := by
      have hs := holds_sub (keys := ctlLive 5006) hR' (by kernel_rfl)
      refine holds_of_pointwise fun r hr => ?_
      rw [← valueOfD_ctl _ (List.mem_filter.mp hr).2]
      exact holds_mem hs (mem_factsFrom hr)
    refine (holds_append _ _ _).mpr ⟨?_, ?_, ?_, hc⟩
    · rw [rsum1_facts0_eq]
      refine holds_of_pointwise fun r hr => ?_
      have hk : ((Gen.rsum1_facts0 (lookupD (expoE p L g v))).map Prod.fst).all
          (fun r => ((expoE p L g v).map Prod.fst).contains r &&
            (liveD (livePc ⟨.pwend .first, v, 0, []⟩)).contains r) = true := by
        unfold expoE; kernel_rfl
      have h := List.all_eq_true.mp hk r hr
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      rw [← valueOfD_p1 hd h.1]
      exact holds_mem hR' (mem_factsFrom h.2)
    · have hk : (liveD (livePc ⟨.pwend .first, v, 0, []⟩)).contains 7256 = true := by kernel_rfl
      have h := holds_mem hR' (mem_factsFrom (List.contains_iff_mem.mp hk))
      rw [valueOfD_p1 hd (by unfold expoE; exact List.contains_iff_mem.mp (by kernel_rfl)),
        expoE, expo1_7256, vExpo1_7256] at h
      exact h
    · have hk : (liveD (livePc ⟨.pwend .first, v, 0, []⟩)).contains 1230 = true := by kernel_rfl
      have h := holds_mem hR' (mem_factsFrom (List.contains_iff_mem.mp hk))
      rw [valueOfD_p1 hd (by unfold expoE; exact List.contains_iff_mem.mp (by kernel_rfl)),
        expoE, expo1_1230, vExpo1_1230] at h
      exact h
  · intro R hR
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    refine ⟨?_, h2⟩
    have := h1.1
    rw [(rsum1_float (g := g) hp v).1] at this
    exact this

/-! ### The step -/

theorem foldF_cases (p : Params) (L : Launch) (g : Nat) (v : V) :
    foldF p L g v = ⊥ ∨ ∃ r : ℝ, foldF p L g v = r := by
  by_cases hb : foldF p L g v = ⊥
  · exact .inl hb
  · exact .inr ⟨_, (EReal.coe_toReal (foldF_lt_top p L g v).ne hb).symm⟩

theorem finE_bot : finE ⊥ = false := by simp [finE]
theorem finE_coe (r : ℝ) : finE r = true := by simp [finE]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
