-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsKeepB2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBarr1

@[expose] public section

/-! # The bias round from its bias-slot arrival

The generated products and maximum lead from pc 5279 to the statistics store. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (andi scmpi)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The bias round's arrival state. -/
abbrev barrB (v : V) : D := ⟨.barr true, v, 0, []⟩

/-- The registers of the round's running values that the pieces carry. -/
def runK : List Nat := [7251, 7257, 1230]

/-- The products' registers. -/
def prodK : List Nat := (List.range 64).map fun j => 8317 + 2 * j

theorem valueOf_barrB_statB (v : V) : valueOf p L g (barrB v) = valueOf p L g (statB v) := rfl

theorem runK_barrB_statB (v : V) : ∀ r ∈ runK,
    valueOfD p L g (barrB v) r = valueOfD p L g (statB v) r := by
  intro r hr
  simp only [runK, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rfl

/-- The round-index test (pc 5535). -/
theorem idxB (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 5535
    (factsFrom (ctlLive 5535) (valueOfD p L g (barrB v))) 5536
    (factsFrom (ctlLive 5536) (valueOfD p L g (barrB v))) := by
  have hparams := params hp
  seg_sym using (soft_seg)

theorem prodB_pairs_eq (p : Params) (v : V) :
    ((7896, joinValue (.bits 32 (Epilogue.paramW p.invScaleBits))
      (.bits 32 (Epilogue.paramW p.invScaleBits))) ::
      (List.range 64).map fun j => (8317 + 2 * j,
        Value.pair (bvl (bpf v (2 * j)) (bps p v (2 * j)))
          (bvl (bpf v (2 * j + 1)) (bps p v (2 * j + 1))))) =
    (7896, joinValue (.bits 32 (Epilogue.paramW p.invScaleBits))
      (.bits 32 (Epilogue.paramW p.invScaleBits))) ::
      (List.range 64).map fun j => (8317 + 2 * j,
        Value.pair (bvl (bpf v (2 * j)) (bps p v (2 * j)))
          (bvl (bpf v (2 * j + 1)) (bps p v (2 * j + 1)))) := rfl

/-- The products' facts at pc 5535 as the statistics store's table states them. -/
theorem prods_statB (hp : Pre p L m) (v : V) {R : Nat → Option Value}
    (h : Holds R (Gen.prodB_facts8 (vProdB p L g v))) :
    Holds R (factsFrom prodK (valueOfD p L g (statB v))) := by
  have hP := prodB_pairs (g := g) hp v R h
  have hP' : Holds R ((List.range 64).map fun j => (8317 + 2 * j,
      Value.pair (bvl (bpf v (2 * j)) (bps p v (2 * j)))
        (bvl (bpf v (2 * j + 1)) (bps p v (2 * j + 1))))) := (cast (congrArg (Holds R)
    (show _ = (7896, joinValue (.bits 32 (Epilogue.paramW p.invScaleBits))
      (.bits 32 (Epilogue.paramW p.invScaleBits))) :: (List.range 64).map fun j => (8317 + 2 * j,
        Value.pair (bvl (bpf v (2 * j)) (bps p v (2 * j)))
          (bvl (bpf v (2 * j + 1)) (bps p v (2 * j + 1)))) from rfl)) hP).2
  refine holds_of_pointwise fun r hr => ?_
  simp only [prodK, List.mem_map, List.mem_range] at hr
  obtain ⟨j, hj, rfl⟩ := hr
  rw [statB_prod v hj]
  exact holds_mem hP' (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- **From pc 5279 to the maximum** (pc 5666). -/
theorem chainB1 (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 5279
    (factsFrom (liveD 5279) (valueOfD p L g (barrB v))) 5666
    ((4560, erealValue .f32 (foldBE p v)) ::
      factsFrom (ctlLive 5536) (valueOfD p L g (barrB v)) ++
      factsFrom (runK ++ prodK) (valueOfD p L g (statB v))) := by
  have p1 := seg_frame (lo := 5279) (hi := 5682)
    (H := factsFrom (ctlLive 5279) (valueOfD p L g (barrB v)) ++
      factsFrom runK (valueOfD p L g (barrB v)))
    (seg_of_segD (Gen.prodB_run L g (vProdB p L g v)) (prodB_ok hp v))
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  have p2 := seg_frame (lo := 5535) (hi := 5682)
    (H := factsFrom (runK ++ prodK) (valueOfD p L g (statB v)))
    (idxB (g := g) hp v) (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  have p3 := seg_frame (lo := 5536) (hi := 5682)
    (H := factsFrom (ctlLive 5536) (valueOfD p L g (barrB v)) ++
      factsFrom (runK ++ prodK) (valueOfD p L g (statB v)))
    (seg_of_segD (Gen.maxB_run L g (valueOfD p L g (statB v))) (maxB_ok v))
    (by kernel_rfl) (by kernel_rfl) (by omega) (by omega)
  -- 5279
  refine Seg.comp_ex (seg_start_ex p1 fun R hR => (holds_append _ _ _).mpr
    ⟨by rw [prodB_facts0_eq]; exact holds_sub hR (by kernel_rfl),
      (holds_append _ _ _).mpr ⟨holds_sub hR (by kernel_rfl), holds_sub hR (by kernel_rfl)⟩⟩) ?_
  -- 5535
  refine Seg.comp_ex (seg_start_ex p2 fun R hR => by
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    obtain ⟨h2, h3⟩ := (holds_append _ _ _).mp h2
    refine (holds_append _ _ _).mpr ⟨holds_sub h2 (by kernel_rfl), ?_⟩
    have hp' := prods_statB (g := g) hp v h1
    refine holds_of_pointwise fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · rw [← runK_barrB_statB v r hr]; exact holds_mem h3 (mem_factsFrom hr)
    · exact holds_mem hp' (mem_factsFrom hr)) ?_
  -- 5536
  refine Seg.comp_ex (seg_start_ex p3 fun R hR => by
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
    refine (holds_append _ _ _).mpr ⟨?_, (holds_append _ _ _).mpr ⟨h1, h2⟩⟩
    rw [maxB_facts0_eq]
    exact holds_sub h2 (by kernel_rfl)) ?_
  -- 5666
  refine ⟨0, Seg.refl _ _ |>.weaken_end fun R hR => ?_⟩
  obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp hR
  simp only [Gen.maxB_facts5, holds_cons, holds_nil, and_true] at h1
  exact ⟨by rw [h1, maxB_val], h2⟩

/-- The keep test's start facts from the facts at the maximum. -/
theorem keepStart_of (v : V) {R : Nat → Option Value} {X : Value}
    (h : Holds R ((4560, X) :: factsFrom (ctlLive 5536) (valueOfD p L g (barrB v)) ++
      factsFrom (runK ++ prodK) (valueOfD p L g (statB v)))) :
    Holds R ((4560, X) :: keepStart p L g v) := by
  obtain ⟨h0, h⟩ := h
  obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp h
  refine ⟨h0, holds_of_pointwise fun r hr => ?_⟩
  have hk : startKeys.all (fun r => (ctlLive 5536).contains r || (runK ++ prodK).contains r) =
      true := by kernel_rfl
  have := List.all_eq_true.mp hk r hr
  simp only [Bool.or_eq_true, List.contains_iff_mem] at this
  rcases this with hc | hd
  · have hct : ctl r = true := by
      have : (ctlLive 5536).all ctl = true := by kernel_rfl
      exact List.all_eq_true.mp this r hc
    rw [valueOfD_ctl _ hct, ← valueOf_barrB_statB, ← valueOfD_ctl _ hct]
    exact holds_mem h1 (mem_factsFrom hc)
  · exact holds_mem h2 (mem_factsFrom hd)

/-- The statistics store's facts from the updated values of a walk with a `-∞` maximum before
the round. -/
theorem factsD_of_keepW {v : V} {a b c : Value} {R : Nat → Option Value}
    (ha : valueOfD p L g (statB v) 7256 = a) (hb : valueOfD p L g (statB v) 4565 = b)
    (hc : valueOfD p L g (statB v) 1362 = c)
    (h : Holds R (factsFrom (liveD 5682) (keepW p L g v a b c))) :
    Holds R (factsD p L g (statB v)) := by
  have he : keepW p L g v a b c = valueOfD p L g (statB v) := by
    funext r
    simp only [keepW]
    by_cases e1 : r = 1362
    · subst e1; rw [Function.update_self, hc]
    rw [Function.update_of_ne e1]
    by_cases e2 : r = 4565
    · subst e2; rw [Function.update_self, hb]
    rw [Function.update_of_ne e2]
    by_cases e3 : r = 7256
    · subst e3; rw [Function.update_self, ha]
    rw [Function.update_of_ne e3]
  rw [he] at h
  exact h

theorem statB_7256 (v : V) : valueOfD p L g (statB v) 7256 =
    bif v.mf then (if keepB p v = true then .float .f32 v.mr else .float .f32 (foldBR p v))
      else erealValue .f32 (foldBE p v) := rfl

theorem statB_4565 (v : V) : valueOfD p L g (statB v) 4565 =
    bif v.mf then (if keepB p v = true then .float .f32 v.mr else .float .f32 (foldBR p v))
      else (if foldBE p v = ⊥ then .bits 32 (BitVec.ofNat 64 0)
        else erealValue .f32 (foldBE p v)) := rfl

theorem statB_1362 (v : V) : valueOfD p L g (statB v) 1362 =
    bif v.mf then (if keepB p v = true then .bits 32 (BitVec.ofNat 64 1065353216)
        else .float .f32 (Real.rpow 2 ((scl p : ℝ) * (v.mr + -foldBR p v))))
      else .float .f32 0 := rfl

/-- **From pc 5279 to the bias round's statistics store.** -/
theorem chainB (hp : Pre p L m) (v : V) : ∃ n, Seg kernel Assumptions.all L g n 5279
    (factsFrom (liveD 5279) (valueOfD p L g (barrB v))) 5682 (factsD p L g (statB v)) := by
  refine Seg.comp_ex (chainB1 hp v) ?_
  obtain ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, mf, mr, rs⟩ := v
  cases mf
  · -- `-∞` before the round
    set v0 : V := ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, false, mr, rs⟩ with hv0
    have hlt := foldBE_lt_top p v0
    by_cases hb : foldBE p v0 = ⊥
    · obtain ⟨n, h⟩ := keep_fb (g := g) hp sc ukw nb bt bpar spar ppar pl sv bk br mr rs
      refine ⟨n, (h.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
      · have := keepStart_of _ hR
        rwa [hb, erealValue_bot] at this
      · refine factsD_of_keepW ?_ ?_ ?_ hR
        · rw [statB_7256, hb, erealValue_bot]; rfl
        · rw [statB_4565, ite_eq_left_of_eq_true _ _ (eq_true hb)]; rfl
        · rw [statB_1362]; rfl
    · have hX : foldBE p v0 = ((foldBR p v0 : ℝ) : EReal) :=
        (EReal.coe_toReal hlt.ne hb).symm
      obtain ⟨n, h⟩ := keep_fr (g := g) hp sc ukw nb bt bpar spar ppar pl sv bk br mr rs
        (foldBR p v0)
      refine ⟨n, (h.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
      · have := keepStart_of _ hR
        rwa [hX, erealValue_coe] at this
      · refine factsD_of_keepW ?_ ?_ ?_ hR
        · rw [statB_7256, hX, erealValue_coe]; rfl
        · rw [statB_4565, ite_eq_right_of_eq_false _ _ (eq_false hb), hX, erealValue_coe]; rfl
        · rw [statB_1362]; rfl
  · have hX := foldBE_real (p := p) (v := ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br,
      true, mr, rs⟩) rfl
    obtain ⟨n, h⟩ := keep_t (g := g) hp sc ukw nb bt bpar spar ppar pl sv bk br mr rs
    exact ⟨n, h.weaken_start fun R hR => by
      have := keepStart_of _ hR
      rwa [hX, erealValue_coe] at this⟩

/-! ### The steps -/

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
