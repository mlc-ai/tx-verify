-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueSteps

@[expose] public section

/-! # The prologue's broadcasts of the shared base and the warp index

After the shuffle of the shared base the thread computes its linear thread index's warp
(`tid >> 5`) and shuffles it twice from lane 0. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}
  {ins : Instr}

set_option maxHeartbeats 4000000 in
/-- The shuffle of the shared base: lane 0's operand is followed to the warp index. -/
theorem step_shfl0 (hpre : Pre P L mem0) (hs : d.site = .shfl0)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  simp only [Option.elim]
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 L.sharedBase
    · obtain ⟨rfl, rfl⟩ := hv
      right
      have h1 : At (PTX.next (setReg t 337 (.bits 32 (BitVec.ofNat 64 L.sharedBase))))
          (Site.shfl0.pc + 1) (factsAt L g (warpOf L g) (rankOf L g) (Site.shfl0.pc + 1)) :=
        at_next_of (ws := [337]) h (by simp [PTX.next, setReg, h.1]) rfl rfl rfl
          (fun r hr _ => by
            simp only [List.mem_singleton] at hr
            subst hr
            simp only [setReg, PTX.next, Function.update_self]
            pro_values
            simp [sb, b32])
          (fun r hr => by
            simp only [List.mem_singleton] at hr
            simp [setReg, PTX.next, Function.update_of_ne hr])
          (by table_decide)
      have hx := Nat.mod_lt g (show 0 < L.block by rw [hpre.block]; decide)
      obtain ⟨t2, hr, ht⟩ : ∃ t2, run kernel asms L g 8 _ = some t2 ∧
          At t2 Site.shfl1.pc (facts L g ⟨.shfl1⟩) := by
        pro_seg h1 hpre [hpre.block, warpOf]
      exact ⟨.inl ⟨.shfl1⟩, t2, by simp [next], run_rtg hr,
        good_inl ht (inv_of (by simp) (by simp) (by simp) (by simp))⟩
    · left
      simp [next, hv]
  all_goals left; simp [next]

/-- The second shuffle of the warp index: lane 0's operand is followed. -/
theorem step_shfl1 (hs : d.site = .shfl1) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_1)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  simp only [Option.elim]
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g)
    · obtain ⟨rfl, rfl⟩ := hv
      right
      have h1 := at_set (r := 679) h (by pro_values; rfl) (by table_decide)
      exact ⟨.inl ⟨.shfl2⟩, _, by simp [next], .refl,
        good_inl h1 (inv_of (by simp) (by simp) (by simp) (by simp))⟩
    · left
      simp [next, hv]
  all_goals left; simp [next]

/-- A tensor-map prefetch of warp 0, as one step. -/
theorem prefetch_at {t : TState} {pc r base : Nat} {i : String}
    (hc : kernel.code[pc]? = some ⟨none, .prefetchTensorMap true 64 (.reg r)⟩)
    (h : At t pc (factsAt L g 0 (rankOf L g) pc)) (hr : r ∈ Flow.live pc)
    (hv : valueOf L g 0 (rankOf L g) r = .ptr 64 true (.param (param i)) 0)
    (hp : L.paramObjects (param i) = some (mapParam i, base)) (hal : base % 64 = 0)
    (hrange : base + 128 ≤ 2 ^ 64) (hl : ∀ x ∈ Flow.live (pc + 1), x ∈ Flow.live pc)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧
      At t' (pc + 1) (factsAt L g 0 (rankOf L g) (pc + 1)) :=
  ⟨_, run_local hc rfl h (exec_prefetchTensorMap (hv ▸ holds_mem h.2.2.2.2 (mem_factsFrom hr))
      (.inr rfl) hp ⟨rfl, by simp [mapParam, ParamObjectDecl.bytes], by simp [mapParam],
        by simpa [mapParam] using hal, by simpa [mapParam, ParamObjectDecl.bytes] using hrange⟩
        asms_localRule_none (Assumption.SegFreePc.of_eq h.1 hsf)),
    At.mono (At.next h) (holds_factsFrom_mono h.2.2.2.2 hl)⟩

set_option maxHeartbeats 4000000 in
/-- Warp 0 prefetches the four tensor maps, then reaches the first fence. -/
theorem warp0_fence (hpre : Pre P L mem0) {t : TState}
    (h : At t Flow.bra_24 (factsAt L g 0 (rankOf L g) Flow.bra_24)) :
    ∃ k t', run kernel asms L g k t = some t' ∧
      At t' Site.fence0.pc (factsAt L g 0 (rankOf L g) Site.fence0.pc) := by
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 2 t = some t1 ∧
      At t1 (Flow.bra_24 + 2) (factsAt L g 0 (rankOf L g) (Flow.bra_24 + 2)) := by
    pro_seg h hpre
  obtain ⟨t2, hr2, h2⟩ := prefetch_at Flow.code_26 h1 (by table_decide) (by pro_values)
    hpre.paramQ hpre.mapAlignment.1 hpre.mapRange.1 (by table_decide)
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
      At t3 (Flow.bra_24 + 4) (factsAt L g 0 (rankOf L g) (Flow.bra_24 + 4)) := by
    pro_seg h2 hpre
  obtain ⟨t4, hr4, h4⟩ := prefetch_at Flow.code_28 h3 (by table_decide) (by pro_values)
    hpre.paramK hpre.mapAlignment.2.1 hpre.mapRange.2.1 (by table_decide)
  obtain ⟨t5, hr5, h5⟩ : ∃ t5, run kernel asms L g 1 t4 = some t5 ∧
      At t5 (Flow.bra_24 + 6) (factsAt L g 0 (rankOf L g) (Flow.bra_24 + 6)) := by
    pro_seg h4 hpre
  obtain ⟨t6, hr6, h6⟩ := prefetch_at Flow.code_30 h5 (by table_decide) (by pro_values)
    hpre.paramV hpre.mapAlignment.2.2.1 hpre.mapRange.2.2.1 (by table_decide)
  obtain ⟨t7, hr7, h7⟩ : ∃ t7, run kernel asms L g 1 t6 = some t7 ∧
      At t7 (Flow.bra_24 + 8) (factsAt L g 0 (rankOf L g) (Flow.bra_24 + 8)) := by
    pro_seg h6 hpre
  obtain ⟨t8, hr8, h8⟩ := prefetch_at Flow.code_32 h7 (by table_decide) (by pro_values)
    hpre.paramO hpre.mapAlignment.2.2.2 hpre.mapRange.2.2.2 (by table_decide)
  obtain ⟨t9, hr9, h9⟩ : ∃ t9, run kernel asms L g 6 t8 = some t9 ∧
      At t9 Site.fence0.pc (factsAt L g 0 (rankOf L g) Site.fence0.pc) := by
    pro_seg h8 hpre [ctaOf, Nat.and_one_is_mod]
  exact ⟨_, t9, run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
    (run_comp hr1 hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9, h9⟩

set_option maxHeartbeats 4000000 in
/-- The other warps skip the prefetches; warp 12 goes to its election, the others to the first
fence. -/
theorem other_fence (hpre : Pre P L mem0) {t : TState} (hw : warpOf L g ≠ 0)
    (h : At t Flow.bra_24 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_24)) :
    (warpOf L g = 12 → ∃ k t', run kernel asms L g k t = some t' ∧
      At t' Site.elect12.pc (factsAt L g (warpOf L g) (rankOf L g) Site.elect12.pc)) ∧
    (warpOf L g ≠ 12 → ∃ k t', run kernel asms L g k t = some t' ∧
      At t' Site.fence0.pc (factsAt L g (warpOf L g) (rankOf L g) Site.fence0.pc)) := by
  have hwl := warpOf_lt hpre g
  obtain ⟨t1, hr1, h1⟩ := bra_to (b := Flow.bra_24 + 9) (pick := decide (warpOf L g ≠ 0))
    Flow.code_24 h (by table_decide) (by pro_values) (by simp [hw]) (by table_decide)
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
      At t2 Flow.bra_37 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_37) := by
    pro_seg h1 hpre [ctaOf, Nat.and_one_is_mod]
  refine ⟨fun h12 => ?_, fun h12 => ?_⟩
  · obtain ⟨t3, hr3, h3⟩ := bra_to (b := Site.elect12.pc) (pick := decide (warpOf L g ≠ 12))
      Flow.code_37 h2 (by table_decide) (by pro_values) (by simp [h12, Site.pc])
      (by table_decide)
    exact ⟨_, t3, run_comp (run_comp hr1 hr2) hr3, h3⟩
  · obtain ⟨t3, hr3, h3⟩ := bra_to (b := Site.init320.pc + 1) (pick := decide (warpOf L g ≠ 12))
      Flow.code_37 h2 (by table_decide) (by pro_values) (by simp [h12, Site.pc])
      (by table_decide)
    obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 1 t3 = some t4 ∧
        At t4 Site.fence0.pc (factsAt L g (warpOf L g) (rankOf L g) Site.fence0.pc) := by
      pro_seg h3 hpre
    exact ⟨_, t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4, h4⟩

set_option maxHeartbeats 4000000 in
/-- The third shuffle, of the warp index: warp 12 goes to its election, the others to the
first fence (warp 0 after its prefetches). -/
theorem step_shfl2 (hpre : Pre P L mem0) (hs : d.site = .shfl2)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  simp only [Option.elim]
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 (warpOf L g)
    · obtain ⟨rfl, rfl⟩ := hv
      right
      have h1 := at_set (r := 336) h (by pro_values; rfl) (by table_decide)
      have hwl := warpOf_lt hpre g
      obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 _ = some t2 ∧
          At t2 Flow.bra_24 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_24) := by
        pro_seg h1 hpre
      by_cases hw0 : warpOf L g = 0
      · rw [hw0] at h2
        obtain ⟨k, t3, hr3, h3⟩ := warp0_fence hpre h2
        rw [← hw0] at h3
        refine ⟨.inl ⟨.fence0⟩, t3, by simp [next, hw0], run_rtg (run_comp hr2 hr3),
          good_inl h3 (inv_of (by simp) (by simp) (by simp) (by simp))⟩
      · by_cases h12 : warpOf L g = 12
        · obtain ⟨k, t3, hr3, h3⟩ := (other_fence hpre hw0 h2).1 h12
          exact ⟨.inl ⟨.elect12⟩, t3, by simp [next, h12], run_rtg (run_comp hr2 hr3),
            good_inl h3 ⟨fun h => (by rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h), fun _ => h12⟩⟩
        · obtain ⟨k, t3, hr3, h3⟩ := (other_fence hpre hw0 h2).2 h12
          exact ⟨.inl ⟨.fence0⟩, t3, by simp [next, h12], run_rtg (run_comp hr2 hr3),
            good_inl h3 (inv_of (by simp) (by simp) (by simp) (by simp))⟩
    · left
      simp [next, hv]
  all_goals left; simp [next]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
