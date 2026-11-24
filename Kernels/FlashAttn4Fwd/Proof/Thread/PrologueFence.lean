-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueSteps

@[expose] public section

/-! # Warp 12's election and the first fence

Warp 12 elects a lane that initializes the handshake barrier; every thread fences the
initializations. After the fence warp 0 goes to its first election; the other warps pass the
tests for warp 0 to the shuffle of the cluster rank. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}
  {ins : Instr}

set_option maxHeartbeats 4000000 in
/-- Warp 12's election: its leader goes to the initialization, the other lanes to the fence. -/
theorem step_elect12 (hpre : Pre P L mem0) (hs : d.site = .elect12) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  have hw := hi.warp12 (.inl rfl)
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  right
  have h1 := at_elect (d := 681) (p := 3) (x := .bits 32 (BitVec.ofNat 64 ld))
    (b := laneOf L g == ld) h (by table_decide) (by table_decide)
  cases hb : (laneOf L g == ld)
  · rw [hb] at h1
    have hne : laneOf L g ≠ ld := by simpa using hb
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 3 _ = some t2 ∧
        At t2 Site.fence0.pc (facts L g ⟨.fence0⟩) := by
      pro_seg h1 hpre
    exact ⟨.inl ⟨.fence0⟩, t2, by simp [next, hne], run_rtg hr2,
      good_inl h2 (inv_of (by simp) (by simp) (by simp) (by simp))⟩
  · rw [hb] at h1
    have heq : laneOf L g = ld := by simpa using hb
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 3 _ = some t2 ∧
        At t2 Site.init320.pc (facts L g ⟨.init320⟩) := by
      pro_seg h1 hpre
    exact ⟨.inl ⟨.init320⟩, t2, by simp [next, heq], run_rtg hr2,
      good_inl h2 ⟨fun h => (by rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h), fun _ => hw⟩⟩

set_option maxHeartbeats 4000000 in
/-- The handshake barrier's initialization, then the fence. -/
theorem step_init320 (hpre : Pre P L mem0) (hs : d.site = .init320)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarInit_0)
  obtain rfl := fires_next (show AdvancesOp (.mbarInit _ _ _) from trivial) hf
  right
  have h1 := At.next h
  have hwl := warpOf_lt hpre g
  obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 (PTX.next t) = some t2 ∧
      At t2 Site.fence0.pc (facts L g ⟨.fence0⟩) := by
    pro_seg h1 hpre
  exact ⟨.inl ⟨.fence0⟩, t2, by simp [next], run_rtg hr2,
    good_inl h2 (inv_of (by simp) (by simp) (by simp) (by simp))⟩

set_option maxHeartbeats 4000000 in
/-- The first fence: warp 0 goes to its first election, the other warps to the shuffle of the
cluster rank. -/
theorem step_fence0 (hpre : Pre P L mem0) (hs : d.site = .fence0)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0)
  obtain rfl := fires_next (show AdvancesOp .fenceMbarInit from trivial) hf
  right
  have h1 := At.next h
  have hwl := warpOf_lt hpre g
  by_cases hw : warpOf L g = 0
  · obtain ⟨t2, hr2, h2⟩ := bra_to (b := (Site.elect 0).pc) (pick := decide (warpOf L g ≠ 0))
      Flow.code_45 h1 (by table_decide) (by pro_values) (by simp [hw, Site.pc]; rfl)
      (by table_decide)
    exact ⟨.inl ⟨.elect 0⟩, t2, by simp [next, hw], run_rtg hr2,
      good_inl h2 ⟨fun _ => hw, fun h => (by rcases h with h | h <;> cases h)⟩⟩
  · obtain ⟨t2, hr2, h2⟩ := bra_to (b := Flow.mbarInit_2 + 1) (pick := decide (warpOf L g ≠ 0))
      Flow.code_45 h1 (by table_decide) (by pro_values) (by simp [hw]) (by table_decide)
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 2 t2 = some t3 ∧
        At t3 Flow.bra_54 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_54) := by
      pro_seg h2 hpre
    obtain ⟨t4, hr4, h4⟩ := bra_to (b := Flow.mbarInit_4 + 1) (pick := decide (warpOf L g ≠ 0))
      Flow.code_54 h3 (by table_decide) (by pro_values) (by simp [hw]) (by table_decide)
    obtain ⟨t5, hr5, h5⟩ : ∃ t5, run kernel asms L g 2 t4 = some t5 ∧
        At t5 Site.shfl3.pc (facts L g ⟨.shfl3⟩) := by
      pro_seg h4 hpre [rankOf, ctaOf, Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, hpre.cluster]
    exact ⟨.inl ⟨.shfl3⟩, t5, by simp [next, hw],
      run_rtg (run_comp (run_comp (run_comp hr2 hr3) hr4) hr5),
      good_inl h5 (inv_of (by simp) (by simp) (by simp) (by simp))⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
