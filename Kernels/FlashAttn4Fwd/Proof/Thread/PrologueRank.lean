-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueSteps

@[expose] public section

/-! # The shuffle of the cluster rank

Every thread broadcasts its cluster rank from lane 0 and computes the multicast mask
`(1 << r % 2) | (1 << (r % 2 ^ 1))` (`3`) and, later, the leader's rank `r / 2 * 2` (`0`); both
are evaluated in the two cases of the rank. Warp 0 then goes to its third election; the other
warps pass every test for warp 0 to the second fence. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}
  {ins : Instr}

theorem rank_cases (hpre : Pre P L mem0) (g : Nat) : rankOf L g = 0 ∨ rankOf L g = 1 := by
  rw [rankOf_eq hpre]
  omega

set_option maxHeartbeats 4000000 in
/-- The warps other than warp 0 pass every test for warp 0 to the second fence. -/
theorem other_fence1 (hpre : Pre P L mem0) {t : TState} (hw : warpOf L g ≠ 0)
    (h : At t (Site.shfl3.pc + 1) (factsAt L g (warpOf L g) (rankOf L g) (Site.shfl3.pc + 1))) :
    ∃ k t', run kernel asms L g k t = some t' ∧
      At t' Site.fence1.pc (factsAt L g (warpOf L g) (rankOf L g) Site.fence1.pc) := by
  have hwl := warpOf_lt hpre g
  have hb : ∀ {pc target p : Nat} {t : TState}
      (_ : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
      (_ : At t pc (factsAt L g (warpOf L g) (rankOf L g) pc)) (_ : p ∈ Flow.live pc)
      (_ : valueOf L g (warpOf L g) (rankOf L g) p = .pred (decide (warpOf L g ≠ 0)))
      (_ : ∀ r ∈ Flow.live target, r ∈ Flow.live pc)
      (_ : Assumption.SegFreePc asms pc := by seg_free_pc),
      ∃ t', run kernel asms L g 1 t = some t' ∧
        At t' target (factsAt L g (warpOf L g) (rankOf L g) target) :=
    fun hc h hp hv hl hsf => bra_to hc h hp hv (by simp [hw]) hl hsf
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 10 t = some t1 ∧
      At t1 Flow.bra_74 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_74) := by
    rcases rank_cases hpre g with hr | hr <;> (rw [hr] at h ⊢; pro_seg h hpre)
  obtain ⟨t2, hr2, h2⟩ := hb Flow.code_74 h1 (by table_decide) (by pro_values) (by table_decide)
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 2 t2 = some t3 ∧
      At t3 Flow.bra_87 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_87) := by
    pro_seg h2 hpre
  obtain ⟨t4, hr4, h4⟩ := hb Flow.code_87 h3 (by table_decide) (by pro_values) (by table_decide)
  obtain ⟨t5, hr5, h5⟩ : ∃ t5, run kernel asms L g 2 t4 = some t5 ∧
      At t5 Flow.bra_106 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_106) := by
    pro_seg h4 hpre
  obtain ⟨t6, hr6, h6⟩ := hb Flow.code_106 h5 (by table_decide) (by pro_values) (by table_decide)
  obtain ⟨t7, hr7, h7⟩ : ∃ t7, run kernel asms L g 9 t6 = some t7 ∧
      At t7 Flow.bra_122 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_122) := by
    rcases rank_cases hpre g with hr | hr <;> (rw [hr] at h6 ⊢; pro_seg h6 hpre)
  obtain ⟨t8, hr8, h8⟩ := hb Flow.code_122 h7 (by table_decide) (by pro_values) (by table_decide)
  obtain ⟨t9, hr9, h9⟩ : ∃ t9, run kernel asms L g 2 t8 = some t9 ∧
      At t9 Flow.bra_131 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_131) := by
    pro_seg h8 hpre
  obtain ⟨t10, hr10, h10⟩ := hb Flow.code_131 h9 (by table_decide) (by pro_values)
    (by table_decide)
  obtain ⟨t11, hr11, h11⟩ : ∃ t11, run kernel asms L g 1 t10 = some t11 ∧
      At t11 Flow.bra_145 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_145) := by
    pro_seg h10 hpre
  obtain ⟨t12, hr12, h12⟩ := hb Flow.code_145 h11 (by table_decide) (by pro_values)
    (by table_decide)
  obtain ⟨t13, hr13, h13⟩ : ∃ t13, run kernel asms L g 3 t12 = some t13 ∧
      At t13 Flow.bra_161 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_161) := by
    pro_seg h12 hpre
  obtain ⟨t14, hr14, h14⟩ := hb Flow.code_161 h13 (by table_decide) (by pro_values)
    (by table_decide)
  obtain ⟨t15, hr15, h15⟩ : ∃ t15, run kernel asms L g 2 t14 = some t15 ∧
      At t15 Flow.bra_176 (factsAt L g (warpOf L g) (rankOf L g) Flow.bra_176) := by
    pro_seg h14 hpre
  obtain ⟨t16, hr16, h16⟩ := hb Flow.code_176 h15 (by table_decide) (by pro_values)
    (by table_decide)
  exact ⟨_, t16, run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
    (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp hr1 hr2)
    hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12) hr13) hr14) hr15) hr16, h16⟩

set_option maxHeartbeats 4000000 in
/-- The shuffle of the cluster rank: lane 0's operand is followed, to warp 0's third election
or to the second fence. -/
theorem step_shfl3 (hpre : Pre P L mem0) (hs : d.site = .shfl3)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_3)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  simp only [Option.elim]
  cases recv
  case bits wd v =>
    by_cases hv : wd = 32 ∧ v = BitVec.ofNat 64 (rankOf L g)
    · obtain ⟨rfl, rfl⟩ := hv
      right
      have h1 := at_set (r := 339) (v := .bits 32 (BitVec.ofNat 64 (rankOf L g))) h
        (by pro_values; rfl) (by table_decide)
      generalize PTX.next (setReg t 339 (.bits 32 (BitVec.ofNat 64 (rankOf L g)))) = u1 at h1 ⊢
      by_cases hw : warpOf L g = 0
      · rw [hw] at h1
        obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 11 u1 = some t2 ∧
            At t2 (Site.elect 2).pc (factsAt L g 0 (rankOf L g) (Site.elect 2).pc) := by
          rcases rank_cases hpre g with hr | hr <;> (rw [hr] at h1 ⊢; pro_seg h1 hpre)
        rw [← hw] at h2
        exact ⟨.inl ⟨.elect 2⟩, t2, by simp [next, hw], run_rtg hr2,
          good_inl h2 ⟨fun _ => hw, fun h => (by rcases h with h | h <;> cases h)⟩⟩
      · obtain ⟨k, t2, hr2, h2⟩ := other_fence1 hpre hw h1
        exact ⟨.inl ⟨.fence1⟩, t2, by simp [next, hw], run_rtg hr2,
          good_inl h2 (inv_of (by simp) (by simp) (by simp) (by simp))⟩
    · left
      simp [next, hv]
  all_goals left; simp [next]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
