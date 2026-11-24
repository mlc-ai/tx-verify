-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarAll

@[expose] public section

/-! # `Cross.BarSched`: every named barrier's per-warp schedule

Each participant warp's events on barrier `id` are at the times of `barS L id` (`barCollSched`),
and a thread's `bar.sync` is no earlier than the other participants' events of its ordinal
(`barSync`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- A followed state's events on each barrier, for a participant. -/
theorem barCnt_eq {g k id : Nat} {d : ThreadD} (hg : g < L.threads)
    (hG : BarGroup id (warpOf L g)) (hk : k ≤ (X.tr g).length) (hσ : St L X g k = some (some d)) :
    ((X.tr g).take k).countP (Execution.isBarId id) = barCnt L g id d := by
  obtain ⟨hJ, -, hw⟩ := state_facts hpre hX ht hok hg hk hσ
  have hlt := barGroup_lt hG
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', m, rfl⟩ | ⟨hw', -⟩ |
      ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
  · exact prologue_not_bar hJ.1 id
  · omega
  · omega
  · exact mma_barCnt hpre hX ht hw' hJ
  · omega
  · exact soft_barCnt hpre hX ht hw' hJ
  · exact corr_barCnt hpre hX ht hw' hw'' hJ

/-- **Each participant warp's events on barrier `id` are on its schedule.** -/
theorem barCollSched (id : Nat) :
    Sched.CollSched (timed L) X (Execution.isBarId id) (warpKey L)
      (fun g => BarGroup id (warpOf L g)) (barS L id) := by
  have hn : 0 < Work.n L := Mma.trips_pos hpre
  refine Sched.collSched_of (fun g d => barCnt L g id d) (fun g d => barIdOf L g d == some id)
    (fun hg hG hk hσ => barCnt_eq hpre hX ht hok hg hG hk hσ)
    (fun hg _ hσ he => fired_barId hpre hX ht hok hg hσ he) ?_ (barS_mono L id)
  intro g k d hg hG hk hσ
  obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
  have hlt := barGroup_lt hG
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', m, rfl⟩ | ⟨hw', -⟩ |
      ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
  · refine ⟨fun h => absurd h (by simp [barIdOf]), fun _ => ?_⟩
    have := Progress.Time.prologue_lt_reg p.site
    have := barS_ge L id (warpKey L g) (barCnt L g id (.inl p))
    simp only [stateTime]
    simp only [regT, bar0T] at *
    omega
  · omega
  · omega
  · have h2 := barGroup_mma (hw' ▸ hG)
    subst h2
    have hh := Mma.b2_time hpre (g := g) (d := m) (by simp at hinv; exact hinv.1)
    have hS : barS L 2 (warpKey L g) = b2M (Work.n L) (Work.T L g) := by
      funext k; simp [barS, warpKey, hw', T_eq]
    simp only [stateTime, barCnt, ↓reduceIte, mma_isB2, hS]
    exact hh
  · omega
  · have hst : warpOf L g / 4 < 2 := by omega
    have hinv' : Softmax.Inv L g s := hinv
    rcases barGroup_soft hG hw' with rfl | rfl
    · have hh := Soft.b2_time hn hinv' hst
      have hS : barS L 2 (warpKey L g) = b2S (Work.n L) (Work.T L g) := by
        funext k; simp [barS, warpKey, hw', T_eq]
      have h3 : ¬ (2 = warpOf L g + 3) := by omega
      simp only [stateTime, barCnt, ↓reduceIte, h3, Nat.add_zero, soft_isB2, hS]
      exact hh
    · have hh := Soft.gen_time hn hinv' hst
      have h2 : ¬ (warpOf L g + 3 = 2) := by omega
      have hS : barS L (warpOf L g + 3) (warpKey L g) =
          statS (Work.n L) (Work.T L g) (bandS (warpOf L g / 4) + 22) 0 := by
        funext k; simp [barS, warpKey, hw', h2, T_eq]
      simp only [stateTime, barCnt, ↓reduceIte, h2, Nat.zero_add, soft_isGen, hS]
      exact hh
  · have hinv' : Correction.Inv L g c := hinv
    rcases barGroup_corr hG hw' hw'' with rfl | rfl | rfl
    · have hh := Corr.b2_time hinv'
      have hS : barS L 2 (warpKey L g) = b2S (Work.n L) (Work.T L g) := by
        funext k
        have : ¬ warpOf L g < 8 := by omega
        simp [barS, warpKey, this, hw'', T_eq]
      have h5 : ¬ (2 = warpOf L g - 5) := by omega
      have h1 : ¬ (2 = warpOf L g - 1) := by omega
      simp only [stateTime, barCnt, ↓reduceIte, h5, h1, Nat.add_zero, corr_isB2 L g c hw', hS]
      exact hh
    · have hh := Corr.sync_time hn hinv' (st := 0) (by decide)
      have h2 : ¬ (warpOf L g - 5 = 2) := by omega
      have h1 : ¬ (warpOf L g - 5 = warpOf L g - 1) := by omega
      have hS : barS L (warpOf L g - 5) (warpKey L g) =
          statS (Work.n L) (Work.T L g) (bandC 0) 2 := by
        funext k
        have : ¬ warpOf L g < 8 := by omega
        simp [barS, warpKey, this, hw'', h2, T_eq]
      have hc := corr_isSync L g c hw' 0 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero] at hc
      simp only [stateTime, barCnt, ↓reduceIte, h2, h1, Nat.add_zero, Nat.zero_add, hc, hS]
      exact hh
    · have hh := Corr.sync_time hn hinv' (st := 1) (by decide)
      have h2 : ¬ (warpOf L g - 1 = 2) := by omega
      have h5 : ¬ (warpOf L g - 1 = warpOf L g - 5) := by omega
      have hS : barS L (warpOf L g - 1) (warpKey L g) =
          statS (Work.n L) (Work.T L g) (bandC 1) 2 := by
        funext k
        have : ¬ warpOf L g < 8 := by omega
        simp [barS, warpKey, this, hw'', h2, h5, T_eq]
      have hc := corr_isSync L g c hw' 1 (by decide)
      rw [show warpOf L g - 5 + 4 * 1 = warpOf L g - 1 by omega] at hc
      simp only [stateTime, barCnt, ↓reduceIte, h2, h5, Nat.zero_add, hc, hS]
      exact hh

/-- The barrier of a followed state's barrier event is its site's. -/
theorem bar_site {g j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : ThreadD}
    (hg : g < L.threads) (he : X.get (g, j) = some ⟨pc, .bar id cnt m⟩)
    (hσ : St L X g j = some (some d)) : barIdOf L g d = some id := by
  have h := fired_barId hpre hX ht hok (id := id) hg hσ he
  simp only [Execution.isBarId, beq_self_eq_true] at h
  exact (beq_iff_eq.mp h.symm)

/-- **A thread's `bar.sync` is no earlier than the other participants' events of its
ordinal.** -/
theorem barSync {id g y j pc : Nat} {cnt : Option Nat} {d : ThreadD} (hg : g < L.threads)
    (_hy : y < L.threads) (hc : y / L.block = g / L.block) (hG : BarGroup id (warpOf L y))
    (he : X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩) (hσ : St L X g j = some (some d)) :
    barS L id (warpKey L y) (barOrd X g j id) ≤ barS L id (warpKey L g) (barOrd X g j id) := by
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hid := bar_site hpre hX ht hok hg he hσ
  have hcta : ctaOf L y = ctaOf L g := hc
  obtain ⟨hJ, -, hw⟩ := state_facts hpre hX ht hok hg hj.le hσ
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', l, rfl⟩ | ⟨hw', m, rfl⟩ |
      ⟨hw', s, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
  · simp [barIdOf] at hid
  · simp [barIdOf] at hid
  · simp [barIdOf] at hid
  · -- the MMA warp: its start barrier (ordinal 0) or its second `bar.sync` (ordinal 1)
    have hb : Execution.isBar ⟨pc, .bar id cnt .sync⟩ = true := rfl
    have hcl := mma_counts_class hpre hX ht hw' j
    rcases mma_bar_event hpre hX ht hw' he hb with ⟨hx, h0⟩ | ⟨hx, h1⟩
    · simp only [Event.mk.injEq, Kind.bar.injEq] at hx
      obtain ⟨-, rfl, -, -⟩ := hx
      have : barOrd X g j 2 = 0 := by unfold barOrd; rw [← hcl.1, h0]
      rw [this, barS_zero, barS_zero]
    · simp only [Event.mk.injEq, Kind.bar.injEq] at hx
      obtain ⟨-, rfl, -, -⟩ := hx
      have : barOrd X g j 2 = 1 := by unfold barOrd; rw [← hcl.1, h1]
      rw [this]
      refine (barS_one L _).trans (le_of_eq ?_)
      simp [barS, warpKey, hw', hcta]
  · simp [barIdOf] at hid
  · -- a softmax thread syncs only at its start barrier
    rcases soft_origin hpre hX ht he hw' (not_ub hpre hX ht hok hg hσ he) with
      ⟨p, hp, -⟩ | ⟨s', t, ins, o, hs', -, -, -, -, -, hev⟩
    · have hp' : St L X g j = some (some (.inl p)) := hp
      rw [hσ] at hp'; cases hp'
    have hs'' : St L X g j = some (some (.inr (.softmax s'))) := hs'
    rw [hσ] at hs''
    cases hs''
    have hb0 : s.site = .bar0 := by
      cases hs : s.site <;> simp only [Softmax.Ev, hs] at hev <;> simp_all
    have hid2 : id = 2 := by simp [barIdOf, hb0] at hid; exact hid.symm
    subst hid2
    have h0 := barCnt_eq hpre hX ht hok hg (.inl ⟨rfl, by omega⟩) hj.le hσ
    have : barOrd X g j 2 = 0 := by
      unfold barOrd; rw [h0]
      simp [barCnt, Softmax.bar2Sync, Softmax.bar2Arrive, hb0]
    rw [this, barS_zero, barS_zero]
  · -- a correction thread: its start barrier, or a sync of a stage after the softmax arrivals
    rcases corr_origin hpre hX ht he hw' hw'' (not_ub hpre hX ht hok hg hσ he) with
      ⟨p, hp, -⟩ | ⟨c', t, ins, o, hs', -, -, -, -, -, hev⟩
    · have hp' : St L X g j = some (some (.inl p)) := hp
      rw [hσ] at hp'; cases hp'
    have hs'' : St L X g j = some (some (.inr (.corr c'))) := hs'
    rw [hσ] at hs''
    cases hs''
    have hev := (hev (fun h => by cases h)).2
    have hk0 := corr_kOf (L := L) hw' hw''
    cases hs : c.site with
    | bar0 =>
      have hid2 : id = 2 := by simp [barIdOf, hs] at hid; exact hid.symm
      subst hid2
      have h0 := barCnt_eq hpre hX ht hok hg (.inl ⟨rfl, by omega⟩) hj.le hσ
      have : barOrd X g j 2 = 0 := by
        unfold barOrd; rw [h0]
        have a : ¬ (2 = warpOf L g - 5) := by omega
        have b : ¬ (2 = warpOf L g - 1) := by omega
        simp [barCnt, Correction.bar2Sync, Correction.bar2Arrive, hs, a, b]
      rw [this, barS_zero, barS_zero]
    | sync st gen =>
      have hid' : id = warpOf L g - 5 + 4 * st.val := by
        simp [barIdOf, hs] at hid; exact hid.symm
      have hst := st.isLt
      have h2 : id ≠ 2 := by omega
      -- the participants of the barrier: the softmax warp of the stage and this warp
      rcases hG with ⟨h, -⟩ | ⟨st', k, hst', hk, hidk, hwy | hwy⟩
      · exact absurd h h2
      · have hk' : k = warpOf L g - 8 ∧ st' = st.val := by
          simp only [statsId] at hidk; omega
        have hwy8 : warpOf L y < 8 := by omega
        have hS1 : barS L id (warpKey L y) = statS (Work.n L) (Tc L (ctaOf L g))
            (bandS st.val + 22) 0 := by
          funext n
          have : warpOf L y / 4 = st.val := by omega
          simp [barS, warpKey, hwy8, h2, hcta, this]
        rw [hS1]
        rcases Softmax.fin2_cases st with rfl | rfl
        · have hS2 : barS L id (warpKey L g) = statS (Work.n L) (Tc L (ctaOf L g))
              (bandC 0) 2 := by
            funext n
            unfold barS
            simp only [warpKey, Fin.val_zero] at hid' ⊢
            split_ifs <;> first | (exfalso; omega) | simp [show id = warpOf L g - 5 by omega]
          rw [hS2]
          exact statS_le (by simp only [bandS, bandC]; omega) (by omega)
        · have hS2 : barS L id (warpKey L g) = statS (Work.n L) (Tc L (ctaOf L g))
              (bandC 1) 2 := by
            funext n
            unfold barS
            simp only [warpKey, Fin.val_one] at hid' ⊢
            split_ifs <;> first | (exfalso; omega) |
              simp [show ¬ id = warpOf L g - 5 by omega]
          rw [hS2]
          exact statS_le (by simp only [bandS, bandC]; omega) (by omega)
      · have hwe : warpOf L y = warpOf L g := by simp only [statsId] at hidk; omega
        rw [show warpKey L y = warpKey L g by simp [warpKey, hwe, hcta]]
    | barEnd => simp only [hs] at hev; cases hev
    | _ => simp [barIdOf, hs] at hid

/-- **The per-warp schedules of every named barrier.** -/
theorem barSched : BarSched L X := fun id =>
  ⟨barS L id, barCollSched hpre hX ht hok id,
    fun hg hy hc hG he hσ => barSync hpre hX ht hok hg hy hc hG he hσ⟩

/-- **`Cross.BarMember`**: a thread's event on a named barrier is a participant warp's. -/
theorem barMember : BarMember L X := by
  intro g j pc id cnt m hg he
  obtain ⟨d, hσ⟩ := Frame.event_state (C := code L) (fun _ hg => sound hpre hg) hX ht he
    (fun _ _ h => by cases h)
  have hid := bar_site hpre hX ht hok hg he hσ
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨-, -, hw⟩ := state_facts hpre hX ht hok hg hj.le hσ
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', l, rfl⟩ | ⟨hw', mm, rfl⟩ |
      ⟨hw', s, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
  · simp [barIdOf] at hid
  · simp [barIdOf] at hid
  · simp [barIdOf] at hid
  · have : id = 2 := by
      revert hid; simp only [barIdOf]; split <;> simp <;> omega
    exact .inl ⟨this, by omega⟩
  · simp [barIdOf] at hid
  · revert hid; simp only [barIdOf]; split
    · intro h; exact .inl ⟨by simp at h; omega, by omega⟩
    · intro h; exact .inl ⟨by simp at h; omega, by omega⟩
    · intro h
      simp at h
      exact .inr ⟨warpOf L g / 4, warpOf L g % 4, by omega, by omega,
        by simp only [statsId]; omega, .inl (by omega)⟩
    · simp
  · revert hid; simp only [barIdOf]; split
    · intro h; exact .inl ⟨by simp at h; omega, by omega⟩
    · intro h; exact .inl ⟨by simp at h; omega, by omega⟩
    · rename_i st _ _
      intro h
      simp at h
      exact .inr ⟨st.val, warpOf L g - 8, st.isLt, by omega,
        by simp only [statsId]; omega, .inr (by omega)⟩
    · simp

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
