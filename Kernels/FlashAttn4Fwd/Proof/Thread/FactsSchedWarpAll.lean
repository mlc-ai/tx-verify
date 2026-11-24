-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedMmaWarpExit
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedSoftWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedCorrWarp

@[expose] public section

/-! # The warp collectives of all warps but the correction warps

* `Cross.WarpSched` (`warpSched_of_corr`): `Sched.warpSched` with the softmax
  (`softWarpRoleSched`), MMA (`mmaWarpSched`) and loader (`loaderWarpSched`) warps' schedules;
  the correction warps' schedule is the premise.
* `Cross.WarpExitAgree`, `Cross.WarpExitAbove` (`warpExitAgree_of_corr`,
  `warpExitAbove_of_corr`), by cases on the warp: the softmax, MMA and loader warps' parts,
  the store and idle warps' (`exitAgree_of`, `exitAbove_of` with `quietWarpSched`: their warp
  collectives are the prologue's, before every store or idle time), and the correction warps'
  part as the premise (`CorrWarpExitAgree`, `CorrWarpExitAbove`).
* With the correction warps' parts (`corrWarpSched`, `Cross.WarpExitAgree_corr`,
  `Cross.WarpExitAbove_corr`): `warpSched_all`, `warpExitAgree_all`, `warpExitAbove_all`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Progress.Time
open PTX.Kernels.FlashAttn4Fwd.Proof.Cross

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The correction warps' part of `Cross.WarpExitAgree`. -/
def CorrWarpExitAgree (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k k' pc pc' : Nat} {d d' : ThreadD}, 8 ≤ warpOf L g → warpOf L g < 12 →
    SameWarp L g h → St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .exit⟩ → X.get (h, k') = some ⟨pc', .exit⟩ →
    ((X.tr g).take k).countP Sched.isWarpColl = ((X.tr h).take k').countP Sched.isWarpColl

/-- The correction warps' part of `Cross.WarpExitAbove`. -/
def CorrWarpExitAbove (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k pc : Nat} {d d' : ThreadD}, 8 ≤ warpOf L g → warpOf L g < 12 → SameWarp L g h →
    St L X g (X.tr g).length = some (some d) → nextKind d = .warp →
    St L X h k = some (some d') → X.get (h, k) = some ⟨pc, .exit⟩ →
    (X.tr g).countP Sched.isWarpColl < ((X.tr h).take k).countP Sched.isWarpColl

theorem Store.site_exit (s : Store.Site) : s.pc = Flow.exit_0 → s = .exit := by
  cases s <;> site_decide

theorem Idle.site_exit (s : Idle.Site) : s.pc = Flow.exit_0 → s = .exit := by
  cases s <;> site_decide

/-- Every store and idle time is from the role entries on. -/
theorem store_ge_reg {n T : Nat} (d : Store.D) : regT ≤ store n T d := by
  obtain ⟨s, i⟩ := d
  cases s <;> simp only [store, storeAt, tailTime, slotTime, regT, base] <;> omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- **`Cross.WarpSched`** from the correction warps' schedule. -/
theorem warpSched_of_corr (hcorr : WarpRoleSched L X (fun w => 8 ≤ w ∧ w < 12)) :
    ∃ S, WarpSched L X S :=
  warpSched hpre hX ht hok (softWarpRoleSched hpre hX ht hok) hcorr
    (mmaWarpSched hpre hX ht hok) (loaderWarpSched hpre hX ht hok)

/-- A lane of warp 13 or 15 at an exit: the store's or the idle warp's exit site. -/
theorem quiet_exit_site {h k : Nat} {d : ThreadD} (hh : h < L.threads)
    (hw : warpOf L h = 13 ∨ warpOf L h = 15) (hk : k ≤ (X.tr h).length)
    (hσ : St L X h k = some (some d)) (hpc : (code L h).pc d = Flow.exit_0) :
    (warpOf L h = 13 ∧ stateTime L h d = tailTime (Work.n L) (Work.T L h) 2000) ∨
      (warpOf L h = 15 ∧ stateTime L h d = idleExitT) := by
  obtain ⟨-, -, hw'⟩ := state_facts hpre hX ht hok hh hk hσ
  rcases quiet_state hpre hX ht hok hh hw hk hσ with ⟨s, rfl, -⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact absurd hpc (Prologue.site_ne_exit s)
  · have hs := Store.site_exit s.site hpc
    have h13 := hw' _ rfl
    simp only [Role.kind, RoleKind.Warp] at h13
    obtain ⟨site, i⟩ := s
    simp only at hs
    subst hs
    exact .inl ⟨h13, rfl⟩
  · have hs := Idle.site_exit s.site hpc
    have h15 := hw' _ rfl
    simp only [Role.kind, RoleKind.Warp] at h15
    obtain ⟨site⟩ := s
    simp only at hs
    subst hs
    exact .inr ⟨h15, rfl⟩

theorem quietExitTimes : ExitTimes L X (fun g => warpOf L g = 13 ∨ warpOf L g = 15) where
  grp hsw hG := by rw [sameWarp_warp hsw]; exact hG
  lt := by
    intro g h k k' d d' hsw hG hk hσ hkd hk' hσ' hpc
    have hG' : warpOf L h = 13 ∨ warpOf L h = 15 := by rw [sameWarp_warp hsw]; exact hG
    have hlo : regT ≤ stateTime L h d' := by
      rcases quiet_state hpre hX ht hok hsw.1.2.1 hG' hk' hσ' with ⟨s, rfl, -⟩ | ⟨s, rfl⟩ |
          ⟨s, rfl⟩
      · exact absurd hpc (Prologue.site_ne_exit s)
      · exact store_ge_reg s
      · obtain ⟨site⟩ := s; cases site <;> simp [stateTime, idle, regT, idleExitT]
    rcases quiet_state hpre hX ht hok hsw.1.1 hG hk hσ with ⟨s, rfl, -⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact (Progress.Time.prologue_lt_reg s).trans_le hlo
    · obtain ⟨site, i⟩ := s
      cases site <;> simp [nextKind, storeKind] at hkd
    · obtain ⟨site⟩ := s
      cases site <;> simp [nextKind, idleKind] at hkd
  eq := by
    intro g h k k' d d' hsw hG hk hσ hpc hk' hσ' hpc'
    have hG' : warpOf L h = 13 ∨ warpOf L h = 15 := by rw [sameWarp_warp hsw]; exact hG
    have hwe := sameWarp_warp hsw
    rcases quiet_exit_site hpre hX ht hok hsw.1.1 hG hk hσ hpc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases quiet_exit_site hpre hX ht hok hsw.1.2.1 hG' hk' hσ' hpc' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h2, h4, T_same hsw]
    · omega
    · omega
    · rw [h2, h4]

/-- **`Cross.WarpExitAgree`** from the correction warps' part. -/
theorem warpExitAgree_of_corr (hcorr : CorrWarpExitAgree L X) : WarpExitAgree L X := by
  intro g h k k' pc pc' d d' hsw hσ hσ' he he'
  have hw := warp_lt hpre g
  have hsched := quietWarpSched hpre hX ht hok
  by_cases h8 : warpOf L g < 8
  · exact softWarpExitAgree hpre hX ht hok h8 hsw he he'
  by_cases h12 : warpOf L g < 12
  · exact hcorr (by omega) h12 hsw hσ hσ' he he'
  by_cases h12' : warpOf L g = 12
  · exact mmaWarpExitAgree hpre hX ht hok h12' hsw hσ hσ' he he'
  by_cases h14 : warpOf L g = 14
  · exact loaderWarpExitAgree hpre hX ht hok h14 hsw hσ hσ' he he'
  exact exitAgree_of hpre hX ht hok hsched (quietExitTimes hpre hX ht hok) (by omega) hsw hσ hσ'
    he he'

/-- **`Cross.WarpExitAbove`** from the correction warps' part. -/
theorem warpExitAbove_of_corr (hcorr : CorrWarpExitAbove L X) : WarpExitAbove L X := by
  intro g h k pc d d' hsw hσ hk hσ' he'
  have hw := warp_lt hpre g
  have hsched := quietWarpSched hpre hX ht hok
  by_cases h8 : warpOf L g < 8
  · exact softWarpExitAbove hpre hX ht hok h8 hsw hσ hk he'
  by_cases h12 : warpOf L g < 12
  · exact hcorr (by omega) h12 hsw hσ hk hσ' he'
  by_cases h12' : warpOf L g = 12
  · exact mmaWarpExitAbove hpre hX ht hok h12' hsw hσ hk hσ' he'
  by_cases h14 : warpOf L g = 14
  · exact loaderWarpExitAbove hpre hX ht hok h14 hsw hσ hk hσ' he'
  exact exitAbove_of hpre hX hsched (quietExitTimes hpre hX ht hok) (by omega) hsw hσ hk hσ' he'

/-- **`Cross.WarpSched`.** -/
theorem warpSched_all : ∃ S, WarpSched L X S :=
  warpSched_of_corr hpre hX ht hok (corrWarpSched hpre hX ht hok)

/-- **`Cross.WarpExitAgree`.** -/
theorem warpExitAgree_all : WarpExitAgree L X :=
  warpExitAgree_of_corr hpre hX ht hok fun hw hw' hs _ _ he he' =>
    Cross.WarpExitAgree_corr hpre hX ht hok hw hw' hs he he'

/-- **`Cross.WarpExitAbove`.** -/
theorem warpExitAbove_all : WarpExitAbove L X :=
  warpExitAbove_of_corr hpre hX ht hok fun hw hw' hs hσ hk _ he' =>
    Cross.WarpExitAbove_corr hpre hX ht hok hw hw' hs hσ hk he'

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
