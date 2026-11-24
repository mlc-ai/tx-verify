-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedMmaWarp

@[expose] public section

/-! # The MMA warp's counts at the exit (`Cross.WarpExitAgree`, `Cross.WarpExitAbove`)

A lane of warp 12 exits at `mmaTail … 24`, the same time on every lane of the warp, after its
prologue, its `shflQ` and every item site (`Mma.time_item`), so its schedule (`mmaWarpSched`)
gives both premises for warp 12 (`exitAgree_of`, `exitAbove_of`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- The exit of a lane of warp 12: the MMA warp's exit site. -/
theorem mma_exit_site {h k : Nat} {d : ThreadD} (hh : h < L.threads) (hw : warpOf L h = 12)
    (hk : k ≤ (X.tr h).length) (hσ : St L X h k = some (some d))
    (hpc : (code L h).pc d = Flow.exit_0) :
    stateTime L h d = mmaTail (Work.n L) (Work.T L h) 24 := by
  rcases mma_state hpre hX ht hok hh hw hk hσ with ⟨s, rfl, -⟩ | ⟨m, rfl⟩
  · exact absurd hpc (Prologue.site_ne_exit s)
  · have hs := Mma.site_exit m.site hpc
    obtain ⟨site, i, t, b, pro⟩ := m
    simp only at hs
    subst hs
    rfl

theorem mmaExitTimes : ExitTimes L X (fun g => warpOf L g = 12) where
  grp hsw hG := (sameWarp_warp hsw).trans hG
  lt := by
    intro g h k k' d d' hsw hG hk hσ hkd hk' hσ' hpc
    rw [mma_exit_site hpre hX ht hok hsw.1.2.1 ((sameWarp_warp hsw).trans hG) hk' hσ' hpc,
      T_same hsw]
    obtain ⟨-, hinv, -⟩ := state_facts hpre hX ht hok hsw.1.1 hk hσ
    rcases mma_state hpre hX ht hok hsw.1.1 hG hk hσ with ⟨s, rfl, -⟩ | ⟨m, rfl⟩
    · exact ((Progress.Time.prologue_lt_reg s).trans (by decide)).trans_le Progress.Time.base_le
    · have hi : Mma.Inv L g m := hinv.1
      change mma _ _ m < _
      by_cases hs : Mma.ItemSite m.site
      · exact (Mma.time_item hpre hi hs).2.trans (Progress.Time.tail_lt (by decide))
      · obtain ⟨site, i, t, b, pro⟩ := m
        cases site <;> simp only [Mma.ItemSite, not_true_eq_false, not_false_eq_true] at hs <;>
          simp only [nextKind, mmaKind, reduceCtorEq] at hkd
        simp only [mma, mmaTail, tailTime, shflQT]
        exact Progress.Time.fixed_lt (by decide)
  eq := by
    intro g h k k' d d' hsw hG hk hσ hpc hk' hσ' hpc'
    rw [mma_exit_site hpre hX ht hok hsw.1.1 hG hk hσ hpc,
      mma_exit_site hpre hX ht hok hsw.1.2.1 ((sameWarp_warp hsw).trans hG) hk' hσ' hpc',
      T_same hsw]

/-- **`Cross.WarpExitAgree` for the lanes of warp 12.** -/
theorem mmaWarpExitAgree : ∀ {g h k k' pc pc' : Nat} {d d' : ThreadD}, warpOf L g = 12 →
    SameWarp L g h → St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .exit⟩ → X.get (h, k') = some ⟨pc', .exit⟩ →
    ((X.tr g).take k).countP Sched.isWarpColl = ((X.tr h).take k').countP Sched.isWarpColl := by
  obtain ⟨S, hs⟩ := mmaWarpSched hpre hX ht hok
  exact exitAgree_of hpre hX ht hok hs (mmaExitTimes hpre hX ht hok)

/-- **`Cross.WarpExitAbove` for the lanes of warp 12.** -/
theorem mmaWarpExitAbove : ∀ {g h k pc : Nat} {d d' : ThreadD}, warpOf L g = 12 →
    SameWarp L g h → St L X g (X.tr g).length = some (some d) → nextKind d = .warp →
    St L X h k = some (some d') → X.get (h, k) = some ⟨pc, .exit⟩ →
    (X.tr g).countP Sched.isWarpColl < ((X.tr h).take k).countP Sched.isWarpColl := by
  obtain ⟨S, hs⟩ := mmaWarpSched hpre hX ht hok
  exact exitAbove_of hpre hX hs (mmaExitTimes hpre hX ht hok)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
