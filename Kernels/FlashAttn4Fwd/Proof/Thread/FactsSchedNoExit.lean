-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedStep

@[expose] public section

/-! # A participant exits after all its events on a named barrier (`Cross.BarNoExit`)

A thread's exit is its trace's last event, fired from its role's exit site, where it has made
all its events on each named barrier (`barCnt`): two on barrier 2, `(n + 1) T` on its statistics
barriers (`exit_count`). A thread's event on a barrier comes before that many of its own
(`ord_lt`): on barrier 2 the start barrier is its first and the end barrier (or the MMA warp's
second `bar.sync`) its second; a statistics event of item `i < T` has ordinal
`(n + 1) i + p` with `p ≤ n`. So a participant with no more events than a thread's ordinal there
has not exited. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The events on barrier `id` a participant of warp `w` makes in all. -/
def barTotal (L : Launch) (g id : Nat) : Nat :=
  if id = 2 then 2 else (Work.n L + 1) * Work.T L g

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- **At its exit a participant has made all its events on the barrier.** -/
theorem exit_count {y k pc id : Nat} (hy : y < L.threads) (hG : BarGroup id (warpOf L y))
    (he : X.get (y, k) = some ⟨pc, .exit⟩) :
    (X.tr y).countP (Execution.isBarId id) = barTotal L y id := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he (fun _ _ h => by cases h)
  have hpc := Lag.exit_pc hpre hX he hσ
  have hk : k < (X.tr y).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨o, hr⟩ := hX.thr y hy
  have hlast := Run.end_last hr he (.inr rfl)
  have htr : X.tr y = (X.tr y).take k ++ [⟨pc, .exit⟩] := by
    rw [← Option.toList_some, ← he, Execution.get, ← List.take_add_one, hlast, List.take_length]
  have hcnt := barCnt_eq hpre hX ht hok hy hG hk.le hσ
  rw [htr, List.countP_append, hcnt]
  simp only [List.countP_singleton, Execution.isBarId, reduceCtorEq, ite_false, Nat.add_zero]
  obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hy hk.le hσ
  have hlt := barGroup_lt hG
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', l, rfl⟩ | ⟨hw', m, rfl⟩ |
      ⟨hw', s, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
  · exact absurd hpc (Prologue.site_ne_exit p.site)
  · omega
  · omega
  · have hs := Mma.site_exit m.site hpc
    have h2 := barGroup_mma (hw' ▸ hG)
    subst h2
    simp [barCnt, barTotal, Mma.bar2A, hs]
  · omega
  · have hs := Facts.soft_site_ret s.site (List.mem_singleton.mpr hpc)
    have hinv' : Softmax.Inv L y s := hinv
    obtain ⟨hi, -⟩ := hinv'.tail (by simp [hs])
    rcases barGroup_soft hG hw' with rfl | rfl
    · simp [barCnt, barTotal, Softmax.bar2Sync, Softmax.bar2Arrive, hs]
    · have h2 : ¬ (warpOf L y + 3 = 2) := by omega
      simp [barCnt, barTotal, Softmax.genPos, hs, h2, hi, Softmax.Site.tile0, Softmax.Site.inTrip]
  · have hs := Facts.corr_site_ret c.site (List.mem_singleton.mpr hpc)
    have hinv' : Correction.Inv L y c := hinv
    have hi := hinv'.tail (by simp [hs, Correction.Site.inItem]) (by simp [hs]) (by simp [hs])
      (fun _ => by simp [hs])
    rcases barGroup_corr hG hw' hw'' with rfl | rfl | rfl
    · have a : ¬ (2 = warpOf L y - 5) := by omega
      have b : ¬ (2 = warpOf L y - 1) := by omega
      simp [barCnt, barTotal, Correction.bar2Sync, Correction.bar2Arrive, hs, a, b]
    · have a : ¬ (warpOf L y - 5 = 2) := by omega
      have b : ¬ (warpOf L y - 5 = warpOf L y - 1) := by omega
      simp [barCnt, barTotal, Correction.syncPos, hs, a, b, hi]
      rfl
    · have a : ¬ (warpOf L y - 1 = 2) := by omega
      have b : ¬ (warpOf L y - 1 = warpOf L y - 5) := by omega
      simp [barCnt, barTotal, Correction.syncPos, hs, a, b, hi]
      rfl

/-- **A thread's event on a barrier comes before all of its events there.** -/
theorem ord_lt {g j pc id : Nat} {cnt : Option Nat} {m : BarMode} (hg : g < L.threads)
    (he : X.get (g, j) = some ⟨pc, .bar id cnt m⟩) :
    barOrd X g j id < barTotal L g id := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he (fun _ _ h => by cases h)
  have hid := bar_site hpre hX ht hok hg he hσ
  have hG := barMember hpre hX ht hok hg he
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hn : 0 < Work.n L := Mma.trips_pos hpre
  unfold barOrd
  rw [barCnt_eq hpre hX ht hok hg hG hj.le hσ]
  obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hj.le hσ
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', l, rfl⟩ | ⟨hw', mm, rfl⟩ |
      ⟨hw', s, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
  · simp [barIdOf] at hid
  · simp [barIdOf] at hid
  · simp [barIdOf] at hid
  · obtain ⟨site, i, t, b, pro⟩ := mm
    cases site <;> simp only [barIdOf, reduceCtorEq, Option.some.injEq] at hid <;> subst hid <;>
      simp [barCnt, barTotal, Mma.bar2A]
  · simp [barIdOf] at hid
  · have hinv' : Softmax.Inv L g s := hinv
    obtain ⟨site, i, t, w, mm, l⟩ := s
    have hitem := hinv'.item
    have htrip := hinv'.trip
    have hlast := hinv'.last
    simp only at hitem htrip hlast
    have hN0 : Softmax.trips L = Work.n L := rfl
    rw [hN0] at htrip hlast
    cases site <;> simp only [barIdOf, reduceCtorEq, Option.some.injEq] at hid <;> subst hid
    · simp [barCnt, barTotal, Softmax.bar2Sync, Softmax.bar2Arrive]
    · rename_i jj
      have hiT : i < Work.T L g := hitem rfl
      have h2 : ¬ (warpOf L g + 3 = 2) := by omega
      have hp : Softmax.genPos ⟨.gen jj, i, t, w, mm, l⟩ ≤ Work.n L := by
        rcases Softmax.fin3_cases jj with rfl | rfl | rfl
        · simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.afterGen]
        · have := htrip rfl
          simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.afterGen,
            Softmax.Site.inTrip]
          omega
        · have := hlast (by simp)
          simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.afterGen,
            Softmax.Site.inTrip]
          omega
      simp only [barCnt, barTotal, h2, ↓reduceIte, Nat.zero_add]
      have : (Work.n L + 1) * (i + 1) ≤ (Work.n L + 1) * Work.T L g :=
        Nat.mul_le_mul_left _ hiT
      have hN : Softmax.trips L = Work.n L := rfl
      rw [hN]
      rw [Nat.mul_succ] at this
      omega
    · simp [barCnt, barTotal, Softmax.bar2Sync, Softmax.bar2Arrive]
  · have hinv' : Correction.Inv L g c := hinv
    obtain ⟨site, i, t, aw, a, o⟩ := c
    have hitem := hinv'.item
    have htrip := hinv'.trip
    simp only at hitem htrip
    cases site <;> simp only [barIdOf, reduceCtorEq, Option.some.injEq] at hid <;> subst hid
    · have a : ¬ (2 = warpOf L g - 5) := by omega
      have b : ¬ (2 = warpOf L g - 1) := by omega
      simp [barCnt, barTotal, Correction.bar2Sync, Correction.bar2Arrive, a, b]
    · rename_i st gen
      have hiT : i < Work.T L g := hitem rfl
      have hst := st.isLt
      have h2 : ¬ (warpOf L g - 5 + 4 * st.val = 2) := by omega
      have hp : Correction.syncPos L st.val ⟨.sync st gen, i, t, aw, a, o⟩ ≤ Work.n L := by
        have hN : Correction.trips L = Work.n L := rfl
        rcases Softmax.fin2_cases st with rfl | rfl <;> cases gen <;>
          simp [Correction.syncPos, hN]
        all_goals (have := htrip rfl; omega)
      have : (Work.n L + 1) * (i + 1) ≤ (Work.n L + 1) * Work.T L g :=
        Nat.mul_le_mul_left _ hiT
      rw [Nat.mul_succ] at this
      have hN : Correction.trips L = Work.n L := rfl
      rcases Softmax.fin2_cases st with rfl | rfl
      · simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at h2 hp
        have b : ¬ (warpOf L g - 5 = warpOf L g - 1) := by omega
        simp only [barCnt, barTotal, Fin.val_zero, Nat.mul_zero, Nat.add_zero, h2, b,
          ↓reduceIte, Nat.zero_add, hN]
        omega
      · simp only [Fin.val_one, Nat.mul_one] at h2 hp
        have e1 : warpOf L g - 5 + 4 = warpOf L g - 1 := by omega
        have b : ¬ (warpOf L g - 1 = warpOf L g - 5) := by omega
        have h2' : ¬ (warpOf L g - 1 = 2) := by omega
        simp only [barCnt, barTotal, Fin.val_one, Nat.mul_one, e1, h2', b, ↓reduceIte,
          Nat.zero_add, hN]
        omega
    · have a : ¬ (2 = warpOf L g - 5) := by omega
      have b : ¬ (2 = warpOf L g - 1) := by omega
      simp [barCnt, barTotal, Correction.bar2Sync, Correction.bar2Arrive, a, b]

/-- **`Cross.BarNoExit`.** -/
theorem barNoExit : BarNoExit L X := by
  intro g y j pc id cnt m hg hy hc hG he hcnt k pc' hx
  have h1 := exit_count hpre hX ht hok hy hG hx
  have h2 := ord_lt hpre hX ht hok hg he
  have hT : barTotal L y id = barTotal L g id := by
    simp only [barTotal, T_eq]
    have : ctaOf L y = ctaOf L g := hc
    rw [this]
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
