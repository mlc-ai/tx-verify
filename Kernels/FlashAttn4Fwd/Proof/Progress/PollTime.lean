-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface
public import Kernels.FlashAttn4Fwd.Proof.Thread.Roles
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressNext

@[expose] public section

/-! # Every mbarrier poll site is in a slot or the tail

The time of every state whose next event is an mbarrier poll is at least `Time.base`: each poll
site is timed in a slot of an item or in the tail (`wait_base_le`). So a thread at a poll has
time at least 2, as `Sched.mbar_at_steps asms_wfStep` needs. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX Time

noncomputable section

theorem base_le_slotTime {n i s o : Nat} : base ≤ slotTime n i s o := by
  unfold slotTime; omega

/-- **Every poll site is timed at least at `base`.** -/
theorem wait_base_le (L : Launch) (g : Nat) {d : ThreadD} (hk : nextKind d = .wait) :
    base ≤ stateTime L g d := by
  rcases d with p | r
  · cases hs : p.site <;> simp [nextKind, prologueKind, hs] at hk
  · cases r with
    | idle s => cases hs : s.site <;> simp [nextKind, idleKind, hs] at hk
    | loader d =>
      simp only [stateTime, Time.loader]
      cases hs : d.site <;> simp [nextKind, loaderKind, hs] at hk <;>
        simp only [loaderUse, tailTime] <;> exact base_le_slotTime
    | mma d =>
      simp only [stateTime, Time.mma]
      cases hs : d.site <;> simp [nextKind, mmaKind, hs] at hk <;>
        simp only [mmaTail, tailTime, mmaAt] <;> (try split_ifs) <;> exact base_le_slotTime
    | store d =>
      simp only [stateTime, Time.store]
      cases hs : d.site <;> simp [nextKind, storeKind, hs] at hk
      simp only [storeAt]
      exact base_le_slotTime
    | softmax d =>
      simp only [stateTime, Time.softmax]
      cases hs : d.site with
      | statsW k =>
        obtain ⟨k, hk4⟩ := k
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
          simp only [tailTime] <;> exact base_le_slotTime
      | sW lp => exact base_le_slotTime
      | _ => simp [nextKind, softmaxKind, hs] at hk
    | corr d =>
      simp only [stateTime, Time.correction]
      cases hs : d.site <;> simp [nextKind, corrKind, hs] at hk <;>
        simp only [tailTime] <;> exact base_le_slotTime

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
