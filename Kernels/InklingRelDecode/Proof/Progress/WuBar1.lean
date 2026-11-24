-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuReg

@[expose] public section

/-!
# `BarTime.lag1`

A lane `y` of the CTA with at most `n` barrier-1 events, where `n` is the ordinal of a barrier-1
event of `g`, is timed at most `capB n`, which is `g`'s time (the generations of barrier 1 are at
`c0`, `c1`, `c2`, `c3` in every machine), and it has not exited: an exit follows four barrier-1
events, and `n` is at most three.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An exit follows at least four barrier-1 events.** -/
theorem exit_b1_ge (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) {y j pc : Nat} (hx : X.get (y, j) = some ⟨pc, .exit⟩) :
    4 ≤ b1N X y j := by
  rcases exit_event_state hX hS htr hx with ⟨e, hσh, hs⟩ | ⟨x, hσh, hs⟩
  · obtain ⟨-, t1, h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR j _ (event_le hx) hσh
    have hp := d_exit_phase e hs
    have ht0 := h3 rfl
    simp only [tPh] at h2
    rw [hp] at h2
    omega
  · obtain ⟨-, t1, h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR j _ (event_le hx) hσh
    have h6' := h5 rfl
    have hp : wPh (.exit x) = (1, 1) := rfl
    simp only [tPh] at h2
    rw [hp] at h2
    omega

/-- **The ordinal of a barrier-1 event is at most three, and its state's time is its cap.** -/
theorem b1_event_cap (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g k pc : Nat}
    {d : TSt} (hget : X.get (g, k) = some ⟨pc, .bar 1 none .sync⟩)
    (hσ : St Q L X g k = some (some d)) :
    b1N X g k ≤ 3 ∧ time g d = capB (b1N X g k) := by
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hS hX hget hσ
  have hb := event_b1 hpre hX hS hget hσ
  have hb1 : tB1 d = true := by
    rw [← hb]
    simp [Execution.isBarId]
  obtain ⟨-, -, -, h4, -, h6, h7⟩ := tbl_at hpre hX hS hR (event_le hget) hσ hinv
  have hc := h6 hb1
  refine ⟨?_, le_antisymm h4 hc⟩
  by_contra hlt
  have := capB_ge (b := b1N X g k) (by omega)
  wt_omega

/-- **`BarTime.lag1` for `Wt.time`.** -/
theorem bar_lag1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) (hub : ¬ HasUb X) {g k pc y : Nat} {d : TSt} (_hg : g < L.threads)
    (hget : X.get (g, k) = some ⟨pc, .bar 1 none .sync⟩) (hσ : St Q L X g k = some (some d))
    (hy : y < L.threads) (_hdiv : y / L.block = g / L.block)
    (hle : (X.tr y).countP (Execution.isBarId 1) ≤ ((X.tr g).take k).countP (Execution.isBarId 1)) :
    (∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩) ∧
      Sched.threadTime (timed Wt.time Q L) X y ≤ Wt.time g d := by
  obtain ⟨h3, h4⟩ := b1_event_cap hpre hX hS hR hget hσ
  have hle' : (X.tr y).countP (Execution.isBarId 1) ≤ b1N X g k := hle
  have hnx : ∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hx
    have h5 := exit_b1_ge hpre hX hS htr hR hx
    have h6 : b1N X y j ≤ (X.tr y).countP (Execution.isBarId 1) := by
      unfold b1N
      exact List.Sublist.countP_le (List.take_sublist _ _)
    omega
  refine ⟨hnx, ?_⟩
  have := threadTime_b1_le hpre hX hS htr hR hub hy hnx hle'
  rw [h4]
  exact this

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
