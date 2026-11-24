-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk5BR

@[expose] public section

/-!
# Bounds of the barrier-0 counts

* `nResc_mono`: the number of rescale iterations is monotone in the bound;
* `prev_bar23`: the state before `bar23` is `store10` of the same iteration;
* `proOff_b0_lt`: a prologue `bar.sync 0, 128` has fewer than the prologue's `1 + 5 nb` before it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk5B
open PTX PTX.Proof PTX.Flow
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem nResc_mono (Dc : Nat → Prop) {a b : Nat} (h : a ≤ b) : nResc Dc a ≤ nResc Dc b := by
  unfold nResc
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_Ico] at hj ⊢
  exact ⟨⟨hj.1.1, by omega⟩, hj.2⟩

/-- **The state before `bar23` is `store10` of the same iteration.** -/
theorem prev_bar23 {L : Launch} {g : Nat} {d0 d : Sm.D} {e : Event}
    (h : Sm.next L g d0 e = some (some d)) (hs : d.site = .bar23) :
    d0.site = .store10 ∧ d.i = d0.i := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d0
  cases s <;>
    simp only [Sm.next, Sm.afterArrive, Sm.afterSetup] at h <;>
    (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [toBar20_iff] at h
       obtain ⟨-, rfl⟩ := h
       simp at hs)
    | (obtain rfl := Option.some.inj (Option.some.inj h)
       simp_all [Sm.D.afterSum])

/-- **A prologue `bar.sync 0, 128` has fewer than `1 + 5 nb` before it**, at a state with the
gate. -/
theorem proOff_b0_lt {L : Launch} {g : Nat} {d : ProA.D} (hb : proB0 d.site = 2)
    (hG : ProA.Gate L g d.site d.dt) : proOff L g d < 1 + 5 * nbOf L g d.dt := by
  obtain ⟨s, dt⟩ := d
  obtain ⟨g0, g1, g2⟩ := hG
  cases s <;> simp only [proB0] at hb <;> (try exact absurd hb (by decide)) <;>
    simp_all (config := { decide := true }) [proOff, blkOff, nbOf] <;> split_ifs <;> omega

/-- The `bar.sync 0, 128` of the softmax region: `bar22`, `bar23`, or a late site. -/
theorem phi_b0 {s : Sm.Site} (h : smB0 s = 2) (i : Nat) :
    (s = .bar22 ∧ phi s i = 4 * (i : Int) - 2) ∨ (s = .bar23 ∧ phi s i = 4 * (i : Int) - 1) ∨
      (late s = true ∧ 4 * (i : Int) ≤ phi s i ∧ phi s i ≤ 4 * (i : Int) + 1 ∧
        mid s = false) := by
  cases s <;> simp_all [smB0, phi, late, mid]

/-- The sites of the softmax region's `bar.sync 0, 128` are not before the loop. -/
theorem lateSite_b0 {s : Sm.Site} (h : smB0 s = 2) : Sm.LateSite s := by
  cases s <;> simp_all [smB0, Sm.LateSite]

/-- The rescale iterations before a state are at most those of the iterations up to its own. -/
theorem rd_le (Dc : Nat → Prop) (d : Sm.D) : RD Dc d ≤ nResc Dc (d.i + 1) := by
  rw [nResc_succ]
  unfold RD
  split_ifs <;> simp_all

/-- The prologue's `bar.sync 0, 128` are after the request-word loads. -/
theorem pro_b0_afterSk {s : ProA.Site} (h : proB0 s = 2) : s.afterSk = true := by
  cases s <;> simp_all [proB0] <;> decide

end
end PTX.Kernels.InklingRelDecode.Proof.Lk5B
