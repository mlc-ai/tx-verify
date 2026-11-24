-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Protocol.Pos
public import Lemmas.Step.WarpShfl

@[expose] public section

/-! # The warps' shuffles

The `n`-th shuffles of the lanes of a warp are one site of one row (`same_round`): a lane's
shuffles before its row's rounds are the warp-index shuffle and five rounds per earlier row (ten
in warp 0). A shuffle receives the operand of its source lane's shuffle of the same number
(`shfl_source`, DEP-WARP-SHUFFLE): the source lane has not exited before it, since a lane exits only
after the rows of its CTA. -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A state of a shuffle site: the warp-index shuffle or a round of a butterfly. -/
def Site.isShfl : Site → Bool
  | .shfl0 | .bfa _ | .bfb _ => true
  | _ => false

theorem isShfl_of_event {g pc : Nat} {d : D} {m : ShflMode} {a : Value} {b c : Nat} {recv : Value}
    {ok : Bool} (h : SiteEvent P g d ⟨pc, .shfl m a b c recv ok⟩) : d.site.isShfl = true := by
  rcases shfl_site h with ⟨hs, -⟩ | ⟨k, hs, -⟩ | ⟨k, hs, -⟩ <;> simp [hs, Site.isShfl]

/-- **The `n`-th shuffles of two lanes of a warp are one site of one row.** -/
theorem same_round {y z : Nat} {dy dz : D} (hiy : Inv P y dy) (hiz : Inv P z dz)
    (hsy : dy.site.isShfl = true) (hsz : dz.site.isShfl = true) (hc : y / 256 = z / 256)
    (hw : y % 256 / 32 = z % 256 / 32) (h : dy.sc y = dz.sc z) :
    dy.site = dz.site ∧ (dy.site ≠ .shfl0 → dy.i = dz.i) := by
  have hw0 : w0 y = w0 z := by unfold w0; split_ifs <;> omega
  have hay := hiy.bfa
  have haz := hiz.bfa
  have hby := hiy.bfb
  have hbz := hiz.bfb
  rcases hy : dy.site <;> simp only [hy, Site.isShfl, Bool.false_eq_true] at hsy <;>
    rcases hz : dz.site <;> simp only [hz, Site.isShfl, Bool.false_eq_true] at hsz <;>
    simp only [D.sc, hy, hz, reduceCtorEq, false_implies, Site.bfa.injEq, Site.bfb.injEq,
      forall_eq', ne_eq, not_false_eq_true, not_true_eq_false, true_implies, and_true]
      at h hay haz hby hbz ⊢
  all_goals (simp only [w0] at h hw0 ⊢; split_ifs at h hw0 <;> omega)

/-- The source lane of a lane of a warp, a lane of the warp. -/
def srcLane (m : ShflMode) (y b c : Nat) : Nat :=
  y - y % 256 % 32 + (shflSource m (y % 256 % 32) b c).1

theorem srcLane_warp (m : ShflMode) (y b c : Nat) :
    srcLane m y b c / 256 = y / 256 ∧ srcLane m y b c % 256 / 32 = y % 256 / 32 ∧
      srcLane m y b c % 256 % 32 = (shflSource m (y % 256 % 32) b c).1 := by
  have := Step.shflSource_lt m (Nat.mod_lt (y % 256) (show 0 < 32 by decide)) b c
  unfold srcLane
  omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **A shuffle receives its source lane's operand** of the shuffle of the same number. -/
theorem shfl_source {y k pc : Nat} {m : ShflMode} {a : Value} {b c : Nat} {recv : Value} {ok : Bool}
    {dy : D} (he : X.get (y, k) = some ⟨pc, .shfl m a b c recv ok⟩)
    (hA : At P L X y k dy ⟨pc, .shfl m a b c recv ok⟩) :
    ∃ kz dz pcz bz cz rz oz, X.get (srcLane m y b c, kz) = some ⟨pcz, .shfl m recv bz cz rz oz⟩ ∧
      At P L X (srcLane m y b c) kz dz ⟨pcz, .shfl m recv bz cz rz oz⟩ ∧
      dz.sc (srcLane m y b c) = dy.sc y := by
  have hB := hpre.hyp.block
  have hK : X.ShflK (y, k) (dy.sc y) := ⟨⟨_, _, _, _, _, _, _, he⟩, hA.sc⟩
  obtain ⟨-, hsrc⟩ := hX.shfl y k (dy.sc y) pc m a b c recv ok he hK
  simp only [laneOf, hB] at hsrc
  rw [show y - y % 256 % 32 + (shflSource m (y % 256 % 32) b c).1 = srcLane m y b c from
    rfl] at hsrc
  obtain ⟨hzc, hzw, -⟩ := srcLane_warp m y b c
  rcases hsrc with ⟨j, pc', b', c', r', o', hKz, hz⟩ | ⟨kx, pcx, hx, hcx⟩
  · obtain ⟨-, dz, hAz⟩ := event_facts hpre hX ht hz (by intro _ _ h; cases h)
    refine ⟨j, dz, pc', b', c', r', o', hz, hAz, ?_⟩
    rw [← hAz.sc]
    exact hKz.2
  · exfalso
    obtain ⟨-, dx, hAx⟩ := event_facts hpre hX ht hx (by intro _ _ h; cases h)
    have hxs := exit_site hAx.event
    have hex := hAx.inv.exit hxs
    rw [hAx.sc] at hcx
    have hw0 : w0 (srcLane m y b c) = w0 y := by unfold w0; split_ifs <;> omega
    have hay := hA.inv.bfa
    have hby := hA.inv.bfb
    rcases shfl_site hA.event with ⟨hs, -⟩ | ⟨q, hs, -⟩ | ⟨q, hs, -⟩
    · simp [D.sc, hs, hxs] at hcx
    · have hr := hA.inv.row (by simp [hs, Site.inRow])
      simp only [row] at hr
      simp only [D.sc, hs, hxs, hw0, Site.bfa.injEq, forall_eq'] at hcx hay
      have : dy.i + 1 ≤ dx.i := by omega
      have := Nat.mul_le_mul_left (5 * (1 + w0 y)) this
      rw [Nat.mul_succ] at this
      omega
    · have hr := hA.inv.row (by simp [hs, Site.inRow])
      simp only [row] at hr
      simp only [D.sc, hs, hxs, hw0, Site.bfb.injEq, forall_eq'] at hcx hby
      have : dy.i + 1 ≤ dx.i := by omega
      have := Nat.mul_le_mul_left (5 * (1 + w0 y)) this
      rw [Nat.mul_succ] at this
      have : w0 y = 1 := by unfold w0; split_ifs <;> omega
      omega

end
end PTX.Kernels.RmsNorm.Proof
