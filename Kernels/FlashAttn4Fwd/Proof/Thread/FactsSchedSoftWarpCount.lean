-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.TrackedCount
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarId
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCountsStep
public import Lemmas.Flow.CountSplit

@[expose] public section

/-! # The warp collectives of a softmax warp before a state

A softmax thread's warp collectives are its shuffles, its elections and its warp barriers: the
prologue makes shuffles and elections, the role elections and warp barriers, and no event of
either is a ballot. Their counts are the shuffle count (`TrackedCount.shflJ`: four after the
prologue) and the roles' run invariant (`roleJ`): in the prologue its elections (warp 0's
`elects0`; none in warps 1 to 7), in the role `Softmax.Counts.elects` (the prologue's fourteen in
warp 0, then one per tile) and `Softmax.Counts.warpBar` (one per tile). So before a state there
are `cnt L g d` of them (`soft_warp_cnt`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace SoftW

/-- The prologue's warp collectives of warp `w` before site `s`: its shuffles and, in warp 0,
its elections. -/
def proCnt (w : Nat) (s : Prologue.Site) : Nat := s.shfls + (if w = 0 then s.elects0 else 0)

/-- The prologue's warp collectives of softmax warp `w`: four shuffles and, in warp 0, fourteen
elections. -/
def pro (w : Nat) : Nat := if w = 0 then 18 else 4

/-- The warp collectives of a softmax thread before a state: the prologue's, then per tile a
warp barrier and an election. -/
def cnt (L : Launch) (g : Nat) : ThreadD → Nat
  | .inl p => proCnt (warpOf L g) p.site
  | .inr (.softmax d) =>
    pro (warpOf L g) + 2 * Softmax.trips L * d.i + Softmax.wbPos d + Softmax.elPos d
  | _ => 0

/-- No softmax site fires a ballot. -/
theorem ev_not_vote {g : Nat} {d : Softmax.D} {e : Event} (hev : Softmax.Ev L g d e)
    (m a b) : e.kind ≠ .vote m a b := by
  intro hk
  unfold Softmax.Ev at hev
  cases hs : d.site <;> simp [hs, hk] at hev

/-- A warp collective that is not a ballot is a shuffle, an election or a warp barrier. -/
theorem coll_split {e : Event} (hv : ∀ m a b, e.kind ≠ .vote m a b) :
    (if Sched.isWarpColl e then 1 else 0) = (if Execution.isShfl e then 1 else 0) +
      (if Softmax.isElectE e then 1 else 0) + (if Execution.isWarpBar e then 1 else 0) := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Sched.isWarpColl, Execution.isShfl, Softmax.isElectE, Execution.isWarpBar]

end SoftW

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- **The warp collectives of a softmax thread before a state.** -/
theorem soft_warp_cnt {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hw : warpOf L g < 8)
    (hk : k ≤ (X.tr g).length) (hσ : St L X g k = some (some d)) :
    ((X.tr g).take k).countP Sched.isWarpColl = SoftW.cnt L g d := by
  have hsplit : ((X.tr g).take k).countP Sched.isWarpColl =
      ((X.tr g).take k).countP Execution.isShfl + ((X.tr g).take k).countP Softmax.isElectE +
        ((X.tr g).take k).countP Execution.isWarpBar := by
    refine countP_split3 fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hjk : j < k := by
      have := List.length_take_le k (X.tr g)
      omega
    rw [List.getElem_take]
    have hjl : j < (X.tr g).length := by omega
    have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hjl
    obtain ⟨d', hσ'⟩ := Frame.stateAt_live (C := code L) ht hg hσ hjk.le
    refine SoftW.coll_split fun m a b hv => ?_
    rcases soft_origin hpre hX ht he hw (not_ub hpre hX ht hok hg hσ' he) with
      ⟨_, _, hpk⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hev⟩
    · rw [hv] at hpk; exact hpk
    · exact SoftW.ev_not_vote hev m a b hv
  obtain ⟨hJ, hS, -⟩ := runInv_at hpre hX ht hok (shflJ_run hpre hg) hg hk hσ
  obtain ⟨-, hinv, hwr⟩ := state_facts hpre hX ht hok hg hk hσ
  rw [hsplit, hS]
  rcases role_cases hwr with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
      ⟨-, s, rfl⟩ | ⟨hw', hw'', -⟩
  · obtain ⟨hall, hel, hel0⟩ := hJ
    have hpi : Prologue.Inv L g p := hinv
    have hwb : ((X.tr g).take k).countP Execution.isWarpBar = 0 :=
      List.countP_eq_zero.mpr fun x hx => by
        have := hall x hx
        obtain ⟨pc, kx⟩ := x
        cases kx <;> simp_all [Prologue.ProKind, Execution.isWarpBar]
    have hce : ((X.tr g).take k).countP Softmax.isElectE =
        ((X.tr g).take k).countP (Prologue.isElect ·.kind) :=
      List.countP_congr fun x _ => by
        obtain ⟨pc, kx⟩ := x
        cases kx <;> simp [Softmax.isElectE, Prologue.isElect]
    rw [hwb, hce]
    simp only [shflCnt, SoftW.cnt, SoftW.proCnt]
    by_cases hw0 : warpOf L g = 0
    · simp [hel0 hw0, hw0]
    · rw [hel hw0]
      obtain ⟨s⟩ := p
      have h12 : s ≠ .init320 := fun h => by have := hpi.warp12 (.inr h); omega
      have hw12 : warpOf L g ≠ 12 := by omega
      cases s <;> simp_all [Prologue.Site.elects]
  all_goals (try omega)
  have hc : Softmax.Counts L g s ((X.tr g).take k) := hJ
  rw [hc.elects, hc.warpBar]
  simp only [shflCnt, SoftW.cnt, SoftW.pro]
  split_ifs <;> ring

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
