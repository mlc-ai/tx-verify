-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpPos
public import Kernels.FlashAttn4Fwd.Proof.Thread.TrackedCount
public import Kernels.FlashAttn4Fwd.Proof.Thread.InitFacts
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarId

@[expose] public section

/-! # The warp collectives of the store and idle warps

Warps 13 and 15 make only the prologue's four shuffles (`shfl0`, `shfl1`, `shfl2` at `0`, `2`,
`4`, the rank broadcast `shfl3` at `24`): their prologue has no election (those of warps 0 and
12), their roles no warp collective. So their warp collectives before a state are its shuffles
(`shflCnt`, `TrackedCount.shflJ`), and the schedule `quietS` is the shuffles' times, then the
tail. All their times are even (`even_time`), so a state before a collective is more than one
before it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The warp collectives' schedule of warps 13 and 15. -/
def quietS (n T : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 24
  | k + 4 => tailTime n T (4000 + 2 * k)

theorem quietS_gap (n T k : Nat) : quietS n T k + 1 < quietS n T (k + 1) := by
  match k with
  | 0 => simp [quietS]
  | 1 => simp [quietS]
  | 2 => simp [quietS]
  | 3 => simp only [quietS, tailTime]; exact Progress.Time.fixed_lt (by decide)
  | k + 4 =>
    show tailTime n T (4000 + 2 * k) + 1 < tailTime n T (4000 + 2 * (k + 1))
    unfold tailTime slotTime; omega

theorem slot_even {n i s o : Nat} (ho : o % 2 = 0) : slotTime n i s o % 2 = 0 := by
  unfold slotTime; simp only [base, span]; omega

theorem quietS_even (n T k : Nat) : quietS n T k % 2 = 0 := by
  match k with
  | 0 | 1 | 2 | 3 => simp [quietS]
  | k + 4 => exact slot_even (by omega)

/-- The store and idle warps' and the prologue's times are even. -/
theorem even_time {g : Nat} (d : ThreadD) (hd : ∀ m, d ≠ .inr (.loader m))
    (hm : ∀ m, d ≠ .inr (.mma m)) (hs : ∀ m, d ≠ .inr (.softmax m))
    (hc : ∀ m, d ≠ .inr (.corr m)) : stateTime L g d % 2 = 0 := by
  rcases d with p | r
  · obtain ⟨s⟩ := p
    cases s <;> simp only [stateTime, prologue, clArriveT, clWaitT] <;> (try split_ifs) <;> omega
  · cases r with
    | idle s => obtain ⟨site⟩ := s; cases site <;> simp [stateTime, idle, regT, idleExitT]
    | loader l => exact absurd rfl (hd l)
    | mma m => exact absurd rfl (hm m)
    | store s =>
      obtain ⟨s, i⟩ := s
      cases s <;> simp only [stateTime, store, storeAt, tailTime, regT] <;>
        first | exact slot_even (by unfold bandST; omega) | exact slot_even (by omega)
    | softmax sd => exact absurd rfl (hs sd)
    | corr cd => exact absurd rfl (hc cd)

theorem isShfl_warp {e : Event} (h : Execution.isShfl e = true) : Sched.isWarpColl e = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Execution.isShfl, Sched.isWarpColl]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- A state of warp 13 or 15: a prologue state off the elections, or a store or idle state. -/
theorem quiet_state {g k : Nat} {d : ThreadD} (hg : g < L.threads)
    (hG : warpOf L g = 13 ∨ warpOf L g = 15) (hk : k ≤ (X.tr g).length)
    (hσ : St L X g k = some (some d)) :
    (∃ s, d = .inl ⟨s⟩ ∧ (∀ e, s ≠ .elect e) ∧ (∀ j, s ≠ .init j) ∧ s ≠ .elect12 ∧
      s ≠ .init320) ∨ (∃ s, d = .inr (.store s)) ∨ (∃ s, d = .inr (.idle s)) := by
  obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
  rcases role_cases hw with ⟨⟨s⟩, rfl⟩ | ⟨-, s, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨-, s, rfl⟩ |
      ⟨hw', -⟩ | ⟨hw', hw'', -⟩
  · have hi : Prologue.Inv L g ⟨s⟩ := hinv
    refine .inl ⟨s, rfl, fun e he => ?_, fun j hj => ?_, fun h => ?_, fun h => ?_⟩
    · have := hi.warp0 (.inl ⟨e, he⟩); omega
    · have := hi.warp0 (.inr ⟨j, hj⟩); omega
    · have := hi.warp12 (.inl h); omega
    · have := hi.warp12 (.inr h); omega
  · exact .inr (.inr ⟨s, rfl⟩)
  · omega
  · omega
  · exact .inr (.inl ⟨s, rfl⟩)
  · omega
  · omega

/-- **The store and idle warps' schedule of warp collectives.** -/
theorem quietWarpSched :
    WarpSchedG L X (fun g => warpOf L g = 13 ∨ warpOf L g = 15)
      (fun c k => quietS (Work.n L) (Tc L c.1) k) := by
  -- the warp collectives are the shuffles
  have hev : ∀ {g j : Nat} {d : ThreadD} {e : Event}, g < L.threads →
      (warpOf L g = 13 ∨ warpOf L g = 15) → j < (X.tr g).length →
      St L X g j = some (some d) → X.get (g, j) = some e →
      Sched.isWarpColl e = Execution.isShfl e := by
    intro g j d e hg hG hj hσ he
    have hk := (fired_kind hpre hX hok hg hσ he).1
    rcases quiet_state hpre hX ht hok hg hG hj.le hσ with
      ⟨s, rfl, h1, h2, h3, h4⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
    · have hE := pro_event hpre hX he hσ
        (fun f h => not_ub hpre hX ht hok hg hσ he e.pc f (by rw [← h]))
      obtain ⟨pc, k⟩ := e
      cases s <;> simp only [Prologue.EvOk] at hE
      all_goals (try exact absurd rfl (h1 _))
      all_goals (try exact absurd rfl (h2 _))
      all_goals (try exact absurd rfl h3)
      all_goals (try exact absurd rfl h4)
      all_goals (try (obtain ⟨_, _, _, _, _, _, hE⟩ := hE))
      all_goals (try (obtain ⟨_, hE⟩ := hE))
      all_goals rfl
    all_goals
      have hf : Sched.isWarpColl e = false := by
        rw [hk]; cases hs : s.site <;> simp [nextKind, storeKind, idleKind, hs]
      rw [hf]
      cases h : Execution.isShfl e
      · rfl
      · rw [isShfl_warp h] at hf; cases hf
  have hcnt : ∀ {g k : Nat} {d : ThreadD}, g < L.threads →
      (warpOf L g = 13 ∨ warpOf L g = 15) → k ≤ (X.tr g).length →
      St L X g k = some (some d) → ((X.tr g).take k).countP Sched.isWarpColl = shflCnt L g d := by
    intro g k d hg hG hk hσ
    have h := Sched.countP_take_congr (p := Sched.isWarpColl) (q := Execution.isShfl) ht hg hσ
      fun {j d' e} hj hσ' he => hev hg hG (by omega) hσ' he
    rw [h]
    exact (runInv_at hpre hX ht hok (shflJ_run hpre hg) hg hk hσ).2.1
  have htime : ∀ {g k : Nat} {d : ThreadD}, g < L.threads →
      (warpOf L g = 13 ∨ warpOf L g = 15) → k ≤ (X.tr g).length →
      St L X g k = some (some d) →
        (nextKind d = .warp →
          stateTime L g d = quietS (Work.n L) (Tc L (warpKey L g).1) (shflCnt L g d)) ∧
        (nextKind d ≠ .warp →
          stateTime L g d < quietS (Work.n L) (Tc L (warpKey L g).1) (shflCnt L g d)) := by
    intro g k d hg hG hk hσ
    obtain ⟨-, hinv, -⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases quiet_state hpre hX ht hok hg hG hk hσ with
      ⟨s, rfl, h1, h2, h3, h4⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
    · cases s
      all_goals (try exact absurd rfl (h1 _))
      all_goals (try exact absurd rfl (h2 _))
      all_goals (try exact absurd rfl h3)
      all_goals (try exact absurd rfl h4)
      all_goals simp only [stateTime, prologue, shflCnt, Prologue.Site.shfls, quietS, nextKind,
        prologueKind, ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false,
        IsEmpty.forall_iff, true_implies, and_true, true_and, clArriveT, clWaitT]
      all_goals first | decide | (unfold tailTime slotTime; simp only [base]; omega)
    · simp only [stateTime, shflCnt, quietS, nextKind]
      refine ⟨fun h => by cases hs : s.site <;> simp [storeKind, hs] at h, fun _ => ?_⟩
      exact (Store.time_lt hinv).trans (Progress.Time.tail_lt (by omega))
    · simp only [stateTime, shflCnt, quietS, nextKind]
      refine ⟨fun h => by obtain ⟨site⟩ := s; cases site <;> simp [idleKind] at h, fun _ => ?_⟩
      exact Idle.time_lt s.site
  refine warpSched_of hpre hX hok (fun g d => shflCnt L g d) hcnt htime ?_
    (fun c k => quietS_gap _ _ k)
  intro g d e hg hG h0 hσ he hp
  have hlen := Sched.len_pos_of_stop h0
  have hk : (X.tr g).length - 1 ≤ (X.tr g).length := Nat.sub_le _ 1
  have hnk : nextKind d ≠ .warp := by
    intro h
    have := (fired_kind hpre hX hok hg hσ he).1
    rw [h, hp] at this
    simp at this
  have hlt := (htime hg hG hk hσ).2 hnk
  have he1 := even_time (L := L) (g := g) d
    (by rcases quiet_state hpre hX ht hok hg hG hk hσ with ⟨s, rfl, -⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
      simp)
    (by rcases quiet_state hpre hX ht hok hg hG hk hσ with ⟨s, rfl, -⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
      simp)
    (by rcases quiet_state hpre hX ht hok hg hG hk hσ with ⟨s, rfl, -⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
      simp)
    (by rcases quiet_state hpre hX ht hok hg hG hk hσ with ⟨s, rfl, -⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
      simp)
  have he2 := quietS_even (Work.n L) (Tc L (warpKey L g).1) (shflCnt L g d)
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
