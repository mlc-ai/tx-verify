-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedSoftWarpTime
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarp

@[expose] public section

/-! # The softmax warps' warp collectives: schedule and exit counts

**Schedule** (`softWarpSched`). The prologue of warps 1 to 7 makes the four shuffles (`shfl0`,
`shfl1`, `shfl2` at `0`, `2`, `4`, the rank broadcast `shfl3` at `24`) and no election. Warp 0
makes the three shuffles, its first two elections (`12`, `18`), the rank broadcast (`24`) and
its other twelve elections (`28` to `110`; `proS0`). Their roles make a warp barrier and an
election per tile (`SoftW.wS`). The schedule `softS` is the prologue's times, then the role's
(`pro_time`, `SoftW.role_time`). Every time is even, so a state before a collective is more
than one before it.

**Exit counts** (`soft_exit_cnt`). At the exit a softmax thread has made the prologue's
collectives (`SoftW.pro`) and two per tile of its `T` items; two lanes of a warp have one warp
index and one item count, so they agree (`softWarpExitAgree`), and a lane at a warp collective
has made fewer (`softWarpExitAbove`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace SoftW

/-- The prologue's shuffles of warps 1 to 7. -/
def proS1 : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | _ => 24

/-- The prologue's collectives of warp 0: three shuffles, two elections, the rank broadcast,
twelve elections (`Time.prologue`). -/
def proS0 : Nat → Nat
  | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 12 | 4 => 18 | 5 => 24 | 6 => 28 | 7 => 42 | 8 => 56
  | 9 => 62 | 10 => 68 | 11 => 74 | 12 => 80 | 13 => 86 | 14 => 92 | 15 => 98 | 16 => 104
  | _ => 110

/-- The prologue's collectives of softmax warp `w`. -/
def proS (w k : Nat) : Nat := if w = 0 then proS0 k else proS1 k

/-- The warp collectives' schedule of softmax warp `w`. -/
def softS (n T w k : Nat) : Nat :=
  if k < pro w then proS w k else wS n T (w / 4) (k - pro w)

theorem proS_gap (w k : Nat) (hk : k + 1 < pro w) : proS w k + 1 < proS w (k + 1) := by
  have h0 : ∀ k, k < 17 → proS0 k + 1 < proS0 (k + 1) := by decide
  have h1 : ∀ k, k < 3 → proS1 k + 1 < proS1 (k + 1) := by decide
  unfold pro at hk
  unfold proS
  split_ifs at hk ⊢
  · exact h0 k (by omega)
  · exact h1 k (by omega)

theorem proS_le (w k : Nat) : proS w k ≤ 110 := by
  unfold proS proS0 proS1
  split_ifs <;> split <;> decide

theorem softS_gap (n T w k : Nat) : softS n T w k + 1 < softS n T w (k + 1) := by
  unfold softS
  by_cases h3 : k + 1 < pro w
  · simp only [show k < pro w by omega, h3, ↓reduceIte]
    exact proS_gap w k h3
  · by_cases h0 : k < pro w
    · have hk : k + 1 - pro w = 0 := by omega
      have := wS_ge n T (w / 4) 0
      have := proS_le w k
      simp only [h0, h3, ↓reduceIte, hk]
      simp only [base] at *
      omega
    · simp only [h0, h3, ↓reduceIte, show k + 1 - pro w = k - pro w + 1 by omega]
      exact wS_gap _ _ _ _

theorem softS_even (n T w k : Nat) : softS n T w k % 2 = 0 := by
  unfold softS
  split_ifs
  · unfold proS proS0 proS1; split_ifs <;> split <;> decide
  · exact wS_even _ _ _ _

theorem prologue_even (s : Prologue.Site) : prologue s % 2 = 0 := by
  cases s <;> simp only [prologue, clArriveT, clWaitT] <;> (try split_ifs) <;> omega

/-- The prologue's warp collectives at a warp-collective site are fewer than all of them. -/
theorem proCnt_lt {w : Nat} {s : Prologue.Site} (hk : prologueKind s = .warp)
    (hw : w = 0 ∨ s ≠ .elect12) (h0 : w ≠ 0 → ∀ e, s ≠ .elect e) : proCnt w s < pro w := by
  cases s <;> simp only [prologueKind, reduceCtorEq] at hk <;>
    simp only [proCnt, pro, Prologue.Site.shfls, Prologue.Site.elects0]
  case elect e =>
    by_cases hw0 : w = 0
    · have := e.isLt; simp only [hw0, ↓reduceIte]; split_ifs <;> omega
    · exact absurd rfl (h0 hw0 e)
  case elect12 => simp_all
  all_goals (by_cases hw0 : w = 0 <;> simp [hw0])

/-- Warp 0's elections are at their schedule times. -/
theorem elect0_time : ∀ e : Fin 14,
    proCnt 0 (.elect e) < 18 ∧ prologue (.elect e) = proS0 (proCnt 0 (.elect e)) := by
  decide

/-- Warp 0's initializations are before the next collective. -/
theorem init0_time : ∀ j : Fin 36, proCnt 0 (.init j) ≤ 18 ∧
    (proCnt 0 (.init j) < 18 → prologue (.init j) < proS0 (proCnt 0 (.init j))) ∧
    prologue (.init j) < base := by
  decide

/-- **The prologue's sites against the schedule**, at the sites of softmax warp `w` (warp 0's
elections and initializations only in warp 0, those of warp 12 in none). -/
theorem pro_time (n T : Nat) {w : Nat} {s : Prologue.Site}
    (h0 : w ≠ 0 → (∀ e, s ≠ .elect e) ∧ ∀ j, s ≠ .init j) (h12 : s ≠ .elect12)
    (h320 : s ≠ .init320) :
    (prologueKind s = .warp → prologue s = softS n T w (proCnt w s)) ∧
    (prologueKind s ≠ .warp → prologue s < softS n T w (proCnt w s)) := by
  have hge := wS_ge n T (w / 4) 0
  simp only [base] at hge
  by_cases hw0 : w = 0
  · subst hw0
    have hge' : 256 ≤ wS n T 0 0 := by simpa using hge
    cases s
    all_goals (try exact absurd rfl h12)
    all_goals (try exact absurd rfl h320)
    case elect e =>
      obtain ⟨hlt, heq⟩ := elect0_time e
      simp only [prologueKind, softS, pro, proS, ↓reduceIte, hlt]
      exact ⟨fun _ => heq, fun h => absurd rfl h⟩
    case init j =>
      obtain ⟨hle, hlt, hb⟩ := init0_time j
      simp only [prologueKind, softS, pro, proS, ↓reduceIte, ne_eq, reduceCtorEq,
        IsEmpty.forall_iff, not_false_eq_true, true_implies, true_and]
      split_ifs with h
      · exact hlt h
      · simp only [base] at hb
        rw [show proCnt 0 (.init j) - 18 = 0 by omega]
        omega
    all_goals simp only [prologueKind, softS, pro, proS, proS0, proCnt, Prologue.Site.shfls,
      Prologue.Site.elects0, prologue, ↓reduceIte, clArriveT, clWaitT]
    all_goals simp (config := { decide := true })
    all_goals omega
  · obtain ⟨he, hj⟩ := h0 hw0
    cases s
    all_goals (try exact absurd rfl h12)
    all_goals (try exact absurd rfl h320)
    all_goals (try exact absurd rfl (he _))
    all_goals (try exact absurd rfl (hj _))
    all_goals simp only [prologueKind, softS, pro, proS, proS1, proCnt, Prologue.Site.shfls,
      hw0, prologue, ↓reduceIte, clArriveT, clWaitT, Nat.add_zero]
    all_goals simp (config := { decide := true })
    all_goals omega

end SoftW

theorem sameWarp_warp {g h : Nat} (hs : SameWarp L g h) : warpOf L h = warpOf L g := by
  have := hs.2
  simp only [warpOf] at this ⊢
  omega

theorem sameWarp_items {g h : Nat} (hs : SameWarp L g h) :
    Softmax.items L g = Softmax.items L h := by
  obtain ⟨⟨-, -, hc⟩, -⟩ := hs
  simp only [Softmax.items, Work.T, Work.cid, clusterOf, ctaOf]
  rw [hc]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- **The schedule of the softmax warps' warp collectives.** -/
theorem softWarpSched :
    WarpSchedG L X (fun g => warpOf L g < 8)
      (fun c k => SoftW.softS (Work.n L) (Tc L c.1) c.2 k) := by
  have hn : 0 < Work.n L := Mma.trips_pos hpre
  have htime : ∀ {g k : Nat} {d : ThreadD}, g < L.threads → warpOf L g < 8 →
      k ≤ (X.tr g).length → St L X g k = some (some d) →
        (nextKind d = .warp → stateTime L g d =
          SoftW.softS (Work.n L) (Tc L (warpKey L g).1) (warpKey L g).2 (SoftW.cnt L g d)) ∧
        (nextKind d ≠ .warp → stateTime L g d <
          SoftW.softS (Work.n L) (Tc L (warpKey L g).1) (warpKey L g).2 (SoftW.cnt L g d)) := by
    intro g k d hg hG hk hσ
    obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨⟨s⟩, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
        ⟨-, s, rfl⟩ | ⟨hw', hw'', -⟩
    · have hi : Prologue.Inv L g ⟨s⟩ := hinv
      simp only [stateTime, SoftW.cnt, nextKind, warpKey]
      refine SoftW.pro_time _ _ (fun hw0 => ⟨fun e he => hw0 (hi.warp0 (.inl ⟨e, he⟩)),
        fun j hj => hw0 (hi.warp0 (.inr ⟨j, hj⟩))⟩) (fun h => ?_) (fun h => ?_)
      · have := hi.warp12 (.inl h); omega
      · have := hi.warp12 (.inr h); omega
    all_goals (try omega)
    have h := SoftW.role_time hn (hinv : Softmax.Inv L g s) (st := warpOf L g / 4) (by omega)
    simp only [stateTime, SoftW.cnt, SoftW.softS, warpKey]
    have hr : ¬ (SoftW.pro (warpOf L g) + 2 * Softmax.trips L * s.i + Softmax.wbPos s +
        Softmax.elPos s < SoftW.pro (warpOf L g)) := by omega
    simp only [hr, ↓reduceIte]
    rw [show SoftW.pro (warpOf L g) + 2 * Softmax.trips L * s.i + Softmax.wbPos s +
          Softmax.elPos s - SoftW.pro (warpOf L g) =
        2 * Work.n L * s.i + Softmax.wbPos s + Softmax.elPos s by
          simp only [show Softmax.trips L = Work.n L from rfl]; omega]
    exact h
  refine warpSched_of hpre hX hok (fun g d => SoftW.cnt L g d)
    (fun hg hG hk hσ => soft_warp_cnt hpre hX ht hok hg hG hk hσ) htime ?_
    (fun c k => SoftW.softS_gap _ _ _ k)
  intro g d e hg hG h0 hσ he hp
  have hk : (X.tr g).length - 1 ≤ (X.tr g).length := Nat.sub_le _ 1
  have hnk : nextKind d ≠ .warp := by
    intro h
    have := (fired_kind hpre hX hok hg hσ he).1
    rw [h, hp] at this
    simp at this
  have hlt := (htime hg hG hk hσ).2 hnk
  have he2 := SoftW.softS_even (Work.n L) (Tc L (warpKey L g).1) (warpKey L g).2
    (SoftW.cnt L g d)
  have he1 : stateTime L g d % 2 = 0 := by
    obtain ⟨-, -, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨⟨s⟩, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
        ⟨-, s, rfl⟩ | ⟨hw', hw'', -⟩
    · exact SoftW.prologue_even s
    all_goals (try omega)
    exact SoftW.soft_even _ _ _ s
  omega

/-- **The softmax part of `Sched.warpSched`.** -/
theorem softWarpRoleSched : WarpRoleSched L X (· < 8) :=
  ⟨_, softWarpSched hpre hX ht hok⟩

/-- The warp collectives of a softmax thread at its exit. -/
theorem soft_exit_cnt {g k pc : Nat} (hw : warpOf L g < 8)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ((X.tr g).take k).countP Sched.isWarpColl =
      SoftW.pro (warpOf L g) + 2 * Softmax.trips L * Softmax.items L g := by
  obtain ⟨d, hσ, hc, hi, hs⟩ := soft_exit_state hpre hX ht hw he
  have hg := Frame.lt_of_get hX he
  have hlen : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  rw [soft_warp_cnt hpre hX ht hok hg hw hlen hσ]
  obtain ⟨site, i, t, w, m, l⟩ := d
  simp only at hs
  subst hs
  obtain ⟨hiT, -⟩ := hi.tail (by simp)
  simp only at hiT
  subst hiT
  simp [SoftW.cnt, Softmax.wbPos, Softmax.elPos, Softmax.Site.tile0, Softmax.Site.inTrip]

/-- **The softmax part of `Cross.WarpExitAgree`.** -/
theorem softWarpExitAgree {g h k k' pc pc' : Nat} (hw : warpOf L g < 8) (hs : SameWarp L g h)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) (he' : X.get (h, k') = some ⟨pc', .exit⟩) :
    ((X.tr g).take k).countP Sched.isWarpColl = ((X.tr h).take k').countP Sched.isWarpColl := by
  have hwh := sameWarp_warp hs
  rw [soft_exit_cnt hpre hX ht hok hw he, soft_exit_cnt hpre hX ht hok (hwh ▸ hw) he', hwh,
    sameWarp_items hs]

/-- **The softmax part of `Cross.WarpExitAbove`.** -/
theorem softWarpExitAbove {g h k pc : Nat} {d : ThreadD} (hw : warpOf L g < 8)
    (hs : SameWarp L g h) (hσ : St L X g (X.tr g).length = some (some d))
    (hk : nextKind d = .warp) (he : X.get (h, k) = some ⟨pc, .exit⟩) :
    (X.tr g).countP Sched.isWarpColl < ((X.tr h).take k).countP Sched.isWarpColl := by
  have hwh := sameWarp_warp hs
  have hg := hs.1.1
  rw [soft_exit_cnt hpre hX ht hok (hwh ▸ hw) he, hwh, ← sameWarp_items hs]
  have hc := soft_warp_cnt hpre hX ht hok hg hw le_rfl hσ
  rw [List.take_length] at hc
  rw [hc]
  obtain ⟨-, hinv, hwr⟩ := state_facts hpre hX ht hok hg le_rfl hσ
  rcases role_cases hwr with ⟨⟨s⟩, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
      ⟨-, s, rfl⟩ | ⟨hw', hw'', -⟩
  · have hi : Prologue.Inv L g ⟨s⟩ := hinv
    have := SoftW.proCnt_lt (w := warpOf L g) hk
      (by by_cases h0 : warpOf L g = 0
          · exact .inl h0
          · exact .inr fun h => by have := hi.warp12 (.inl h); omega)
      (fun h0 e he => h0 (hi.warp0 (.inl ⟨e, he⟩)))
    dsimp only at this
    simp only [SoftW.cnt]
    omega
  all_goals (try omega)
  have hi : Softmax.Inv L g s := hinv
  obtain ⟨site, i, t, w, m, l⟩ := s
  have hiT := hi.item
  have htr := hi.trip
  simp only at hiT htr
  simp only [nextKind, softmaxKind] at hk
  have hlt : ∀ {a b : Nat}, a < b → 2 * Softmax.trips L * a + 2 * Softmax.trips L ≤
      2 * Softmax.trips L * b := fun {a b} hab => by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hab
  have h1 := soft_trips_pos hpre
  clear hc hσ
  cases site <;> simp only [reduceCtorEq] at hk
  all_goals rename_i lp
  all_goals have hiT' := hlt (hiT rfl)
  all_goals cases lp <;> simp only [SoftW.cnt, Softmax.wbPos, Softmax.elPos,
    Softmax.Site.tile0, Softmax.Site.inTrip, Softmax.tileNo, Softmax.Site.afterWB,
    Softmax.Site.afterEl, Bool.true_or, Bool.or_true, ↓reduceIte,
    Bool.false_eq_true, forall_const] at htr ⊢
  all_goals omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
