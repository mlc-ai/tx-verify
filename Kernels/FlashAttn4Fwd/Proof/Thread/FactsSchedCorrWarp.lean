-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedCorrVote
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTcAgree

@[expose] public section

/-! # The correction warps' warp collectives (`WarpRoleSched`, the exit counts)

A correction warp's warp collectives are its shuffles and its votes: its prologue has no
election (those of warps 0 and 12) and no correction site makes a shuffle, an election or a warp
barrier (`warp_ev`). Before a state there are `shflCnt` shuffles (four from the role's entry on)
and `V i + votePos 0 + votePos 1` votes (`Counts.voteN`), so the count is a function of the state
(`warp_cnt`). Against the schedule `corrWS` (`Thread/FactsSchedCorrVote.lean`) a state at a
vote or a shuffle is at its time and every other state earlier; all these times are even, so a
stopped machine's last state is more than one before the next collective (`corrWarpSched`).

At its exit a correction lane has made `4 + V T` warp collectives (`corr_exit_warp`), the same for
the lanes of a warp (one cluster, one `T`), and more than a lane of its warp at a shuffle or a vote
(`Cross.WarpExitAgree_corr`, `Cross.WarpExitAbove_corr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time CorrTc CorrW

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem prologue_not_vote {es : List Event} (h : ∀ x ∈ es, Prologue.ProKind x.kind) :
    es.countP Correction.isVote = 0 := by
  refine List.countP_eq_zero.mpr fun x hx => ?_
  have := h x hx
  obtain ⟨pc, k⟩ := x
  cases k <;> simp_all [Prologue.ProKind, Correction.isVote]

theorem countP_shfl_vote (l : List Event) :
    l.countP (fun e => Execution.isShfl e || Correction.isVote e) =
      l.countP Execution.isShfl + l.countP Correction.isVote := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, ih]
    obtain ⟨pc, k⟩ := x
    cases k <;> (simp [Execution.isShfl, Correction.isVote]; try omega)

/-- The votes of the current item before a correction state. -/
def vCnt (L : Launch) : ThreadD → Nat
  | .inr (.corr c) => nV (Work.n L) * c.i + Correction.votePos L 0 c + Correction.votePos L 1 c
  | _ => 0

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- **A correction lane's warp collectives are its shuffles and its votes.** -/
theorem warp_ev {g j : Nat} {d : ThreadD} {e : Event} (hg : g < L.threads)
    (hG : 8 ≤ warpOf L g ∧ warpOf L g < 12) (hj : j ≤ (X.tr g).length)
    (hσ : St L X g j = some (some d)) (he : X.get (g, j) = some e) :
    Sched.isWarpColl e = (Execution.isShfl e || Correction.isVote e) := by
  have hub := not_ub hpre hX ht hok hg hσ he
  obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hj hσ
  rcases role_cases hw with ⟨⟨s⟩, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
      ⟨hw', -⟩ | ⟨-, -, c, rfl⟩
  · have hi : Prologue.Inv L g ⟨s⟩ := hinv
    have hE := pro_event hpre hX he hσ (fun f h => hub e.pc f (by rw [← h]))
    obtain ⟨pc, k⟩ := e
    cases k
    all_goals first
      | rfl
      | (cases s <;> simp [Prologue.EvOk] at hE <;>
          first
            | (have := hi.warp12 (.inl rfl); omega)
            | (have := hi.warp0 (.inl ⟨_, rfl⟩); omega))
  all_goals (try omega)
  rcases corr_origin hpre hX ht he hG.1 hG.2 hub with ⟨p, hp, -⟩ |
    ⟨c', t, ins, o, hc', -, -, -, -, -, hev⟩
  · have : St L X g j = some (some (.inl p)) := hp
    rw [hσ] at this
    cases this
  · have : St L X g j = some (some (.inr (.corr c'))) := hc'
    rw [hσ] at this
    simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at this
    subst this
    obtain ⟨pc, k⟩ := e
    cases k
    all_goals first
      | rfl
      | (obtain ⟨-, hk⟩ := hev (by simp)
         obtain ⟨site, i, t, aw, a, o⟩ := c
         cases site <;> simp at hk)

/-- **The warp collectives before a correction lane's state.** -/
theorem warp_cnt {g k : Nat} {d : ThreadD} (hg : g < L.threads)
    (hG : 8 ≤ warpOf L g ∧ warpOf L g < 12) (hk : k ≤ (X.tr g).length)
    (hσ : St L X g k = some (some d)) :
    ((X.tr g).take k).countP Sched.isWarpColl = shflCnt L g d + vCnt L d := by
  have h := Sched.countP_take_congr (p := Sched.isWarpColl)
    (q := fun e => Execution.isShfl e || Correction.isVote e) ht hg hσ
    fun {j d' e} hj hσ' he => warp_ev hpre hX ht hok hg hG (by omega) hσ' he
  rw [h, countP_shfl_vote, (runInv_at hpre hX ht hok (shflJ_run hpre hg) hg hk hσ).2.1]
  obtain ⟨hJ, -, hw⟩ := state_facts hpre hX ht hok hg hk hσ
  congr 1
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
      ⟨hw', -⟩ | ⟨-, -, c, rfl⟩
  · exact prologue_not_vote hJ.1
  all_goals (try omega)
  exact hJ.voteN

/-- **The correction warps' schedule of warp collectives.** -/
theorem corrWarpSched : WarpRoleSched L X (fun w => 8 ≤ w ∧ w < 12) := by
  have htime : ∀ {g k : Nat} {d : ThreadD}, g < L.threads →
      (8 ≤ warpOf L g ∧ warpOf L g < 12) → k ≤ (X.tr g).length →
      St L X g k = some (some d) →
        (nextKind d = .warp → stateTime L g d =
          corrWS (Work.n L) (Tc L (warpKey L g).1) (shflCnt L g d + vCnt L d)) ∧
        (nextKind d ≠ .warp → stateTime L g d <
          corrWS (Work.n L) (Tc L (warpKey L g).1) (shflCnt L g d + vCnt L d)) := by
    intro g k d hg hG hk hσ
    rw [show Tc L (warpKey L g).1 = Work.T L g from rfl]
    have hv := voteS_ge (Work.n L) (Work.T L g) 0
    simp only [base] at hv
    obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨⟨s⟩, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
        ⟨hw', -⟩ | ⟨-, -, c, rfl⟩
    · have hi : Prologue.Inv L g ⟨s⟩ := hinv
      cases s
      all_goals (try (exfalso; have := hi.warp12 (.inl rfl); omega))
      all_goals (try (exfalso; have := hi.warp12 (.inr rfl); omega))
      all_goals (try (exfalso; have := hi.warp0 (.inl ⟨_, rfl⟩); omega))
      all_goals (try (exfalso; have := hi.warp0 (.inr ⟨_, rfl⟩); omega))
      all_goals simp only [stateTime, prologue, shflCnt, vCnt, Prologue.Site.shfls,
        nextKind, prologueKind, ne_eq, reduceCtorEq, not_false_eq_true,
        not_true_eq_false, IsEmpty.forall_iff, true_implies, and_true, true_and, clArriveT,
        clWaitT, Nat.add_zero]
      all_goals simp only [corrWS, shflT, ↓reduceIte, Nat.reduceLT, Nat.reduceSub]
      all_goals omega
    all_goals (try omega)
    have hn : 0 < Work.n L := Mma.trips_pos hpre
    obtain ⟨hr, hwarp, hnw⟩ := siteW_ok hn (g := g) hinv
    have hS : corrWS (Work.n L) (Work.T L g)
        (shflCnt L g (.inr (.corr c)) + vCnt L (.inr (.corr c))) =
        voteS (Work.n L) (Work.T L g) (nV (Work.n L) * c.i + rOfW L c) := by
      simp only [shflCnt, vCnt, rOfW]
      unfold corrWS
      rw [ite_eq_right (by omega)]
      congr 1
      omega
    rw [hS]
    simp only [stateTime, nextKind]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨hiT, hr', heq⟩ := hwarp h
      rw [heq, voteS_at hiT hr']
    · rcases hnw h with ⟨hiT, hr', hlt⟩ | ⟨hiT, hr', hlt⟩ | hlt | ⟨hiT, hr', hlt⟩
      · rw [voteS_at hiT hr']
        exact hlt
      · rw [hr']
        exact lt_of_lt_of_le hlt (voteS_next hiT)
      · exact lt_of_lt_of_le hlt (voteS_ge _ _ _)
      · rw [hiT, hr', Nat.add_zero, voteS_tail]
        exact hlt
  refine ⟨fun c k => corrWS (Work.n L) (Tc L c.1) k,
    warpSched_of hpre hX hok (fun g d => shflCnt L g d + vCnt L d)
    (fun hg hG hk hσ => warp_cnt hpre hX ht hok hg hG hk hσ) htime ?_
    fun c k => corrWS_gap _ _ k⟩
  intro g d e hg hG h0 hσ he hp
  have hk : (X.tr g).length - 1 ≤ (X.tr g).length := Nat.sub_le _ 1
  have hnk : nextKind d ≠ .warp := by
    intro h
    have := (fired_kind hpre hX hok hg hσ he).1
    rw [h, hp] at this
    simp at this
  have hlt := (htime hg hG hk hσ).2 hnk
  have he1 : stateTime L g d % 2 = 0 := by
    obtain ⟨-, -, hw⟩ := state_facts hpre hX ht hok hg hk hσ
    rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
        ⟨hw', -⟩ | ⟨-, -, c, rfl⟩
    · exact even_time _ (by simp) (by simp) (by simp) (by simp)
    all_goals (try omega)
    exact corr_even _ _ c
  have he2 := corrWS_even (Work.n L) (Tc L (warpKey L g).1) (shflCnt L g d + vCnt L d)
  omega

/-- **The warp collectives of a correction lane at its exit.** -/
theorem corr_exit_warp {g k pc : Nat} (hg : g < L.threads) (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ((X.tr g).take k).countP Sched.isWarpColl = 4 + nV (Work.n L) * Work.T L g := by
  obtain ⟨d, hσ, -, hi, hs⟩ := corr_exit_state hpre hX ht hw hw' he
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  rw [warp_cnt hpre hX ht hok hg ⟨hw, hw'⟩ hk hσ]
  have hti := hi.tail (by rw [hs]; rfl) (by rw [hs]; simp) (by rw [hs]; simp)
    (fun _ => by rw [hs]; simp)
  obtain ⟨site, i, t, aw, a, o⟩ := d
  simp only at hs hti
  subst hs hti
  simp only [shflCnt, vCnt, Correction.votePos, Nat.add_zero]
  rfl

/-- **The correction part of `Cross.WarpExitAgree`.** -/
theorem Cross.WarpExitAgree_corr {g h k k' pc pc' : Nat} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hs : SameWarp L g h) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (he' : X.get (h, k') = some ⟨pc', .exit⟩) :
    ((X.tr g).take k).countP Sched.isWarpColl = ((X.tr h).take k').countP Sched.isWarpColl := by
  have hwh : warpOf L h = warpOf L g := hs.2.symm
  rw [corr_exit_warp hpre hX ht hok hs.1.1 hw hw' he,
    corr_exit_warp hpre hX ht hok hs.1.2.1 (by omega) (by omega) he', ← Corr.items_eq,
    ← Corr.items_eq, corr_items_eq hs]

/-- **The correction part of `Cross.WarpExitAbove`.** -/
theorem Cross.WarpExitAbove_corr {g h k pc : Nat} {d : ThreadD} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hs : SameWarp L g h)
    (hσ : St L X g (X.tr g).length = some (some d)) (hk : nextKind d = .warp)
    (he' : X.get (h, k) = some ⟨pc, .exit⟩) :
    (X.tr g).countP Sched.isWarpColl < ((X.tr h).take k).countP Sched.isWarpColl := by
  have hwh : warpOf L h = warpOf L g := hs.2.symm
  have hg := hs.1.1
  have hc := warp_cnt hpre hX ht hok hg ⟨hw, hw'⟩ le_rfl hσ
  rw [List.take_length] at hc
  rw [hc, corr_exit_warp hpre hX ht hok hs.1.2.1 (by omega) (by omega) he', ← Corr.items_eq,
    ← corr_items_eq hs, Corr.items_eq]
  obtain ⟨-, hinv, hw0⟩ := state_facts hpre hX ht hok hg le_rfl hσ
  rcases role_cases hw0 with ⟨⟨s⟩, rfl⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ | ⟨hw', -⟩ |
      ⟨hw', -⟩ | ⟨-, -, c, rfl⟩
  · have hi : Prologue.Inv L g ⟨s⟩ := hinv
    cases s
    all_goals (try (exfalso; have := hi.warp12 (.inl rfl); omega))
    all_goals (try (exfalso; have := hi.warp0 (.inl ⟨_, rfl⟩); omega))
    all_goals simp only [nextKind, prologueKind, reduceCtorEq] at hk
    all_goals simp only [shflCnt, vCnt, Prologue.Site.shfls]
    all_goals omega
  all_goals (try omega)
  obtain ⟨hiT, hr, -⟩ := (siteW_ok (Mma.trips_pos hpre) (g := g) hinv).2.1 hk
  have := Nat.mul_le_mul_left (nV (Work.n L)) (show c.i + 1 ≤ Work.T L g by omega)
  rw [Nat.mul_succ] at this
  simp only [shflCnt, vCnt]
  simp only [rOfW] at hr
  omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
