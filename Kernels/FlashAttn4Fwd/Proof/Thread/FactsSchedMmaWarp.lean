-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedMmaWarpTab

@[expose] public section

/-! # The MMA warp's schedule of warp collectives (`WarpRoleSched` of warp 12)

Warp 12's states are its prologue's, off warp 0's elections, and the MMA warp's (`mma_state`).
Its warp collectives before a state are `collM` (`mma_count`): the shuffles (`shflJ`: the
prologue's four, `shflQ`, `Mma.shA`), the elections (the prologue's one, `Mma.Counts.elects`),
and no warp barrier or ballot (`mma_noWV`). Every state is at the schedule `mmaS` or before it
(`mma_time`): the prologue's collectives and `shflQ` at the fixed times, the item sites by the
table (`mma_item`), the exit stage in the tail (past the items: `Counts.done` on the leader CTA,
no item on the other). The times of the schedule are even, and so are the MMA warp's but the
MMAs', at which the machine never stops (`Mma.next` continues on every event); hence the strict
clause of a stopped machine (`mmaWarpSched`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The elections before a state of warp 12. -/
def elCntM (L : Launch) (g : Nat) : ThreadD → Nat
  | .inl p => p.site.elects (warpOf L g)
  | .inr (.mma m) => 1 + Mma.cnt L Mma.elA 8 4 m
  | _ => 0

/-- The warp collectives before a state of warp 12. -/
def collM (L : Launch) (g : Nat) (d : ThreadD) : Nat := shflCnt L g d + elCntM L g d

theorem elects_mma (l : List Event) : l.countP Loader.isElectE = l.countP Mma.isElectE :=
  List.countP_congr fun x _ => by
    obtain ⟨pc, k⟩ := x
    cases k <;> simp [Loader.isElectE, Mma.isElectE]

theorem mmaS_fix (c : Nat × Nat) : mmaS L c 0 = 0 ∧ mmaS L c 1 = 2 ∧ mmaS L c 2 = 4 ∧
    mmaS L c 3 = 6 ∧ mmaS L c 4 = prologue .shfl3 ∧ mmaS L c 5 = shflQT := by
  unfold mmaS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Sched.ItemTab.sched_fix (by decide)] <;> rfl

/-- The MMA warp's times are even but at the MMAs. -/
theorem mma_even {n T : Nat} {d : Mma.D} (h : d.site.isMma = false) : mma n T d % 2 = 0 := by
  have he := List.all_eq_true.mp check_evenM d.site (Mma.mem_allSites _)
  simp only [h, Bool.false_or, beq_iff_eq] at he
  by_cases hs : Mma.ItemSite d.site
  · rw [time_itemM hs]
    exact slot_even (by unfold offM; omega)
  · obtain ⟨s, i, t, b, pro⟩ := d
    cases s <;> simp only [Mma.ItemSite, not_true_eq_false, not_false_eq_true] at hs
    all_goals simp only [mma, mmaTail, tailTime]
    all_goals first | decide | exact slot_even (by omega)

/-- The state after an MMA warp event, from the state before it. -/
theorem mma_succ {g j : Nat} {e : Event} {d : Mma.D}
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.mma d)))) :
    St L X g (j + 1) = (Mma.next L g d e).map (Option.map (.inr ∘ .mma)) := by
  unfold St at hσ ⊢
  rw [Frame.stateAt_succ he, hσ]
  rfl

theorem coll_phase0 {g : Nat} {s : Mma.Site} {t : Nat} {b : Value} {pro : Nat → Value}
    (h : s.phase = 0) : collM L g (.inr (.mma ⟨s, 0, t, b, pro⟩)) = 5 := by
  cases s <;> (try simp [Mma.Site.phase] at h) <;>
    simp [collM, shflCnt, elCntM, Mma.shfls, Mma.cnt, Mma.shA, Mma.elA, Mma.Site.after,
      Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord, Mma.Site.phase]

theorem coll_tailM {g : Nat} {s : Mma.Site} {i t : Nat} {b : Value} {pro : Nat → Value}
    (h : s.phase = 2) : collM L g (.inr (.mma ⟨s, i, t, b, pro⟩)) =
      fixM.length + ((14 * Work.n L + 6) * i + 0) := by
  have htn : Mma.trips L = Work.n L := rfl
  cases s <;> (try simp [Mma.Site.phase] at h) <;>
    simp [collM, shflCnt, elCntM, Mma.shfls, Mma.cnt, Mma.shA, Mma.elA, Mma.Site.after,
      Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord, Mma.Site.phase, fixM, htn] <;> ring

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- A state of warp 12: a prologue state off warp 0's elections, or an MMA warp state. -/
theorem mma_state {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hw : warpOf L g = 12)
    (hk : k ≤ (X.tr g).length) (hσ : St L X g k = some (some d)) :
    (∃ s, d = .inl ⟨s⟩ ∧ (∀ e, s ≠ .elect e) ∧ (∀ j, s ≠ .init j)) ∨
      ∃ m, d = .inr (.mma m) := by
  obtain ⟨-, hinv, hw'⟩ := state_facts hpre hX ht hok hg hk hσ
  rcases role_cases hw' with ⟨⟨s⟩, rfl⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, m, rfl⟩ | ⟨h', -⟩ |
      ⟨h', -⟩ | ⟨h', h'', -⟩
  · have hi : Prologue.Inv L g ⟨s⟩ := hinv
    refine .inl ⟨s, rfl, fun e he => ?_, fun j hj => ?_⟩
    · have := hi.warp0 (.inl ⟨e, he⟩); omega
    · have := hi.warp0 (.inr ⟨j, hj⟩); omega
  all_goals (try omega)
  exact .inr ⟨m, rfl⟩

/-- **Warp 12 makes no warp barrier and no ballot** before a followed state. -/
theorem mma_noWV {g k j : Nat} {d d' : ThreadD} {e : Event} (hg : g < L.threads)
    (hw : warpOf L g = 12) (hjk : j < k) (hσ : St L X g k = some (some d))
    (hσj : St L X g j = some (some d')) (he : X.get (g, j) = some e) : isWV e = false := by
  have hjl : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases mma_state hpre hX ht hok hg hw hjl.le hσj with ⟨s, rfl, -⟩ | ⟨m, rfl⟩
  · have hE := pro_event hpre hX he hσj
      (fun f h => not_ub hpre hX ht hok hg hσj he e.pc f (by rw [← h]))
    exact prologue_isWV hE.proKind
  · by_contra hv
    have hv : isWV e = true := by simpa using hv
    have hkind := (fired_kind hpre hX hok hg hσj he).1
    rw [isWV_warp hv] at hkind
    obtain ⟨d'', hσ'⟩ := Frame.stateAt_live (C := code L) ht hg hσ (show j + 1 ≤ k by omega)
    have hs := mma_succ he hσj
    change St L X g (j + 1) = _ at hσ'
    rw [hs] at hσ'
    obtain ⟨site, i, t, b, pro⟩ := m
    obtain ⟨pc, kk⟩ := e
    cases site <;> simp [nextKind, mmaKind] at hkind <;> cases kk <;> simp [isWV] at hv <;>
      simp [Mma.next] at hσ'

/-- **The warp collectives before a state of warp 12.** -/
theorem mma_count {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hw : warpOf L g = 12)
    (hk : k ≤ (X.tr g).length) (hσ : St L X g k = some (some d)) :
    ((X.tr g).take k).countP Sched.isWarpColl = collM L g d := by
  rw [warpColl_split]
  have hwv : ((X.tr g).take k).countP isWV = 0 := by
    rw [Sched.countP_take_congr (q := fun _ => false) ht hg hσ
      (fun hj hσj he => mma_noWV hpre hX ht hok hg hw hj hσ hσj he)]
    simp
  have hsh := (runInv_at hpre hX ht hok (shflJ_run hpre hg) hg hk hσ).2.1
  obtain ⟨hJ, -, -⟩ := state_facts hpre hX ht hok hg hk hσ
  rcases mma_state hpre hX ht hok hg hw hk hσ with ⟨s, rfl, -⟩ | ⟨m, rfl⟩
  · rw [hwv, hsh, elects_pro, hJ.2.1 (by omega)]; rfl
  · rw [hwv, hsh, elects_mma, (show Mma.Counts L g m _ from hJ).elects]; rfl

/-- **Every state of warp 12 against the schedule.** -/
theorem mma_time {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hw : warpOf L g = 12)
    (hk : k ≤ (X.tr g).length) (hσ : St L X g k = some (some d)) :
    (nextKind d = .warp → stateTime L g d = mmaS L (warpKey L g) (collM L g d)) ∧
    (nextKind d ≠ .warp → stateTime L g d < mmaS L (warpKey L g) (collM L g d)) := by
  obtain ⟨hJ, hinv, -⟩ := state_facts hpre hX ht hok hg hk hσ
  have hf := mmaS_fix (L := L) (warpKey L g)
  simp only [prologue, shflQT] at hf
  rcases mma_state hpre hX ht hok hg hw hk hσ with ⟨s, rfl, h1, h2⟩ | ⟨m, rfl⟩
  · cases s
    all_goals (try exact absurd rfl (h1 _))
    all_goals (try exact absurd rfl (h2 _))
    all_goals simp only [stateTime, prologue, collM, shflCnt, elCntM, Prologue.Site.shfls,
      Prologue.Site.elects, hw, nextKind, prologueKind, hf, clArriveT, clWaitT]
    all_goals simp [hf]
  · have hi : Mma.Inv L g m := hinv.1
    have hC : Mma.Counts L g m _ := hJ
    change (mmaKind m.site = .warp → mma _ _ m = _) ∧ (mmaKind m.site ≠ .warp → mma _ _ m < _)
    by_cases hs : Mma.ItemSite m.site
    · exact mma_item hpre hi hs
    have hpre0 := hC.pre
    have hdone := hC.done
    obtain ⟨site, i, t, b, pro⟩ := m
    simp only at hpre0 hdone hs ⊢
    by_cases hp0 : site.phase = 0
    · have hi0 := hpre0 hp0
      subst hi0
      rw [coll_phase0 hp0]
      cases site <;> simp only [Mma.ItemSite, not_true_eq_false, not_false_eq_true] at hs <;>
        (try simp [Mma.Site.phase] at hp0)
      all_goals simp [mma, mmaKind, hf, regT, allocT, allocWriteT, bar0T, ldBaseT, shflQT]
    have hp2 : site.phase = 2 := by
      cases site <;> simp only [Mma.ItemSite, not_true_eq_false, not_false_eq_true] at hs <;>
        simp_all [Mma.Site.phase]
    have hTi : (if (warpKey L g).1 % 2 = 0 then Tc L (warpKey L g).1 else 0) *
        tabM.len (Work.n L) ≤ (14 * Work.n L + 6) * i := by
      rw [tabM_len (n_pos hpre), Nat.mul_comm]
      split_ifs with hr
      · exact Nat.mul_le_mul_left _ (Nat.le_of_not_lt fun hlt =>
          absurd ((Work.mma_work_lt hpre).mpr hlt) (Nat.not_lt.mpr (hdone hp2 hr)))
      · simp
    rw [coll_tailM hp2]
    unfold mmaS
    rw [Sched.ItemTab.sched_tail (by omega), show Tc L (warpKey L g).1 = Work.T L g from rfl]
    cases site <;> simp only [Mma.ItemSite, not_true_eq_false, not_false_eq_true] at hs <;>
      (try simp [Mma.Site.phase] at hp2)
    all_goals simp only [mma, mmaKind, mmaTail, reduceCtorEq, ne_eq, not_false_eq_true,
      true_implies, IsEmpty.forall_iff, true_and]
    all_goals exact Progress.Time.tail_lt (by unfold tailM; omega)

/-- **The MMA warp's schedule of warp collectives.** -/
theorem mmaWarpSched : WarpRoleSched L X (· = 12) := by
  refine ⟨mmaS L, warpSched_of hpre hX hok (fun g d => collM L g d)
    (fun hg hG hk hσ => mma_count hpre hX ht hok hg hG hk hσ)
    (fun hg hG hk hσ => mma_time hpre hX ht hok hg hG hk hσ) ?_
    (fun c k => mmaS_gap hpre c k)⟩
  intro g d e hg hG h0 hσ he hp
  have hlen := Sched.len_pos_of_stop h0
  have hk : (X.tr g).length - 1 ≤ (X.tr g).length := Nat.sub_le _ 1
  have hnk : nextKind d ≠ .warp := by
    intro h
    have := (fired_kind hpre hX hok hg hσ he).1
    simp [h, hp] at this
  have hlt := (mma_time hpre hX ht hok hg hG hk hσ).2 hnk
  have he2 := mmaS_even (L := L) (warpKey L g) (collM L g d)
  rcases mma_state hpre hX ht hok hg hG hk hσ with ⟨s, rfl, -⟩ | ⟨m, rfl⟩
  · have he1 := even_time (L := L) (g := g) (.inl ⟨s⟩) (by simp) (by simp) (by simp) (by simp)
    omega
  · cases hm : m.site.isMma
    · have he1 := mma_even (n := Work.n L) (T := Work.T L g) hm
      change mma (Work.n L) (Work.T L g) m < _ at hlt
      show mma (Work.n L) (Work.T L g) m + 1 < _
      omega
    · exfalso
      have hs := mma_succ he hσ
      rw [Nat.sub_add_cancel hlen, h0] at hs
      obtain ⟨site, i, t, b, pro⟩ := m
      cases site <;> simp [Mma.Site.isMma] at hm
      simp [Mma.next] at hs

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
