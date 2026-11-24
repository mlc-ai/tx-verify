-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedLoaderWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarp

@[expose] public section

/-! # The loader warp's schedule of warp collectives

Warp 14's states are its prologue's, off warp 0's and warp 12's elections, and the loader's
(`loader_state`). Its warp collectives before a state are `collL` (`loader_count`): the
shuffles (`shflJ`), the elections (the prologue's `elects`, `Loader.Counts.elects`), and no
warp barrier or ballot (`loader_noWV`: the prologue's events are of its kinds, the loader's
warp-collective sites continue only on a shuffle or an election). Every state is at the
schedule `loadS` or before it (`loader_time`): the prologue's shuffles at the fixed times, the
item sites by the table (`loader_item`), the setup below the items, the drain, the tail's
election and the exit at the tail's offsets. With the even times and `loader_tight` this is the
role's `WarpRoleSched` (`loaderWarpSched`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem n_pos (hpre : Pre P L mem0) : 1 ≤ Work.n L := by
  have := skOf_eq hpre; have := hpre.skPos
  unfold Work.n Work.sk; omega

theorem loadS_fix (c : Nat × Nat) : loadS L c 0 = 0 ∧ loadS L c 1 = 2 ∧ loadS L c 2 = 4 ∧
    loadS L c 3 = prologue .shfl3 := by
  unfold loadS
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Sched.ItemTab.sched_fix (by decide)] <;> rfl

theorem loadS_base (c : Nat × Nat) (m : Nat) : base ≤ loadS L c (4 + m) :=
  Sched.ItemTab.base_le_sched slotClock (fix := fixL) (by simp [fixL])

/-- The count of a tail site: the items' collectives and the tail's `j` before it. -/
theorem loadS_tail {g : Nat} (j : Nat) :
    loadS L (warpKey L g) (4 + Work.T L g + Work.T L g * Loader.itemElects L g + j) =
      tailTime (Work.n L) (Work.T L g) (tailL (Loader.r0 L g) j) := by
  unfold loadS
  rw [show (warpKey L g).1 = ctaOf L g from rfl, r0c_eq,
    show Tc L (ctaOf L g) = Work.T L g from rfl]
  have hl := tabL_len L g (Work.n L) rfl
  have he : 4 + Work.T L g + Work.T L g * Loader.itemElects L g + j =
      fixL.length + ((tabL (Loader.r0 L g)).len (Work.n L) * Work.T L g + j) := by
    rw [hl]; simp only [fixL, List.length_cons, List.length_nil]; ring
  rw [he, Sched.ItemTab.sched_tail (by rw [Nat.mul_comm]; omega)]
  congr 2
  rw [Nat.mul_comm]; omega

/-- The tail's collectives before a tail site of the loader. -/
def tailJ (r0 : Nat) : Loader.Site → Nat
  | .arriveTail => 1
  | .exit => r0
  | _ => 0

theorem coll_tailL {g : Nat} {l : Loader.D} (h : l.site.inItem = false)
    (hs : l.site ≠ .setMaxReg) :
    collL L g (.inr (.loader l)) = 4 + Work.T L g + Work.T L g * Loader.itemElects L g +
      tailJ (Loader.r0 L g) l.site := by
  obtain ⟨s, i, t, a, b, c⟩ := l
  cases s <;> simp_all [collL, shflCnt, elCntL, Loader.shfls, Loader.electOf, tailJ,
    Loader.Site.inItem] <;> ring

/-- The loader's times are even but at the polls, the arrivals and the copies. -/
theorem loader_even {n T : Nat} {l : Loader.D}
    (h : ¬ ((∃ u, l.site = .wait u) ∨ (∃ u, l.site = .arrive u) ∨ ∃ u jj, l.site = .copy u jj)) :
    loader n T l % 2 = 0 := by
  obtain ⟨s, i, t, a, b, c⟩ := l
  cases s <;> simp only [loader, loaderUse, tailTime, bandL]
  all_goals first
    | decide
    | exact slot_even (by omega)
    | (exfalso; apply h; simp)

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- A state of warp 14: a prologue state off the elections, or a loader state. -/
theorem loader_state {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hw : warpOf L g = 14)
    (hk : k ≤ (X.tr g).length) (hσ : St L X g k = some (some d)) :
    (∃ s, d = .inl ⟨s⟩ ∧ (∀ e, s ≠ .elect e) ∧ (∀ j, s ≠ .init j) ∧ s ≠ .elect12 ∧
      s ≠ .init320) ∨ ∃ l, d = .inr (.loader l) := by
  obtain ⟨-, hinv, hw'⟩ := state_facts hpre hX ht hok hg hk hσ
  rcases role_cases hw' with ⟨⟨s⟩, rfl⟩ | ⟨h', -⟩ | ⟨-, l, rfl⟩ | ⟨h', -⟩ | ⟨h', -⟩ |
      ⟨h', -⟩ | ⟨h', h'', -⟩
  · have hi : Prologue.Inv L g ⟨s⟩ := hinv
    refine .inl ⟨s, rfl, fun e he => ?_, fun j hj => ?_, fun h => ?_, fun h => ?_⟩
    · have := hi.warp0 (.inl ⟨e, he⟩); omega
    · have := hi.warp0 (.inr ⟨j, hj⟩); omega
    · have := hi.warp12 (.inl h); omega
    · have := hi.warp12 (.inr h); omega
  all_goals (try omega)
  exact .inr ⟨l, rfl⟩

/-- **Warp 14 makes no warp barrier and no ballot** before a followed state. -/
theorem loader_noWV {g k j : Nat} {d d' : ThreadD} {e : Event} (hg : g < L.threads)
    (hw : warpOf L g = 14) (hjk : j < k) (hσ : St L X g k = some (some d))
    (hσj : St L X g j = some (some d')) (he : X.get (g, j) = some e) : isWV e = false := by
  have hjl : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases loader_state hpre hX ht hok hg hw hjl.le hσj with ⟨s, rfl, -⟩ | ⟨l, rfl⟩
  · have hE := pro_event hpre hX he hσj
      (fun f h => not_ub hpre hX ht hok hg hσj he e.pc f (by rw [← h]))
    exact prologue_isWV hE.proKind
  · by_contra hv
    have hv : isWV e = true := by simpa using hv
    have hkind := (fired_kind hpre hX hok hg hσj he).1
    rw [isWV_warp hv] at hkind
    obtain ⟨d'', hσ'⟩ := Frame.stateAt_live (C := code L) ht hg hσ (show j + 1 ≤ k by omega)
    have hs := loader_succ he hσj
    change St L X g (j + 1) = _ at hσ'
    rw [hs] at hσ'
    obtain ⟨site, i, t, a, b, c⟩ := l
    obtain ⟨pc, kk⟩ := e
    cases site <;> simp [nextKind, loaderKind] at hkind <;> cases kk <;> simp [isWV] at hv <;>
      simp [Loader.next] at hσ'

/-- **The warp collectives before a state of warp 14.** -/
theorem loader_count {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hw : warpOf L g = 14)
    (hk : k ≤ (X.tr g).length) (hσ : St L X g k = some (some d)) :
    ((X.tr g).take k).countP Sched.isWarpColl = collL L g d := by
  rw [warpColl_split]
  have hwv : ((X.tr g).take k).countP isWV = 0 := by
    rw [Sched.countP_take_congr (q := fun _ => false) ht hg hσ
      (fun hj hσj he => loader_noWV hpre hX ht hok hg hw hj hσ hσj he)]
    simp
  have hsh := (runInv_at hpre hX ht hok (shflJ_run hpre hg) hg hk hσ).2.1
  obtain ⟨hJ, -, -⟩ := state_facts hpre hX ht hok hg hk hσ
  rcases loader_state hpre hX ht hok hg hw hk hσ with ⟨s, rfl, -⟩ | ⟨l, rfl⟩
  · rw [hwv, hsh, elects_pro, hJ.2.1 (by omega)]; rfl
  · rw [hwv, hsh, (show Loader.Counts L g l _ from hJ).elects]; rfl

/-- **Every state of warp 14 against the schedule.** -/
theorem loader_time {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hw : warpOf L g = 14)
    (hk : k ≤ (X.tr g).length) (hσ : St L X g k = some (some d)) :
    (nextKind d = .warp → stateTime L g d = loadS L (warpKey L g) (collL L g d)) ∧
    (nextKind d ≠ .warp → stateTime L g d < loadS L (warpKey L g) (collL L g d)) := by
  obtain ⟨-, hinv, -⟩ := state_facts hpre hX ht hok hg hk hσ
  have hf := loadS_fix (L := L) (warpKey L g)
  simp only [prologue] at hf
  rcases loader_state hpre hX ht hok hg hw hk hσ with ⟨s, rfl, h1, h2, h3, h4⟩ | ⟨l, rfl⟩
  · have hb := loadS_base (L := L) (warpKey L g) 0
    cases s
    all_goals (try exact absurd rfl (h1 _))
    all_goals (try exact absurd rfl (h2 _))
    all_goals (try exact absurd rfl h3)
    all_goals (try exact absurd rfl h4)
    all_goals simp only [stateTime, prologue, collL, shflCnt, elCntL, Prologue.Site.shfls,
      Prologue.Site.elects, hw, nextKind, prologueKind, hf, clArriveT, clWaitT] at hb ⊢
    all_goals simp [base] at hb ⊢
    all_goals omega
  · have hi : Loader.Inv L g l := hinv
    by_cases hit : l.site.inItem = true
    · exact loader_item (n_pos hpre) hi hit
    have hl := hi.lead
    by_cases hs0 : l.site = .setMaxReg
    · obtain ⟨site, i, t, a, b, c⟩ := l
      simp only at hs0
      subst hs0
      have := loadS_base (L := L) (warpKey L g) 0
      refine ⟨fun h => absurd h (by simp [nextKind, loaderKind]), fun _ => ?_⟩
      simp only [stateTime, loader, collL, shflCnt, elCntL, Loader.shfls,
        Loader.electOf, Nat.add_zero, base, regT] at this ⊢
      omega
    simp only [stateTime, nextKind]
    rw [coll_tailL (by simpa using hit) hs0, loadS_tail]
    obtain ⟨site, i, t, a, b, c⟩ := l
    simp only at hl hs0 ⊢
    cases site <;> simp only [Loader.Site.inItem, not_true_eq_false] at hit
    all_goals (try exact absurd rfl hs0)
    all_goals simp only [Loader.Site.leadOnly, true_implies] at hl
    all_goals simp only [loaderKind, loader, tailJ, tailL, Loader.r0, hl, ne_eq, reduceCtorEq,
      not_false_eq_true, true_implies, IsEmpty.forall_iff, and_true, true_and, and_self,
      ↓reduceIte, not_true_eq_false]
    all_goals (try (split_ifs <;> exact Progress.Time.tail_lt (by omega)))
    all_goals (apply Progress.Time.tail_lt; by_cases hr : Work.rank L g = 0 <;> simp [hr])

/-- **The loader warp's schedule of warp collectives.** -/
theorem loaderWarpSched : WarpRoleSched L X (· = 14) := by
  refine ⟨loadS L, warpSched_of hpre hX hok (fun g d => collL L g d)
    (fun hg hG hk hσ => loader_count hpre hX ht hok hg hG hk hσ)
    (fun hg hG hk hσ => loader_time hpre hX ht hok hg hG hk hσ) ?_
    (fun c k => loadS_gap hpre c k)⟩
  intro g d e hg hG h0 hσ he hp
  have hlen := Sched.len_pos_of_stop h0
  have hk : (X.tr g).length - 1 ≤ (X.tr g).length := Nat.sub_le _ 1
  have hnk : nextKind d ≠ .warp := by
    intro h
    have := (fired_kind hpre hX hok hg hσ he).1
    simp [h, hp] at this
  have hlt := (loader_time hpre hX ht hok hg hG hk hσ).2 hnk
  have he2 := loadS_even (L := L) (warpKey L g) (collL L g d)
  rcases loader_state hpre hX ht hok hg hG hk hσ with ⟨s, rfl, -⟩ | ⟨l, rfl⟩
  · have he1 := even_time (L := L) (g := g) (.inl ⟨s⟩) (by simp) (by simp) (by simp) (by simp)
    omega
  · by_cases hodd : (∃ u, l.site = .wait u) ∨ (∃ u, l.site = .arrive u) ∨
        ∃ u jj, l.site = .copy u jj
    · have := loader_tight hpre hX hok hg he hσ hodd
      rw [Nat.sub_add_cancel hlen] at this
      exact absurd h0 this
    · have he1 := loader_even (n := Work.n L) (T := Work.T L g) hodd
      change loader (Work.n L) (Work.T L g) l < _ at hlt
      show loader (Work.n L) (Work.T L g) l + 1 < _
      omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
