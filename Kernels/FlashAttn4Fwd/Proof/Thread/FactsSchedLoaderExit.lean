-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedLoaderSched

@[expose] public section

/-! # The loader warp's counts at the exit (`Cross.WarpExitAgree`, `Cross.WarpExitAbove`)

Both premises follow from a schedule of the warp collectives of a group of warps (`WarpSchedG`)
and two facts of the group's times (`warpExit_of_sched`):

* every lane exits at one time (`heq`);
* every state at a warp collective is earlier than the exit of every lane of its warp (`hlt`).

Two lanes exiting with counts `c < c'`: the second made its `c`-th collective at a state of time
`S c`, earlier than its exit, which is the first lane's exit, earlier than `S c` (the first's
next collective). A lane at a warp collective with count `c` no below an exiting lane's `c'`:
its time `S c ≥ S c'` is after the exit, but it is earlier.

For warp 14 the exit is at `tailTime … 18`, after the prologue, the items' slots and the tail's
election at `+14` (`loaderWarpExitAgree`, `loaderWarpExitAbove`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The event at which a count passes `c`. -/
theorem exists_nth {α : Type} {p : α → Bool} : ∀ {l : List α} {c : Nat}, c < l.countP p →
    ∃ j, ∃ h : j < l.length, (l.take j).countP p = c ∧ p l[j] = true
  | [], c, h => by simp at h
  | a :: l, c, h => by
    by_cases ha : p a = true
    · rcases c with _ | c
      · exact ⟨0, by simp, by simp, by simpa using ha⟩
      · rw [List.countP_cons_of_pos ha] at h
        obtain ⟨j, hj, h1, h2⟩ := exists_nth (p := p) (l := l) (c := c) (by omega)
        exact ⟨j + 1, by simp; omega, by simp [List.countP_cons_of_pos ha, h1], by simpa using h2⟩
    · rw [List.countP_cons_of_neg ha] at h
      obtain ⟨j, hj, h1, h2⟩ := exists_nth (p := p) (l := l) (c := c) h
      exact ⟨j + 1, by simp; omega, by simp [List.countP_cons_of_neg ha, h1], by simpa using h2⟩

theorem sameWarp_symm {g h : Nat} (hs : SameWarp L g h) : SameWarp L h g := by
  obtain ⟨⟨hg, hh, hc⟩, hw⟩ := hs
  exact ⟨⟨hh, hg, hc.symm⟩, hw.symm⟩

theorem sameWarp_warp {g h : Nat} (hs : SameWarp L g h) : warpOf L h = warpOf L g :=
  (congrArg Prod.snd (warpKey_eq hs)).symm

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)

/-- The exit times of a group of warps: one per warp, after every warp collective. -/
structure ExitTimes (L : Launch) (X : Execution) (Grp : Nat → Prop) : Prop where
  grp : ∀ {g h : Nat}, SameWarp L g h → Grp g → Grp h
  lt : ∀ {g h k k' : Nat} {d d' : ThreadD}, SameWarp L g h → Grp g → k ≤ (X.tr g).length →
    St L X g k = some (some d) → nextKind d = .warp → k' ≤ (X.tr h).length →
    St L X h k' = some (some d') → (code L h).pc d' = Flow.exit_0 →
    stateTime L g d < stateTime L h d'
  eq : ∀ {g h k k' : Nat} {d d' : ThreadD}, SameWarp L g h → Grp g → k ≤ (X.tr g).length →
    St L X g k = some (some d) → (code L g).pc d = Flow.exit_0 → k' ≤ (X.tr h).length →
    St L X h k' = some (some d') → (code L h).pc d' = Flow.exit_0 →
    stateTime L g d = stateTime L h d'

include hpre hX ht hok in
theorem exit_lt {Grp : Nat → Prop} {S : Nat × Nat → Nat → Nat} (hs : WarpSchedG L X Grp S)
    (hE : ExitTimes L X Grp) {g h k k' pc pc' : Nat} {d d' : ThreadD} (hG : Grp g)
    (hsw : SameWarp L g h) (hσ : St L X g k = some (some d)) (hσ' : St L X h k' = some (some d'))
    (he : X.get (g, k) = some ⟨pc, .exit⟩) (he' : X.get (h, k') = some ⟨pc', .exit⟩) :
    ¬ ((X.tr g).take k).countP Sched.isWarpColl < ((X.tr h).take k').countP Sched.isWarpColl := by
  intro hc
  have hg := hsw.1.1
  have hh := hsw.1.2.1
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hk' : k' < (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1
  obtain ⟨j, hj, h1, h2⟩ := exists_nth hc
  rw [List.length_take] at hj
  have hjk : j < k' := by omega
  rw [List.take_take, Nat.min_eq_left hjk.le] at h1
  rw [List.getElem_take] at h2
  obtain ⟨dj, hσj⟩ := Frame.stateAt_live (C := code L) ht hh hσ' hjk.le
  have hej : X.get (h, j) = some (X.tr h)[j] :=
    List.getElem?_eq_getElem (show j < (X.tr h).length by omega)
  have hG' := hE.grp hsw hG
  have hat : stateTime L _ _ = _ := hs.sched.atEv hh hG' hσj hej h2
  have hkind := (fired_kind hpre hX hok hh hσj hej).1
  rw [h2] at hkind
  have hlt := hE.lt ⟨⟨hh, hh, rfl⟩, rfl⟩ hG'
    (hjk.le.trans hk'.le) hσj (beq_iff_eq.mp hkind.symm) hk'.le hσ' (Lag.exit_pc hpre hX he' hσ')
  have hnon : stateTime L _ _ < _ := hs.sched.nonEv hg hG hσ he rfl
  have heq := hE.eq hsw hG hk.le hσ (Lag.exit_pc hpre hX he hσ) hk'.le hσ'
    (Lag.exit_pc hpre hX he' hσ')
  rw [h1, ← warpKey_eq hsw] at hat
  omega

include hpre hX ht hok in
/-- **Lanes of a group exit with one count of warp collectives.** -/
theorem exitAgree_of {Grp : Nat → Prop} {S : Nat × Nat → Nat → Nat}
    (hs : WarpSchedG L X Grp S) (hE : ExitTimes L X Grp) :
    ∀ {g h k k' pc pc' : Nat} {d d' : ThreadD}, Grp g → SameWarp L g h →
      St L X g k = some (some d) → St L X h k' = some (some d') →
      X.get (g, k) = some ⟨pc, .exit⟩ → X.get (h, k') = some ⟨pc', .exit⟩ →
      ((X.tr g).take k).countP Sched.isWarpColl = ((X.tr h).take k').countP Sched.isWarpColl := by
  intro g h k k' pc pc' d d' hG hsw hσ hσ' he he'
  have h1 := exit_lt hpre hX ht hok hs hE hG hsw hσ hσ' he he'
  have h2 := exit_lt hpre hX ht hok hs hE (hE.grp hsw hG) (sameWarp_symm hsw) hσ' hσ he' he
  omega

include hpre hX in
/-- **A lane of a group at a warp collective has made fewer than an exiting lane of its warp.** -/
theorem exitAbove_of {Grp : Nat → Prop} {S : Nat × Nat → Nat → Nat}
    (hs : WarpSchedG L X Grp S) (hE : ExitTimes L X Grp) :
    ∀ {g h k pc : Nat} {d d' : ThreadD}, Grp g → SameWarp L g h →
      St L X g (X.tr g).length = some (some d) → nextKind d = .warp →
      St L X h k = some (some d') → X.get (h, k) = some ⟨pc, .exit⟩ →
      (X.tr g).countP Sched.isWarpColl < ((X.tr h).take k).countP Sched.isWarpColl := by
  intro g h k pc d d' hG hsw hσ hk hσ' he'
  have hg := hsw.1.1
  have hh := hsw.1.2.1
  have hk' : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp he').1
  by_contra hc
  have hat := hs.endAt hg hG hσ hk
  have hnon : stateTime L _ _ < _ := hs.sched.nonEv hh (hE.grp hsw hG) hσ' he' rfl
  have hle := Sched.sched_le hs.sched.mono (warpKey L g)
    (show ((X.tr h).take k).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl by omega)
  have hlt := hE.lt hsw hG le_rfl hσ hk hk'.le hσ' (Lag.exit_pc hpre hX he' hσ')
  rw [← warpKey_eq hsw] at hnon
  omega

/-! ### Warp 14 -/

theorem T_same {g h : Nat} (hsw : SameWarp L g h) : Work.T L h = Work.T L g := by
  have := congrArg Prod.fst (warpKey_eq hsw)
  simp only [warpKey] at this
  rw [show Work.T L g = Tc L (ctaOf L g) from rfl, show Work.T L h = Tc L (ctaOf L h) from rfl,
    this]

theorem rslot_leL {g : Nat} {l : Loader.D} (hi : Loader.Inv L g l)
    (hit : l.site.inItem = true) :
    Sched.ItemTab.rslot (Work.n L) l.t (regionL l.site) ≤ Work.n L := by
  have htr := hi.trip
  obtain ⟨s, i, t, a, b, c⟩ := l
  simp only at htr ⊢
  cases s <;> simp only [Loader.Site.inItem, Bool.false_eq_true] at hit
  all_goals (try (rename_i u _; cases u))
  all_goals (try (rename_i u; cases u))
  all_goals simp [regionL, Loader.UseK.trip, Sched.ItemTab.rslot, Loader.Site.inTrip] at htr ⊢
  all_goals omega

include hpre hX ht hok in
/-- The exit of a lane of warp 14: the loader's exit site. -/
theorem loader_exit_site {h k : Nat} {d : ThreadD} (hh : h < L.threads) (hw : warpOf L h = 14)
    (hk : k ≤ (X.tr h).length) (hσ : St L X h k = some (some d))
    (hpc : (code L h).pc d = Flow.exit_0) :
    stateTime L h d = tailTime (Work.n L) (Work.T L h) 18 := by
  rcases loader_state hpre hX ht hok hh hw hk hσ with ⟨s, rfl, -⟩ | ⟨l, rfl⟩
  · exact absurd hpc (Prologue.site_ne_exit s)
  · have hs := Loader.site_exit l.site hpc
    obtain ⟨site, i, t, a, b, c⟩ := l
    simp only at hs
    subst hs
    rfl

include hpre hX ht hok in
theorem loaderExitTimes : ExitTimes L X (fun g => warpOf L g = 14) where
  grp hsw hG := (sameWarp_warp hsw).trans hG
  lt := by
    intro g h k k' d d' hsw hG hk hσ hkd hk' hσ' hpc
    have hh := hsw.1.2.1
    rw [loader_exit_site hpre hX ht hok hh ((sameWarp_warp hsw).trans hG) hk' hσ' hpc,
      T_same hsw]
    obtain ⟨-, hinv, -⟩ := state_facts hpre hX ht hok hsw.1.1 hk hσ
    rcases loader_state hpre hX ht hok hsw.1.1 hG hk hσ with ⟨s, rfl, -⟩ | ⟨l, rfl⟩
    · exact ((Progress.Time.prologue_lt_reg s).trans (by decide)).trans_le Progress.Time.base_le
    · have hi : Loader.Inv L g l := hinv
      change loader _ _ l < _
      by_cases hit : l.site.inItem = true
      · rw [time_itemL hit]
        exact Progress.Time.lt_tail (rslot_leL hi hit) (hi.item hit) ((offL_lt _).trans (by decide))
      · obtain ⟨site, i, t, a, b, c⟩ := l
        cases site <;> simp only [Loader.Site.inItem, not_true_eq_false] at hit <;>
          simp only [nextKind, loaderKind, reduceCtorEq] at hkd
        exact Progress.Time.tail_lt (by decide)
  eq := by
    intro g h k k' d d' hsw hG hk hσ hpc hk' hσ' hpc'
    rw [loader_exit_site hpre hX ht hok hsw.1.1 hG hk hσ hpc,
      loader_exit_site hpre hX ht hok hsw.1.2.1 ((sameWarp_warp hsw).trans hG) hk' hσ' hpc',
      T_same hsw]

include hpre hX ht hok in
/-- **`Cross.WarpExitAgree` for the lanes of warp 14.** -/
theorem loaderWarpExitAgree : ∀ {g h k k' pc pc' : Nat} {d d' : ThreadD}, warpOf L g = 14 →
    SameWarp L g h → St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .exit⟩ → X.get (h, k') = some ⟨pc', .exit⟩ →
    ((X.tr g).take k).countP Sched.isWarpColl = ((X.tr h).take k').countP Sched.isWarpColl := by
  obtain ⟨S, hs⟩ := loaderWarpSched hpre hX ht hok
  exact exitAgree_of hpre hX ht hok hs (loaderExitTimes hpre hX ht hok)

include hpre hX ht hok in
/-- **`Cross.WarpExitAbove` for the lanes of warp 14.** -/
theorem loaderWarpExitAbove : ∀ {g h k pc : Nat} {d d' : ThreadD}, warpOf L g = 14 →
    SameWarp L g h → St L X g (X.tr g).length = some (some d) → nextKind d = .warp →
    St L X h k = some (some d') → X.get (h, k) = some ⟨pc, .exit⟩ →
    (X.tr g).countP Sched.isWarpColl < ((X.tr h).take k).countP Sched.isWarpColl := by
  obtain ⟨S, hs⟩ := loaderWarpSched hpre hX ht hok
  exact exitAbove_of hpre hX hs (loaderExitTimes hpre hX ht hok)

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
