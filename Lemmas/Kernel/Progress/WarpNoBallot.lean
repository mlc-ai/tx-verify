-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WarpCollRelU

@[expose] public section

/-! # Progress at the warp collectives of a kernel with mode votes

`Sched.no_aheadU` and `Sched.warpColl_steps_relU` assume a code without mode votes
(`vote.sync` with `.all`, `.any`, `.uni`): a ballot's ordinal counts the full-mask mode votes too,
which `isWarpColl` does not count. The assumption is used only at a ballot. A kernel that never
ballots (`hnb`: no `vote` event in the execution) needs no assumption on its mode votes: the mode
votes are not warp collectives of the count, and the shuffles, elections and warp barriers are
ordered by their own ordinals (DEP-WARP-SHUFFLE, DEP-WARP-ELECT, DEP-WARP-BARRIER).

* `no_aheadNB`: no lane of a warp is past a lane that has not exited, without ballots.
* `warpColl_steps_relNB`: progress at a warp collective, without ballots. -/

namespace PTX.Sched

open PTX Classical

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Flow.Code K A L g} {κ : Type} {key : Nat → κ}

/-- **No lane is past a lane that has not exited**, in an execution without ballots. -/
theorem no_aheadNB
    (hnb : ∀ {i : EvId} {pc m : Nat} {a : Bool} {b : BitVec 32}, X.get i ≠ some ⟨pc, .vote m a b⟩)
    (hk : ∀ {g h : Nat}, SameWarp L g h → key g = key h) (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (C g).SoundU) (htr : Frame.Tracked C X)
    (hub : ¬ HasUb X) (hw : WarpRec C X key) {g h : Nat} (hg : g < L.threads)
    (hs : SameWarp L g h) {t : TState} (hr : Run K A L g {} (X.tr g) (some t))
    (hlt : (X.tr g).countP isWarpColl < (X.tr h).countP isWarpColl) : False := by
  obtain ⟨F, hfull, hrec⟩ := id hw
  have hh : h < L.threads := hs.1.2.1
  have hsh : SameWarp L h g := sameWarp_symm hs
  have hkey : key h = key g := (hk hs).symm
  have hrg := shape_recU hX hsound htr hub hrec hg
  have hrh := shape_recU hX hsound htr hub hrec hh
  obtain ⟨j, e, hj, hc, hjn⟩ := MbarRing.Slot.exists_nth_countP isWarpColl
    (xs := X.tr h) (c := (X.tr g).countP isWarpColl) hlt
  have hjl : j ≤ (X.tr h).length := (List.getElem?_eq_some_iff.mp hj).1.le
  -- the events of a kind before `h`'s `n`-th warp collective are as many as in `g`'s trace
  have cnt : ∀ (q : Event → Bool) (i : Nat), (∀ e, q e = true → isWarpColl e = true) →
      (∀ e s, kindShape e.kind = some s → q e = (s.tag == i)) →
      ((X.tr h).take j).countP q = (X.tr g).countP q := by
    intro q i hq hqr
    rw [count_shape F (key h) hrh q (fun s => s.tag == i) hq hqr j hjl,
      ← List.take_length (l := X.tr g),
      count_shape F (key g) hrg q (fun s => s.tag == i) hq hqr _ le_rfl, hjn, hkey,
      List.take_length]
  have hnx : ∀ k pc, X.get (g, k) ≠ some ⟨pc, .exit⟩ := fun k pc hk => hr.no_exit hk
  have hlg : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨pc, k⟩ := e
  cases k <;> simp only [isWarpColl, Bool.false_eq_true] at hc
  case shfl m a b c recv ok =>
    have hc' := cnt Execution.isShfl 0 shfl_coll shfl_tag
    rcases Step.shfl_lane_of_ready hX hj ⟨⟨_, _, _, _, _, _, _, hj⟩, rfl⟩ hsh with
      ⟨j', hk'⟩ | ⟨k, pce, hex, -⟩
    · have := Step.ShflK.lt_count hk'
      simp only at this
      omega
    · exact hnx k pce hex
  case elect mask inst leader =>
    have hc' := cnt isElectEv 1 elect_coll elect_tag
    have hef : ∀ {e : EvId} {pc mask inst l : Nat}, X.Elect e pc mask inst l →
        mask = 4294967295 := fun {e} _ _ _ _ he' =>
      rec_maskU hX hsound htr hub hw (x := e.1) (k := e.2) he' rfl rfl
    have hel : X.Elect (h, j) pc mask inst leader := hj
    have hmem : ∀ {x y} z pc' m i l, X.Elect (x, z) pc' m i l → electMember m (laneOf L y) :=
      fun z _ _ _ _ he' => by
        rw [hef he']; exact full_member (Nat.mod_lt _ (by decide))
    obtain ⟨x, hp⟩ := ElectOrd.partner hX hsh hel (hmem j _ _ _ _ hel)
    have heq := ElectOrd.ordinal_eq hX hsh (fun z => hmem z) (fun z => hmem z) hp
    obtain ⟨_, _, _, _, _, _, _, -, hx⟩ := hp
    obtain ⟨hxl, hxe⟩ := List.getElem?_eq_some_iff.mp (show (X.tr g)[x]? = _ from hx)
    have := PTX.countP_take_lt (p := isElectEv) (l := X.tr g) hxl (by rw [hxe]; rfl)
    simp only [elections] at heq
    omega
  case warpBar mask inst =>
    have hc' := cnt Execution.isWarpBar 2 warpBar_coll warpBar_tag
    have hmask : ∀ {x} (hx : x < L.threads) {y m i}, X.WarpBar (x, y) m i → m = 4294967295 := by
      intro x hx y m i ⟨p, hp⟩
      exact rec_full hfull (shape_recU hX hsound htr hub hrec hx y _ hp rfl) rfl
    have hwb : X.WarpBar (h, j) mask inst := ⟨pc, hj⟩
    obtain ⟨x, hp⟩ := WarpBar.partner hX hsh hwb (by rw [hmask hh hwb]; exact full_member hlg)
    have heq := WarpBar.ordinal_eq hX hsh
      (fun y m i hy => by rw [hmask hh hy]; exact full_member hlg)
      (fun y m i hy => by rw [hmask hg hy]; exact full_member (Nat.mod_lt _ (by decide))) hp
    obtain ⟨_, _, -, p', hp'⟩ := hp
    obtain ⟨hxl, hxe⟩ := List.getElem?_eq_some_iff.mp (show (X.tr g)[x]? = _ from hp')
    have := PTX.countP_take_lt (p := Execution.isWarpBar) (l := X.tr g) hxl (by rw [hxe]; rfl)
    simp only [warpBars] at heq
    omega
  case vote mask a ballot => exact hnb (i := (h, j)) hj

variable {M : Timed K A L} {AtColl : ∀ g, (M.code g).D → Prop}

/-- **Progress at a warp collective**, in an execution without ballots: `warpColl_steps_relU`
with `no_aheadNB` for the order of the lanes. -/
theorem warpColl_steps_relNB
    (hnb : ∀ {i : EvId} {pc m : Nat} {a : Bool} {b : BitVec 32}, X.get i ≠ some ⟨pc, .vote m a b⟩)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h)
    (hsound : ∀ g < L.threads, (M.code g).SoundU) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X) (hw : WarpCollRel mem0 M X key AtColl)
    (hb : L.block % 32 = 0) (hlaunch : ∀ h, Step.Launched L X h)
    (hcl : ∀ h, ¬ ClcCanceled L X h)
    (happ : ∀ (ds : List Nat) (ev : Nat → Event), (∀ x, (ev x).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev))
    (hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run K A L h {} (X.tr h) (some t) → Relation.ReflTransGen (Tau K A L h) t t1 →
      out K A L h t1 = .ev (.ub f) → ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtColl g d)
    (hrel : Step.Released L X g) : Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hub := safe_noUb (hs.2 X hX)
  have hwrec : WarpRec M.code X key := by
    obtain ⟨F, hfull, hrec, -⟩ := hw.shape
    exact ⟨fun c n => (F c n).2, hfull, hrec⟩
  obtain ⟨tg, hrg⟩ := Frame.run_some hX hub hp
  have hle : ∀ h, SameWarp L g h → (X.tr h).countP isWarpColl ≤ (X.tr g).countP isWarpColl :=
    fun h hsw => Nat.le_of_not_lt fun hlt =>
      no_aheadNB hnb hkey hX hsound htr hub hwrec hg hsw hrg hlt
  obtain ⟨F, hfullF, -, hshape⟩ := hw.shape
  by_cases hall : ∀ h, SameWarp L g h →
      (X.tr h).countP isWarpColl = (X.tr g).countP isWarpColl ∧
      ∃ dh, Frame.stateAt M.code X h (X.tr h).length = some (some dh) ∧ AtColl h dh
  · -- every lane at the collective
    by_cases hext : ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L
    · exact .inl hext
    have hrels : ∀ h, SameWarp L g h → Step.Released L X h := fun h hsw => by
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      exact (hw.released hg hsw hσ hk hσh hkh hn hrel).resolve_right hext
    have hfire : ∀ h, SameWarp L g h → ∃ t t1 m, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev m ∧
        ((∃ f, m = .ub f) ∨ (t1.pc = (F (key g) ((X.tr g).countP isWarpColl)).1 ∧
          tmplShape m = some (F (key g) ((X.tr g).countP isWarpColl)).2)) := by
      intro h hsw
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      have hh := hsw.1.2.1
      obtain ⟨t, hr⟩ := Frame.run_some hX hub
        (hw.lane_noExitU hkey hX hsound htr hub hcl hg hsw hσ hk (hle h hsw))
      rcases Frame.end_atU hsound hh hr hσh with hsite | ⟨u,f,hτ,ho⟩
      case inr => exact ⟨t,u,_,hr,hτ,ho,.inl ⟨f,rfl⟩⟩
      obtain ⟨t1, ins, hτ, hat, hinv, -, hout⟩ := hsite
      have hsh := hshape hh hσh hkh hat hinv hout
      rw [hn, ← hkey hsw] at hsh
      exact ⟨t, t1, _, hr, hτ, hout, hsh⟩
    by_cases hubl : ∃ h, SameWarp L g h ∧ ∃ t t1 f, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev (.ub f)
    · obtain ⟨h, hsw, t, t1, f, hr, hτ, hout⟩ := hubl
      exact .inl (hubx hsw.1.2.1 (hrels h hsw) hr hτ hout)
    · push Not at hubl
      refine .inl (coll_batch hX hb hg (pc := (F (key g) ((X.tr g).countP isWarpColl)).1)
        (hfullF (key g) ((X.tr g).countP isWarpColl)) (fun h hsw => ?_)
        (fun h _ => .inr (hlaunch h)) happ hrels)
      obtain ⟨t, t1, m, hr, hτ, hout, hm⟩ := hfire h hsw
      rcases hm with ⟨f, rfl⟩ | ⟨hpc, hsh⟩
      · exact (hubl h hsw t t1 f hr hτ hout).elim
      · exact ⟨t, t1, m, hr, hτ, hout, hpc, hsh⟩
  · -- a lane not at the collective is earlier
    push Not at hall
    obtain ⟨h, hsw, hnot⟩ := hall
    have hph := hw.lane_noExitU hkey hX hsound htr hub hcl hg hsw hσ hk (hle h hsw)
    by_cases hnone : Frame.stateAt M.code X h (X.tr h).length = none
    · obtain ⟨t, hr⟩ := Frame.run_some hX hub hph
      obtain ⟨t1, f, hτ, hout⟩ := Frame.end_deadU hsound hph.1 hr hnone
      exact .inl (hubx hph.1 (hw.dead hph hnone) hr hτ hout)
    have hlag := hw.lag hg hsw.1.2.1 hsw hσ hk (hle h hsw) (fun ⟨hn, dh, hσh, hkh⟩ =>
      hnot hn dh hσh hkh) hnone
    have htime : threadTime M X h < threadTime M X g := by
      rw [threadTime_of hσ]
      exact hlag
    refine .inr ⟨X, .thread h, hmax, hph, ?_⟩
    rw [rank_released hrel]
    exact rank_lt_of_time_lt htime

end
end PTX.Sched
