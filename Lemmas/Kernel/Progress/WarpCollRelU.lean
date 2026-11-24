-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WarpCollRel
public import Lemmas.Kernel.Progress.WarpU

@[expose] public section
namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {κ : Type}

variable {key : Nat → κ} {AtColl : ∀ g, (M.code g).D → Prop}

/-- **A lane of the warp of a lane at a warp collective has not exited** when it has made at most
as many warp collectives. -/
theorem WarpCollRel.lane_noExitU (hw : WarpCollRel mem0 M X key AtColl)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h) (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (M.code g).SoundU) (htr : Frame.Tracked M.code X)
    (hub : ¬ HasUb X) (hcl : ∀ h, ¬ ClcCanceled L X h) {g h : Nat} {d : (M.code g).D}
    (hg : g < L.threads) (hs : SameWarp L g h)
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtColl g d)
    (hle : (X.tr h).countP isWarpColl ≤ (X.tr g).countP isWarpColl) :
    Frame.Pending L X h := by
  obtain ⟨T, hT1, hT2⟩ := hw.exit
  refine ⟨hs.1.2.1, hcl h, fun pc hl => ?_⟩
  have hex := exit_get hl
  obtain ⟨dx, hdx⟩ := Frame.state_of_noUbU hsound hX htr hub hex
  have h1 := hT1 hg hσ hk
  have h2 := hT2 hs.1.2.1 hdx hex
  have h3 := Flow.countP_take_mono isWarpColl (X.tr h) (Nat.sub_le (X.tr h).length 1)
  rw [List.take_length] at h3
  rw [← hkey hs] at h2
  omega

/-- **Progress at a warp collective.** A released pending thread whose state at its trace's end
is at a warp collective steps. -/
theorem warpColl_steps_relU (hK : K.code.all (fun ins => !voteModeOp ins.op) = true)
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
      no_aheadU hK hkey hX hsound htr hub hwrec hg hsw hrg hlt
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
