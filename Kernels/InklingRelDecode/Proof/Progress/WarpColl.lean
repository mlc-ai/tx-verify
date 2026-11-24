-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WarpLanes

@[expose] public section

/-! # Progress at a warp collective

A released pending thread `g` at its `n`-th warp collective (`nextKind = .warp`) steps
(`warp_next_steps`):

* no lane of its warp has made more than `n` warp collectives (`Sched.no_ahead`);
* a lane that has made at most `n` and is not at its `n`-th is earlier (`WarpCollFacts.lag`); it
  has not exited (it would have made more, `WarpCollFacts.exit`), so it is a pending obligation
  of smaller rank;
* otherwise every lane is at its `n`-th warp collective, and every lane is released
  (`lane_released`). A lane whose machine reaches undefined behaviour performs it; else all lanes
  fire templates of one static part at one source position (`WarpCollFacts.shape`) and the warp
  performs one instance (`Sched.coll_batch`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress

open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface Classical

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}


theorem kernel_noVoteMode : kernel.code.all (fun ins => !Sched.voteModeOp ins.op) = true := by
  decide +kernel

/-- The recorded static parts of the warp collectives (`WarpCollFacts.shape`). -/
theorem warpRec (hw : WarpCollFacts T Q L X) : Sched.WarpRec (code L Q) X (warpKey L) := by
  obtain ⟨F, hfull, hrec, -⟩ := hw.shape
  exact ⟨fun c n => (F c n).2, hfull, hrec⟩

/-- A lane of the warp of a lane at a warp collective has not exited when it has made at most
as many warp collectives. -/
theorem lane_noExit (hX : Consistent L kernel asms mem0 X)
    (hsound : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hub : ¬ HasUb X) (hw : WarpCollFacts T Q L X) {g h : Nat} {d : TSt} (hg : g < L.threads)
    (hs : SameWarp L g h) (hσ : St Q L X g (X.tr g).length = some (some d))
    (hk : nextKind d = .warp)
    (hle : (X.tr h).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl) :
    Frame.Pending L X h := by
  obtain ⟨N, hT1, hT2⟩ := hw.exit
  refine ⟨hs.1.2.1, no_canceled hX _ hs.1.2.1, fun pc hl => ?_⟩
  have hex := Sched.exit_get hl
  obtain ⟨dx, hdx⟩ := Frame.state_of_noUb hsound hX htr hub hex
  have h1 := hT1 hg hσ hk
  have h2 := hT2 hs.1.2.1 hdx hex
  have h3 := Flow.countP_take_mono Sched.isWarpColl (X.tr h) (Nat.sub_le (X.tr h).length 1)
  rw [List.take_length] at h3
  rw [← warpKey_eq hs] at h2
  omega

/-- **Progress at a warp collective.** -/
theorem warp_next_steps (hpre : Pre Q L mem0) (hs : SafeGoal kernel asms L mem0)
    (hsound : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hw : WarpCollFacts T Q L X)
    (hmax : Maximal L kernel asms mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some d)) (hk : nextKind d = .warp)
    (hrel : Step.Released L X g) (hpub : AllocStored L X g) :
    Sched.Steps (timed T Q L) mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hub := Sched.safe_noUb (hs.2 X hX)
  obtain ⟨tg, hrg⟩ := Frame.run_some hX hub hp
  have hle : ∀ h, SameWarp L g h →
      (X.tr h).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl :=
    fun h hsw => Nat.le_of_not_lt fun hlt =>
      Sched.no_ahead kernel_noVoteMode warpKey_eq hX hsound htr hub (warpRec hw) hg hsw hrg hlt
  by_cases hall : ∀ h, SameWarp L g h →
      (X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl ∧
      ∃ dh, St Q L X h (X.tr h).length = some (some dh) ∧ nextKind dh = .warp
  · -- every lane at the collective
    have hrels : ∀ h, SameWarp L g h → Step.Released L X h := fun h hsw => by
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      exact lane_released hX hw hpub hg hsw hσ hk hσh hkh hn hrel
    have hfire : ∀ h, SameWarp L g h → ∃ t t1 m, Run kernel asms L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau kernel asms L h) t t1 ∧ out kernel asms L h t1 = .ev m ∧
        ((∃ f, m = .ub f) ∨
          (t1.pc = (Classical.choose hw.shape (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).1 ∧
          Sched.tmplShape m =
            some (Classical.choose hw.shape (warpKey L g)
              ((X.tr g).countP Sched.isWarpColl)).2)) := by
      intro h hsw
      obtain ⟨hn, dh, hσh, hkh⟩ := hall h hsw
      have hh := hsw.1.2.1
      obtain ⟨t, hr⟩ := Frame.run_some hX hub (lane_noExit hX hsound htr hub hw hg hsw hσ hk
        (hle h hsw))
      obtain ⟨t1, m, hτ, hat, hout, -⟩ := fire hsound hh hσh hr
      have hsh := (Classical.choose_spec hw.shape).2.2 hh hσh hkh hat hout
      rw [hn, ← warpKey_eq hsw] at hsh
      exact ⟨t, t1, m, hr, hτ, hout, hsh⟩
    by_cases hubl : ∃ h, SameWarp L g h ∧ ∃ t t1 f, Run kernel asms L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau kernel asms L h) t t1 ∧ out kernel asms L h t1 = .ev (.ub f)
    · obtain ⟨h, hsw, t, t1, f, hr, hτ, hout⟩ := hubl
      exact .inl (ub_ext hX hsw.1.2.1 (hrels h hsw) hr hτ hout)
    · push Not at hubl
      refine .inl (Sched.coll_batch hX (by rw [hpre.block]) hg
        (pc := (Classical.choose hw.shape (warpKey L g) ((X.tr g).countP Sched.isWarpColl)).1)
        ((Classical.choose_spec hw.shape).1 (warpKey L g) ((X.tr g).countP Sched.isWarpColl))
        (fun h hsw => ?_) (fun h _ => .inr (launched hX h))
        (fun _ _ h => asms_wfStep.quiet hX le_appendLanes rfl (noNewRead_appendLanes h)) hrels)
      obtain ⟨t, t1, m, hr, hτ, hout, hm⟩ := hfire h hsw
      rcases hm with ⟨f, rfl⟩ | ⟨hpc, hsh⟩
      · exact (hubl h hsw t t1 f hr hτ hout).elim
      · exact ⟨t, t1, m, hr, hτ, hout, hpc, hsh⟩
  · -- a lane not at the collective is earlier
    push Not at hall
    obtain ⟨h, hsw, hnot⟩ := hall
    have hlag := hw.lag hg hsw.1.2.1 hsw hσ hk hrel (hle h hsw) fun ⟨hn, dh, hσh, hkh⟩ =>
      hnot hn dh hσh hkh
    have hph := lane_noExit hX hsound htr hub hw hg hsw hσ hk (hle h hsw)
    have htime : Sched.threadTime (timed T Q L) X h < Sched.threadTime (timed T Q L) X g := by
      rw [threadTime_eq hσ]
      exact hlag.2
    refine .inr ⟨X, .thread h, hmax, hph, ?_⟩
    rw [Sched.rank_released hrel]
    exact Sched.rank_lt_of_time_lt htime

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
