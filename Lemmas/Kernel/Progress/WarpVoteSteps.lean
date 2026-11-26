-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WarpCollRelU
public import Lemmas.Step.WarpVoteMode

@[expose] public section

/-! # Progress at a mode vote

A proof tool, generic over the kernel: `Sched.warpColl_steps_relU` for a mode vote (`vote.sync`
with mode `.all`, `.any` or `.uni`), which is no warp collective of the count (`isWarpColl`). The
votes of a lane are counted by their member mask (`Step.maskCount voteClass X h mask`), and the
warp's lanes perform one instance with `Step.vote_mode_counted_extension` in place of
`coll_batch`. With the facts `WarpVoteRel` about the states at the vote (`AtVote`):

* no lane of the warp has made more votes with the mask than a pending lane (`vote_lane_of_ready`:
  the lane would have a partner, or the pending lane would have exited);
* a lane that has made at most as many votes and is not at the vote is earlier (`lag`) and not
  exited (`exit`): it is a pending thread of smaller rank;
* otherwise every lane is at the vote, released, and its template is the vote with the mask and
  its own predicate (`tmpl`): either some lane's run reaches undefined behaviour, which is
  performed (`hubx`), or the warp performs one instance. -/

namespace PTX.Sched

open PTX Classical

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution} {κ : Type}

/-- **The facts of a kernel's mode vote** at the pc `pc` with the member mask `mask`, for the
states classified as at the vote (`AtVote`), with the lanes' warp key `key`. -/
structure WarpVoteRel (mem0 : Mem0) (M : Timed K A L) (X : Execution) (key : Nat → κ)
    (AtVote : ∀ g, (M.code g).D → Prop) (pc mask : Nat) (mode : VoteMode) : Prop where
  /-- The template at a state at the vote is undefined behaviour or the vote with the mask. -/
  tmpl : ∀ {g : Nat} {d : (M.code g).D} {t : TState} {ins : Instr}, g < L.threads →
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtVote g d →
    (M.code g).AtD d t → (M.code g).inv d → K.code[(M.code g).pc d]? = some ins →
    (∃ f, eventTmpl A L g t ins.op = .ub f) ∨
      ∃ a k, eventTmpl A L g t ins.op = .voteMode mode mask a k ∧ t.pc = pc
  /-- A lane at the vote is released. -/
  released : ∀ {g : Nat} {d : (M.code g).D}, g < L.threads →
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtVote g d →
    Step.Released L X g
  /-- A lane exits after a number of votes fixed by its warp, more than a lane at the vote has
  made. -/
  exit : ∃ T : κ → Nat,
    (∀ {g : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtVote g d →
      Step.maskCount voteClass X g mask < T (key g)) ∧
    (∀ {g k pc' : Nat} {d : (M.code g).D}, g < L.threads →
      Frame.stateAt M.code X g k = some (some d) → X.get (g, k) = some ⟨pc', .exit⟩ →
      T (key g) ≤ (((X.tr g).take k).countP fun ev => (voteClass ev.kind).any (·.mask == mask)))
  /-- A pending lane whose machine stopped is released. -/
  dead : ∀ {h : Nat}, Frame.Pending L X h →
    Frame.stateAt M.code X h (X.tr h).length = none → Step.Released L X h
  /-- A lane of the warp of a thread at the vote that has made at most as many votes and is not
  at the vote is earlier. -/
  lag : ∀ {g h : Nat} {d : (M.code g).D}, g < L.threads → h < L.threads → SameWarp L g h →
    Frame.stateAt M.code X g (X.tr g).length = some (some d) → AtVote g d →
    Step.maskCount voteClass X h mask ≤ Step.maskCount voteClass X g mask →
    ¬ (Step.maskCount voteClass X h mask = Step.maskCount voteClass X g mask ∧
      ∃ d', Frame.stateAt M.code X h (X.tr h).length = some (some d') ∧ AtVote h d') →
    Frame.stateAt M.code X h (X.tr h).length ≠ none →
    threadTime M X h < M.time g d

variable {key : Nat → κ} {AtVote : ∀ g, (M.code g).D → Prop} {pc mask : Nat} {mode : VoteMode}

/-- **No lane of the warp is past a pending lane** in its votes with the member mask. -/
theorem vote_no_ahead (hX : Consistent L K A mem0 X)
    (hm : ∀ l, l < 32 → mask.testBit l = true) {g h : Nat} (hs : SameWarp L g h)
    {t : TState} (hr : Run K A L g {} (X.tr g) (some t)) :
    Step.maskCount voteClass X h mask ≤ Step.maskCount voteClass X g mask := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ := Step.exists_maskK (X := X) (c := voteClass) (g := h) (m := mask)
    (n := Step.maskCount voteClass X g mask) hlt
  rcases Step.vote_lane_of_ready hX hj (sameWarp_symm hs) (hm _ (Nat.mod_lt _ (by decide))) with
    ⟨j', hk'⟩ | ⟨k, pce, hex⟩
  · exact Nat.lt_irrefl _ (Step.MaskK.lt_count hk')
  · exact hr.no_exit hex

/-- **A lane of the warp of a lane at the vote has not exited** when it has made at most as many
votes. -/
theorem WarpVoteRel.lane_noExit (hw : WarpVoteRel mem0 M X key AtVote pc mask mode)
    (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h) (hX : Consistent L K A mem0 X)
    (hsound : ∀ g < L.threads, (M.code g).SoundU) (htr : Frame.Tracked M.code X)
    (hub : ¬ HasUb X) (hcl : ∀ h, ¬ ClcCanceled L X h) {g h : Nat} {d : (M.code g).D}
    (hg : g < L.threads) (hs : SameWarp L g h)
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtVote g d)
    (hle : Step.maskCount voteClass X h mask ≤ Step.maskCount voteClass X g mask) :
    Frame.Pending L X h := by
  obtain ⟨T, hT1, hT2⟩ := hw.exit
  refine ⟨hs.1.2.1, hcl h, fun pc' hl => ?_⟩
  have hex := exit_get hl
  obtain ⟨dx, hdx⟩ := Frame.state_of_noUbU hsound hX htr hub hex
  have h1 := hT1 hg hσ hk
  have h2 := hT2 hs.1.2.1 hdx hex
  have h3 := Flow.countP_take_mono (fun ev => (voteClass ev.kind).any (·.mask == mask))
    (X.tr h) (Nat.sub_le (X.tr h).length 1)
  rw [List.take_length] at h3
  rw [← hkey hs] at h2
  unfold Step.maskCount at h1 hle
  omega

/-- **Progress at a mode vote.** A released pending thread whose state at its trace's end is at
the vote steps. -/
theorem warpVote_steps (hkey : ∀ {g h : Nat}, SameWarp L g h → key g = key h)
    (hsound : ∀ g < L.threads, (M.code g).SoundU) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X) (hw : WarpVoteRel mem0 M X key AtVote pc mask mode)
    (hm : ∀ l, l < 32 → mask.testBit l = true)
    (hb : L.block % 32 = 0) (hlaunch : ∀ h, Step.Launched L X h)
    (hcl : ∀ h, ¬ ClcCanceled L X h)
    (happ : ∀ (ds : List Nat) (ev : Nat → Event), (∀ x, (ev x).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev))
    (hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run K A L h {} (X.tr h) (some t) → Relation.ReflTransGen (Tau K A L h) t t1 →
      out K A L h t1 = .ev (.ub f) → ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtVote g d) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hub := safe_noUb (hs.2 X hX)
  have hrel := hw.released hg hσ hk
  obtain ⟨tg, hrg⟩ := Frame.run_some hX hub hp
  have hle : ∀ h, SameWarp L g h →
      Step.maskCount voteClass X h mask ≤ Step.maskCount voteClass X g mask :=
    fun h hsw => vote_no_ahead hX hm hsw hrg
  by_cases hall : ∀ h, SameWarp L g h →
      Step.maskCount voteClass X h mask = Step.maskCount voteClass X g mask ∧
      ∃ dh, Frame.stateAt M.code X h (X.tr h).length = some (some dh) ∧ AtVote h dh
  · -- every lane at the vote
    have hrels : ∀ h, SameWarp L g h → Step.Released L X h := fun h hsw => by
      obtain ⟨-, dh, hσh, hkh⟩ := hall h hsw
      exact hw.released hsw.1.2.1 hσh hkh
    have hfire : ∀ h, SameWarp L g h → ∃ t t1 m, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev m ∧
        ((∃ f, m = .ub f) ∨ ∃ a k, m = .voteMode mode mask a k ∧ t1.pc = pc) := by
      intro h hsw
      obtain ⟨-, dh, hσh, hkh⟩ := hall h hsw
      have hh := hsw.1.2.1
      obtain ⟨t, hr⟩ := Frame.run_some hX hub
        (hw.lane_noExit hkey hX hsound htr hub hcl hg hsw hσ hk (hle h hsw))
      rcases Frame.end_atU hsound hh hr hσh with hsite | ⟨u, f, hτ, ho⟩
      case inr => exact ⟨t, u, _, hr, hτ, ho, .inl ⟨f, rfl⟩⟩
      obtain ⟨t1, ins, hτ, hat, hinv, hc, hout⟩ := hsite
      exact ⟨t, t1, _, hr, hτ, hout, hw.tmpl hh hσh hkh hat hinv hc⟩
    by_cases hubl : ∃ h, SameWarp L g h ∧ ∃ t t1 f, Run K A L h {} (X.tr h) (some t) ∧
        Relation.ReflTransGen (Tau K A L h) t t1 ∧ out K A L h t1 = .ev (.ub f)
    · obtain ⟨h, hsw, t, t1, f, hr, hτ, hout⟩ := hubl
      exact .inl (hubx hsw.1.2.1 (hrels h hsw) hr hτ hout)
    · push Not at hubl
      have hv : ∀ h, SameWarp L g h → ∃ (a : Bool) (t t1 : TState),
          Run K A L h {} (X.tr h) (some t) ∧ Relation.ReflTransGen (Tau K A L h) t t1 ∧
          ∃ k, out K A L h t1 = .ev (.voteMode mode mask a k) ∧ t1.pc = pc := by
        intro h hsw
        obtain ⟨t, t1, m, hr, hτ, hout, hm'⟩ := hfire h hsw
        rcases hm' with ⟨f, rfl⟩ | ⟨a, k, rfl, hpc⟩
        · exact (hubl h hsw t t1 f hr hτ hout).elim
        · exact ⟨a, t, t1, hr, hτ, k, hout, hpc⟩
      have : Nonempty TState := ⟨{}⟩
      choose! a t t1 hr hτ k hout hpc using hv
      refine .inl (Step.vote_mode_counted_extension (pc := pc) hX hb mode a hg
        (fun h _ => hm _ (Nat.mod_lt _ (by decide))) (fun h _ => .inr (hlaunch h))
        hrels (fun h hsw result => ⟨t h, t1 h, some (k h result), hr h hsw, hτ h hsw, ?_⟩)
        (fun result => ?_))
      · exact ⟨_, hout h hsw, result, by rw [hpc h hsw], rfl⟩
      · exact happ _ _ fun _ => rfl
  · -- a lane not at the vote is earlier
    push Not at hall
    obtain ⟨h, hsw, hnot⟩ := hall
    have hph := hw.lane_noExit hkey hX hsound htr hub hcl hg hsw hσ hk (hle h hsw)
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
