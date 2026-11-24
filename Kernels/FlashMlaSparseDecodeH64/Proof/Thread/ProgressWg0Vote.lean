-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Lemmas.Step.WarpVoteMode

public section

/-! # Issuing the softmax rescale decision -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

/-- When every warp lane reaches its rescale vote, the actual predicates select the result of
one full-mask vote. -/
theorem softmax_rescale_vote_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) (hub : ¬ HasUb X)
    (hall : ∀ h, SameWarp L g h → ∃ d, Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
      Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some (.wg0 d)) ∧
      d.site = .rescaleVote) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  let d (h : Nat) (hw : SameWarp L g h) := (hall h hw).choose
  let a (h : Nat) := if hw : SameWarp L g h then (d h hw).voteTest else false
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  refine PTX.Step.vote_mode_counted_extension (pc := Wg0.Site.rescaleVote.pc) hX hb .any a hg
    (fun h _ => (full_member L h).2) ?_ (fun h hw => (hall h hw).choose_spec.2.1) ?_ ?_
  · intro h hw
    obtain ⟨d, _, _, hState, _⟩ := hall h hw
    refine .inl ?_
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hState
    cases hState
  · intro h hw result
    have hPending := (hall h hw).choose_spec.1
    have hState := (hall h hw).choose_spec.2.2.1
    have hSite := (hall h hw).choose_spec.2.2.2
    obtain ⟨t, hRun⟩ := Frame.run_some hX hub hPending
    obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hPending.1 hRun hState
    rw [Wg0.rescaleVote_template hpre hSite ha hc] at hout
    have hp : u.pc = Wg0.Site.rescaleVote.pc := ha.1.trans (congrArg Wg0.Site.pc hSite)
    dsimp only [a]
    rw [dite_eq_left hw]
    exact ⟨t, u, some (PTX.next (setReg u 1 (.pred result))), hRun, hTau, _, hout,
      result, by rw [hp], rfl⟩
  · intro result
    apply all_wf_collective_batch hX (PTX.Step.warpThreads L g)
    · intro _ _ _ h
      exact Kind.noConfusion h
    · intro _ _ _ h
      exact Kind.noConfusion h
    · intro _ h
      exact Kind.noConfusion h

set_option maxHeartbeats 800000 in
private theorem vote_previous_not_blocking {P : Params} {L : Launch} {g : Nat}
    {z d : Wg0.D} {e : Event} (hn : Wg0.next P L g z e = some (some d))
    (hd : d.site = .rescaleVote) : e.kind.resume ≠ .blocking false := by
  intro h
  cases hk : e.kind <;> simp only [hk, Kind.resume, reduceCtorEq, Resume.blocking.injEq,
    Bool.true_eq_false] at h
  case' tc k => cases k <;> simp only [TcKind.resume, reduceCtorEq] at h
  all_goals
    cases hs : z.site <;>
      simp only [Wg0.next, Wg0.nextSite, hs, hk, Wg0.waitStep, Wg0.writeStep, reduceCtorEq] at hn
  all_goals repeat' split at hn
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hn
  all_goals
    have hSite := congrArg Wg0.D.site hn
    rw [hd] at hSite
    try simp only [Wg0.epiAfterBar, Wg0.afterScoreSite] at hSite
    try split_ifs at hSite
    all_goals cases hSite

/-- At the reference vote, the last event is already released. -/
theorem softmax_vote_released {P : Params} {L : Launch} {X : Execution}
    {g : Nat} {d : Wg0.D}
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hSite : d.site = .rescaleVote) : PTX.Step.Released L X g := by
  apply PTX.Step.Released.of_get
  intro e he
  have hLen := PTX.len_of_get he
  have hTail : (X.tr g).length - 1 + 1 = (X.tr g).length := by
    change (X.tr g).length - 1 < (X.tr g).length at hLen
    omega
  obtain ⟨q, r, _, hr, hn⟩ := FollowedPrefix.step_at hd hLen he
  rw [hTail, hd] at hr
  obtain rfl := Option.some.inj (Option.some.inj hr)
  change Machine.next P L g q e = some (some (.wg0 d)) at hn
  cases q
  case wg0 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i d' hStep
      cases hn
      exact vote_previous_not_blocking hStep hSite
    · split at hn <;> cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp [Kind.resume]
  case prologue q =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i wg _
        split_ifs at hn
        · fin_cases wg <;> cases hn
          change Wg0.firstSite P = .rescaleVote at hSite
          simp only [Wg0.firstSite, Wg0.afterSink, Wg0.afterLen] at hSite
          split_ifs at hSite
        · cases hn
      · cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
