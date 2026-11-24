-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCopyHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcDrainTrace
import Lemmas.Kernel.Frame

public section

/-! # The query-copy commit preceding a pending MMA poll -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryCopyHistory

open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- Query initialization through the copy commit itself. -/
@[expose] def BeforeCommit : Wg1Mma.Site → Prop
  | .head | .elect | .loadTopk | .loadExtra | .qLoad _ | .qArrive | .qWait | .qFence
  | .qCopy _ | .qCopyCommit => True
  | _ => False

set_option maxHeartbeats 1200000 in
private theorem copy_commit_step {d d' : Machine.ThreadD} {e : Event} {q : Wg1Mma.D}
    (hBatch : Wg1Mma.geBatch L g = false)
    (hn : Machine.next P L g d e = some (some d'))
    (hd : d' = .mma q) (hq : ¬ BeforeCommit q.site) :
    ∃ prev : Wg1Mma.D, d = .mma prev ∧
      (¬ BeforeCommit prev.site ∨ prev.site = .qCopyCommit) := by
  subst d'
  cases d
  case mma old =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i next hNext
      cases hn
      refine ⟨old, rfl, ?_⟩
      cases h : old.site
      case qCopyCommit => exact .inr rfl
      all_goals try exact .inl (fun hh => hh)
      all_goals simp only [Wg1Mma.next, h, Wg1Mma.nextSite] at hNext
      all_goals repeat' split at hNext
      all_goals cases hNext
      all_goals
        try simp only [Wg1Mma.startSite, Wg1Mma.afterTopk, hBatch, Bool.false_eq_true,
          ↓reduceIte] at hq
        repeat' split_ifs at hq
        all_goals simp_all [BeforeCommit]
    · split_ifs at hn <;> cases hn
    · split_ifs at hn
      cases hn
  case prologue s =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn <;> fin_cases w <;> cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
    exact (hq trivial).elim
  all_goals
    simp only [Machine.next] at hn
    all_goals repeat' split at hn
    all_goals cases hn

private theorem commit_event_before_site {i : Nat} {q : Wg1Mma.D}
    (hBatch : Wg1Mma.geBatch L g = false) (hi : i ≤ (X.tr g).length)
    (hσ : Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)))
    (hq : ¬ BeforeCommit q.site) :
    ∃ j < i, ∃ e d, X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)) ∧ d.site = .qCopyCommit := by
  induction i generalizing q with
  | zero => rw [Frame.stateAt_zero] at hσ; cases hσ
  | succ i ih =>
    let e := (X.tr g)[i]
    have he : (X.tr g)[i]? = some e := List.getElem?_eq_getElem hi
    rw [Frame.stateAt_succ he] at hσ
    obtain ⟨prev, hs, hn⟩ := Option.bind_eq_some_iff.mp hσ
    cases prev with
    | none => cases hn
    | some p =>
      obtain ⟨d, rfl, hPoll | hCommit⟩ := copy_commit_step hBatch hn rfl hq
      · obtain ⟨j, hj, e, d', he', hs', hd'⟩ := ih (Nat.le_of_succ_le hi) hs hPoll
        exact ⟨j, hj.trans (Nat.lt_succ_self i), e, d', he', hs', hd'⟩
      · exact ⟨i, Nat.lt_succ_self i, e, d, he, hs, hCommit⟩

/-- A later MMA site follows its actual query-copy commit, with rank zero targeting its
CTA's query-copy object. -/
theorem commit_before_site {i : Nat} {q : Wg1Mma.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    (hi : i ≤ (X.tr g).length)
    (hσ : Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)))
    (hq : ¬ BeforeCommit q.site) :
    ∃ j < i, ∃ tag d sp,
      X.get (g, j) = some ⟨tag, .tc (.commit sp)⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)) ∧
      d.site = .qCopyCommit ∧
      TcCommit.target sp 0 = some ⟨.shared, ctaOf L g, L.sharedBase + 222784⟩ := by
  have hBatch := Wg1Mma.geBatch_false hpre (Wg1Mma.batchOf_lt_of_pre hpre g)
  obtain ⟨j, hj, e, d, he, hd, hsite⟩ := commit_event_before_site hBatch hi hσ hq
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hd
  obtain ⟨sp, hKind, hm, hRank⟩ := RingCommitEvents.commit_issue hpre hg (.inl hsite) hf
  cases e with
  | mk tag kind =>
    change kind = _ at hKind
    subst kind
    exact ⟨j, hj, tag, d, sp, he, hd, hsite, by simpa [hsite, hm] using hRank 0⟩

/-- The pending query-copy poll is one of the sites after its actual commit. -/
theorem commit_before_pending_wait {q : Wg1Mma.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma q)))
    (hq : q.site = .qCopyWait) :
    ∃ j < (X.tr g).length, ∃ tag d sp,
      X.get (g, j) = some ⟨tag, .tc (.commit sp)⟩ ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)) ∧
      d.site = .qCopyCommit ∧
      TcCommit.target sp 0 = some ⟨.shared, ctaOf L g, L.sharedBase + 222784⟩ :=
  commit_before_site hpre hX hs hg le_rfl hσ (by simp [hq, BeforeCommit])

/-- The asynchronous operations tracked by the query-copy commit are its actual query chunks. -/
theorem tracked_query_copy (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    {i j : Nat} {e : Event} {d : Wg1Mma.D} (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hsite : d.site = .qCopyCommit) (hTracks : TracksMma X (g, i) (g, j)) :
    ∃ k : Fin 16, X.CpIssue (g, i) (MmaDataTrace.queryCopySpec L g k) := by
  obtain ⟨w, hw, hSite⟩ := TcDrainTrace.async_site hpre hX hs ht hTracks.2.2.1
  rcases hSite with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨a, f, o, _, _, ha, haState, haSite, _, hcp⟩ :=
      query_copy_site_before_commit k hpre hX (hs g (Frame.lt_of_get hX he)).machine he hd hsite
    obtain ⟨u, hu⟩ : ∃ u, X.get (g, i) = some u := by
      rcases hTracks.2.2.1 with ⟨_, _, _, _, _, hu⟩ | ⟨_, _, hu⟩ | ⟨_, _, hu⟩
      all_goals exact ⟨_, hu⟩
    have hEq := QueryTmaSites.copy_site_unique ha hu haState hw haSite hk
    exact ⟨k, hEq ▸ hcp⟩
  · exact (Nat.not_lt_of_ge hTracks.2.1.le
      (QueryTmaSites.loop_after_copy_commit he hw hd (by simp [hk, Wg1Mma.LoopSite]) hsite)).elim
  · exact (Nat.not_lt_of_ge hTracks.2.1.le
      (QueryTmaSites.loop_after_copy_commit he hw hd (by simp [hk, Wg1Mma.LoopSite]) hsite)).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryCopyHistory
