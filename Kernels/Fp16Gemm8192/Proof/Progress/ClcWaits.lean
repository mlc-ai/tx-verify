-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Descent

@[expose] public section

/-! # Progress at the CLC waits

The CLC response barrier and the acknowledgement barrier are polled as mbarrier waits, so each
wait steps by `Descent.mbar_wait_steps`: a ready poll is a counted extension, and a failed poll is
blocked by an open obligation of smaller rank.

* A role at its CLC poll (`atClcWait`) is blocked, after a failed poll of the response barrier, by
  an undelivered request of the cluster (rank 1) or by the leader scheduler, whose next event ranks
  at most `blockAt n + 4` (`ClcBlocked`).
* The leader scheduler at its acknowledgement poll (`atAckWait`) is blocked by an acknowledging
  thread that has arrived fewer than `n` times on the barrier, whose next event ranks below
  `blockAt n`, or that has stopped without its exit (rank at most 1) (`AckBlocked`).

The protocol exports and the poll and rank facts of the threads are the premises of `ClcWaitFacts`
and of the two steps. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow MBarrier AsyncCopy Classical

noncomputable section

/-- The protocol exports and the thread facts the CLC waits use, for every consistent execution. -/
structure ClcWaitFacts (L : Launch) (mem0 : Mem0) : Prop where
  ub : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ HasUb Y
  thread : ∀ Y, Consistent L kernel Prod mem0 Y → ThreadFacts L Y
  clcBlocked : ∀ Y, Consistent L kernel Prod mem0 Y → ClcBlocked L Y
  ackBlocked : ∀ Y, Consistent L kernel Prod mem0 Y → AckBlocked L Y
  /-- An acknowledging thread outside the exit stage ranks below the block of its arrivals plus
  one: its next event is in the block of its own acknowledgements. -/
  ackRank : ∀ Y, Consistent L kernel Prod mem0 Y → ∀ (b : Nat) (d : ThreadD), b < L.threads →
    (∃ f : Fin 10, ClcRing.consumerSel L (b / L.block / 2) f b = true) →
    Frame.stateAt (code L) Y b (Y.tr b).length = some (some d) → d.exitOff = none →
    d.vtime L b (Y.tr b) + 1 <
      blockAt (arrivals (Bar.loc L (2 * (b / L.block / 2)) ⟨.clc, 0, false⟩) (Y.tr b) + 1)

theorem blockAt_mono {a n : Nat} (h : a ≤ n) : blockAt a ≤ blockAt n := by
  unfold blockAt blockSpan
  omega

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Progress at a CLC response wait.** A pending role at its CLC poll, whose last event is
released, extends a maximal execution or passes to an obligation of smaller rank. Its rank is at
least `blockAt n + 6` for its `n` successful response polls (`hcount`). -/
theorem clc_wait_steps (hF : ClcWaitFacts L mem0) (hmax : Maximal L kernel Prod mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hrel : Step.Released L X g) (hne : X.tr g ≠ [])
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
      (hd : d.AtClcWait)
    (hcount : blockAt (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) + 6 ≤
      threadTime L X g)
    {before : MBarrier.State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).length = some before) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  refine Descent.mbar_wait_steps prod_wfFree (hF.ub X hX) hmax hp hrel hne
    (m := Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (pcw := (code L g).pc d) (par := d.cpOf)
    (Q := fun sc => (code L g).toMachine.after (some (code L g).init) (X.tr g ++
      [⟨(code L g).pc d, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) d.cpOf false true sc⟩]) =
        some (some d))
    (fun t hr ok => (hF.thread X hX).clc_poll hg hσ hd hr ok) hstate fun sc hq hready hYmax => ?_
  · generalize hpcw : (code L g).pc d = pcw at hq hYmax ⊢
    generalize hpar : d.cpOf = par at hq hready hYmax ⊢
    generalize hY : Step.failedPoll X g pcw par (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) true sc
      before = Y at hYmax ⊢
    have hYc := hYmax.1
    have htrY : Y.tr g = X.tr g ++ [⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) par false
        true sc⟩] := by
      rw [← hY, Step.failedPoll_tr]
      simp
    have hσY : Frame.stateAt (code L) Y g (Y.tr g).length = some (some d) := by
      unfold Frame.stateAt
      rw [List.take_length, htrY]
      exact hq
    have hlastY : (Y.tr g).getLast? = some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)
        par false true sc⟩ := by
      rw [htrY]
      simp
    have hstateY : stateBefore (Y.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩))
        (Y.objects (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩)).length = some before := by
      rw [← hY, Step.failedPoll_objects]
      simp [stateBefore, Step.failedRecord]
    have hcnt : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (Y.tr g) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g) := by
      rw [htrY]
      simp [Flow.okPolls, List.countP_append, okPoll, sourceWaitSuccess]
    have hrank : rank L X (.thread g) = threadTime L X g := rank_released hrel
    have hcX : 1 < rank L X (.thread g) := by
      rw [hrank]
      unfold blockAt blockSpan at hcount
      omega
    rcases hF.clcBlocked Y hYc g pcw par true sc before d hg hσY hd hlastY hstateY hready with
      ⟨i, s, tg, hi, hnot⟩ | ⟨h, hh, -, -, hne', ⟨d', hσh, hex, hdv⟩ | ⟨hdead, hnx⟩⟩
    · refine ⟨.clc, by simp only [Descent.Obl]; exact fun hall => hnot (hall i s tg hi), ?_⟩
      have h1 : rank L Y .clc = 1 := rfl
      rw [h1]
      exact hcX
    · have hpend : Frame.Pending L Y h := ⟨hh, fun hc => hne' hc.1, fun pc' hl => by
        rw [(hF.thread Y hYc).exited_state hh hl] at hσh
        cases hσh⟩
      have hdv' : d'.vtime L h (Y.tr h) ≤
          blockAt (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) (X.tr g)) + 4 := by
        rw [← hcnt]
        exact hdv
      have hr1 : rank L Y (.thread h) ≤ threadTime L Y h + 1 := rank_thread_le
      have hr2 : threadTime L Y h = d'.vtime L h (Y.tr h) := threadTime_of hσh hex
      refine ⟨.thread h, hpend, ?_⟩
      rw [hrank]
      unfold blockAt blockSpan at hdv' hcount
      omega
    · -- a warp-10 thread stopped without its exit is pending, of rank at most one
      have hpend : Frame.Pending L Y h := ⟨hh, fun hc => hne' hc.1, hnx⟩
      have hr1 : rank L Y (.thread h) ≤ threadTime L Y h + 1 := rank_thread_le
      have hr2 : threadTime L Y h = 0 := by simp [threadTime, hdead]
      refine ⟨.thread h, hpend, ?_⟩
      omega

/-- **Progress at the leader scheduler's acknowledgement wait.** The leader scheduler (warp 10 of
an even CTA) at its acknowledgement poll, whose last event is released, extends a maximal execution
or passes to an obligation of smaller rank. Its rank is the block of its successful response polls,
which are its successful acknowledgement polls (`hcount`). -/
theorem ack_wait_steps (hF : ClcWaitFacts L mem0) (hmax : Maximal L kernel Prod mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hrel : Step.Released L X g) (hne : X.tr g ≠ [])
    (hlead : g / L.block % 2 = 0) (hwarp : g % L.block / 32 = 10) {pcw par : Nat}
    (hpoll : ∀ t, Run kernel Prod L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1
        ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) par ok true sc⟩ (some u))
    (hcount : blockAt (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g)) ≤
      threadTime L X g)
    {before : MBarrier.State}
    (hstate : stateBefore (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩))
      (X.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩)).length = some before) :
    Descent.Steps L kernel Prod mem0 (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  refine Descent.mbar_wait_steps prod_wfFree (hF.ub X hX) hmax hp hrel hne
    (m := Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (pcw := pcw) (par := par)
    (Q := fun _ => True) (fun t hr ok => ?_) hstate fun sc _ hready hYmax => ?_
  · obtain ⟨t1, u, sc, h1, h2⟩ := hpoll t hr ok
    exact ⟨t1, u, sc, h1, h2, fun _ => trivial⟩
  · generalize hY : Step.failedPoll X g pcw par (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) true sc
      before = Y at hYmax ⊢
    have hYc := hYmax.1
    have hg := hp.1
    have htrY : Y.tr g = X.tr g ++ [⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) par false
        true sc⟩] := by
      rw [← hY, Step.failedPoll_tr]
      simp
    have hlastY : (Y.tr g).getLast? = some ⟨pcw, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩)
        par false true sc⟩ := by
      rw [htrY]
      simp
    have hstateY : stateBefore (Y.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩))
        (Y.objects (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩)).length = some before := by
      rw [← hY, Step.failedPoll_objects]
      simp [stateBefore, Step.failedRecord]
    have hcnt : okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (Y.tr g) =
        okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g) := by
      rw [htrY]
      simp [Flow.okPolls, List.countP_append, okPoll, sourceWaitSuccess]
    have hrank : rank L X (.thread g) = threadTime L X g := rank_released hrel
    obtain ⟨b, hb, hbne, ⟨f, hf⟩, harr, ⟨d, hσb, hex⟩ | ⟨hdead, hnx⟩⟩ :=
      hF.ackBlocked Y hYc g pcw par true sc before hg hlead hwarp hlastY hstateY hready
    swap
    · -- an acknowledging thread stopped without its exit is pending, of rank at most one
      have hpend : Frame.Pending L Y b := ⟨hb, fun hc => hbne hc.1, hnx⟩
      have hr1 : rank L Y (.thread b) ≤ threadTime L Y b + 1 := rank_thread_le
      have hr2 : threadTime L Y b = 0 := by simp [threadTime, hdead]
      refine ⟨.thread b, hpend, ?_⟩
      rw [hrank]
      unfold blockAt blockSpan at hcount
      omega
    have hcl : b / L.block / 2 = g / L.block / 2 := by
      have h1 := hf
      simp only [ClcRing.consumerSel, decide_eq_true_eq] at h1
      have hc := ClcRing.ctaOf_lt f
      have h2 := h1.1
      omega
    have hf' : ClcRing.consumerSel L (b / L.block / 2) f b = true := by
      rw [hcl]
      exact hf
    have hloc : 2 * (b / L.block / 2) = g / L.block := by
      rw [hcl]
      omega
    have hrk := hF.ackRank Y hYc b d hb ⟨f, hf'⟩ hσb hex
    rw [hloc] at hrk
    rw [hcnt] at harr
    have hbk : blockAt (arrivals (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (Y.tr b) + 1) ≤
        blockAt (okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, false⟩) (X.tr g)) :=
      blockAt_mono (by omega)
    have hr1 : rank L Y (.thread b) ≤ threadTime L Y b + 1 := rank_thread_le
    have hr2 : threadTime L Y b = d.vtime L b (Y.tr b) := threadTime_of hσb hex
    have hpend : Frame.Pending L Y b := ⟨hb, fun hc => hbne hc.1, fun pc' hl => by
      rw [(hF.thread Y hYc).exited_state hb hl] at hσb
      cases hσb⟩
    refine ⟨.thread b, hpend, ?_⟩
    rw [hrank]
    omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
