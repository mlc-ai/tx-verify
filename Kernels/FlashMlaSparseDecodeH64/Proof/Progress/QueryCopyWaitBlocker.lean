-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.QueryWaitPhase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopyCompletion
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarQueryFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCopyWaitHistory
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.MbarRingBlocker
import Lemmas.Protocol.PairTmaRing.ItemFacts

public section

/-! # A pending query-copy poll identifies an uncaptured query chunk -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

variable (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) (hub : ¬ HasUb X)
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
include hpre hmax hs ht hub hp hrel

private theorem query_copy_poll_of_notification {d : Machine.ThreadD}
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hd : QueryWait d true) {c : EvId} {tag : Nat} {sp : TcCommit.Spec} {rank : Fin 16}
    (he : X.get c = some ⟨tag, .tc (.commit sp)⟩)
    (hTarget : TcCommit.target sp rank = some (Protocol.QueryCopy.object L (ctaOf L g)))
    (hNotify : rank ∈ X.tcNotified c) : False := by
  let m := Protocol.QueryCopy.object L (ctaOf L g)
  let log := X.objects m
  let sound := fun w hw => (hs w hw).machine
  have hAct : objectAction X X.async m (.async c (.tcNotify rank)) = some (.arrive 1 0) := by
    simp [objectAction, he, show TcCommit.target sp rank = some m from hTarget, hNotify]
  obtain ⟨r, hr, hid⟩ := (hmax.1.tma.2.2.1 m).2.2 _ _ hAct
  have ha := ((hmax.1.tma.2.2.1 m).2.1 r hr).1
  rw [hid, hAct] at ha
  have ha := (Option.some.inj ha).symm
  have hChecked := X.objects_checked hmax.1 m
  have hUnique q (hq : q ∈ log) n tx (hA : q.action = .arrive n tx) : q = r :=
    hmax.1.record_eq hq hr (Safety.query_copy_notify_unique hpre hmax.1 hs ht hq hr hA ha)
  have hUnits := one_unit_arrival (List.Nodup.of_map _ hChecked.1) hr ha
    (Safety.mbar_query_copy_clean hpre hmax.1 hs ht hr) hUnique
  have hFirst := Protocol.QueryCopy.init_first (cta := ctaOf L g) hpre hmax.1 sound ht
  obtain ⟨r0, h0, ha0, _, _⟩ := hFirst r hr
  have hNI := Protocol.objects_single_lifetime hmax.1 m
  obtain ⟨s, hState⟩ := stateBefore_length_some hChecked hNI (List.mem_of_getElem? h0) ha0
    (by decide : validCount 1)
  have hExpected := PairTmaRing.expected_of_init hmax.1 hFirst hNI hState
  have hZero : s.tx = 0 := MbarRing.tx_zero_of hmax.1 hNI
    (fun q hq n tx hA => (Protocol.QueryCopy.arrival_form hmax.1 hpre sound ht hq hA).2.1)
    (fun q hq n hA => Protocol.QueryCopy.no_completion hpre hmax.1 sound ht hq hA)
    le_rfl hState
  have hPhase := MbarRing.Blocker.units_eq_phase hChecked hNI hState hZero hExpected
    (Protocol.objects_no_pending_increment hmax.1 m)
  rw [hUnits] at hPhase
  exact hmax.not_grows (query_poll_extension hpre hs hmax.1 hub hp hrel hσ hd hState
    (by rw [← hPhase]; decide))

omit hpre hmax hs ht hub hp hrel in
private theorem copy_completion_ready {i : EvId} {sp : TcCopy.Spec}
    (hCopy : X.CpIssue i sp) : TcMma.CompletionReady L X i := by
  intro w hw
  obtain ⟨_, _, _, ⟨_, _, _, _, _, _, _, _, _, hMma, _⟩, _⟩ :=
    TcMma.completionPrecedes_iff.mp hw
  have h := congrArg Event.kind
    (Option.some.inj (hCopy.choose_spec.symm.trans hMma.choose_spec))
  cases h

/-- If a represented query wait is blocked after the matching real commit, some tracked query
chunk has not yet captured its operands. A started chunk or a ready notification would extend
the execution. -/
theorem query_copy_wait_missing_chunk {d : Machine.ThreadD}
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    (hd : QueryWait d true) {issuer j tag : Nat} {q : Wg1Mma.D} {sp : TcCommit.Spec} {rank : Fin 16}
    (he : X.get (issuer, j) = some ⟨tag, .tc (.commit sp)⟩)
    (hq : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)))
    (hSite : q.site = .qCopyCommit)
    (hTarget : TcCommit.target sp rank = some (Protocol.QueryCopy.object L (ctaOf L g))) :
    ∃ (i : Nat) (chunk : Fin 16), i < j ∧
      X.CpIssue (issuer, i) (MmaDataTrace.queryCopySpec L issuer chunk) ∧
      X.async.mmaOperands (issuer, i) = none ∧ X.async.mmaDone (issuer, i) = false := by
  by_cases hDone : ∀ i, TracksMma X i (issuer, j) → X.async.mmaDone i = true
  · have hNotify := completed_commit_notified hpre hmax hs ht ⟨tag, he⟩ hTarget hDone
    exact (query_copy_poll_of_notification
      hpre hmax hs ht hub hp hrel hσ hd he hTarget hNotify).elim
  · push Not at hDone
    obtain ⟨⟨w, i⟩, hTracks, hMissing⟩ := hDone
    obtain rfl : w = issuer := hTracks.1
    have hFalse : X.async.mmaDone (w, i) = false := Bool.eq_false_of_not_eq_true hMissing
    obtain ⟨k, hCopy⟩ := QueryCopyHistory.tracked_query_copy hpre hmax.1 hs ht he hq hSite hTracks
    have hNone : X.async.mmaOperands (w, i) = none := by
      cases ho : X.async.mmaOperands (w, i) with
      | none => rfl
      | some ops =>
        have hStarted : X.async.mmaStarted (w, i) = true := by
          simp [Snapshot.mmaStarted, ho]
        exact (hmax.not_grows (tc_completion_extension hmax.1 hStarted hFalse
          (copy_completion_ready hCopy))).elim
    exact ⟨i, k, hTracks.2.1, hCopy, hNone, hFalse⟩

/-- The MMA lane's own pending query-copy wait supplies the actual commit automatically. -/
theorem pending_mma_query_copy_missing_chunk {d : Wg1Mma.D}
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.mma d)))
    (hd : d.site = .qCopyWait) :
    ∃ (i : Nat) (chunk : Fin 16), i < (X.tr g).length ∧
      X.CpIssue (g, i) (MmaDataTrace.queryCopySpec L g chunk) ∧
      X.async.mmaOperands (g, i) = none ∧ X.async.mmaDone (g, i) = false := by
  obtain ⟨j, hj, _, q, _, he, hq, hSite, hTarget⟩ := QueryCopyHistory.commit_before_pending_wait
    hpre hmax.1 (hs g hp.1).machine hp.1 hσ hd
  obtain ⟨i, k, hi, hCopy, hNone, hFalse⟩ :=
    query_copy_wait_missing_chunk hpre hmax hs ht hub hp hrel hσ
      (.copy d rfl hd) he hq hSite hTarget
  exact ⟨i, k, hi.trans hj, hCopy, hNone, hFalse⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
