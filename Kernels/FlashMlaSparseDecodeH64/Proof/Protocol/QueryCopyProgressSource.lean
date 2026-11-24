-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopyCompletion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryCopyHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryOperandHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Lemmas.Tcgen05.TcFence

public section

/-! # Actual query-copy read sources before completion -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopy

open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

/-- An actual copy is the recorded query-copy site with its concrete chunk descriptor. -/
theorem issue_state {g i : Nat} {c : TcCopy.Spec} (hCopy : X.CpIssue (g, i) c) :
    ∃ q k, Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qCopy k ∧ c = MmaDataTrace.queryCopySpec L g k := by
  obtain ⟨tag, he⟩ := hCopy
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hState, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by simp)
  rcases Wg0ScoreSources.writer_fields hpre hg hf (.inr (.inl ⟨c, rfl⟩)) with
    ⟨_, _, _, _, h⟩ | ⟨q, k, rfl, hsite, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
  · cases h
  · exact ⟨q, k, hState, hsite, TcKind.cp.inj (Kind.tc.inj h)⟩
  · cases h
  · cases h

/-- A successful query-copy wait in the CTA implies that all its actual query copies are done. -/
theorem copy_done_of_wait {g i w j tag : Nat} {c : TcCopy.Spec} (hCopy : X.CpIssue (g, i) c)
    (hCta : ctaOf L g = ctaOf L w)
    (hWait : X.get (w, j) = some ⟨tag, .wait (object L (ctaOf L w)) 0 true true .cta⟩) :
    X.async.mmaDone (g, i) = true := by
  let sound := fun h hh => (hs h hh).machine
  obtain ⟨q, k, hqState, hqSite, _⟩ := issue_state hpre hX hs ht hCopy
  obtain ⟨issuer, commit, _, _, _, d, he, hIssuer, hdSite, hdState, hObserve⟩ :=
    observe_query_copy_commit hpre hX sound ht hWait
  obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := ctaOf L w) hpre hX sound
  have hEq := (hLeader issuer commit d hIssuer hdState (by simp [hdSite])).trans
    (hLeader g i q hCta hqState (by simp [hqSite])).symm
  subst issuer
  obtain ⟨u, v, p, _, hLt, hEv, hState, hSite, _, hCp⟩ :=
    QueryCopyHistory.query_copy_site_before_commit k hpre hX (sound g (Frame.lt_of_get hX he))
      he hdState hdSite
  have hI := QueryTmaSites.copy_site_unique hEv hCopy.choose_spec hState hqState hSite hqSite
  subst u
  have hFinish := copy_read_finished (index := 0) hX he hCp hLt hObserve hCta
  rcases hFinish with ⟨kind, hFalse, _⟩ | ⟨scope, hObs, _⟩
  · cases kind with
    | bulk mode => cases mode <;> cases hFalse
    | cpAsync => cases hFalse
  · obtain ⟨_, _, ⟨commit', _, rank, _, hTracks, _, _, hNotified⟩, _⟩ := hObs
    exact (hX.tcCommit commit' rank hNotified).2 _ hTracks

omit hpre hX hs ht in
private theorem incomplete_copy_pipeline {g i : Nat} {w : EvId} {c : TcCopy.Spec}
    (hCopy : X.CpIssue (g, i) c) (hCommit : CommitOk X)
    (hDone : X.async.mmaDone (g, i) = false)
    (h : TcMma.WriteBefore L X (g, i) w) :
    TcMma.Pipelined L X .cpWrite (g, i) .aRead w := by
  have apart : ∀ e, X.get (g, i) = some e → e.kind = .tc (.cp c) :=
    fun e he => congrArg Event.kind (Option.some.inj (he.symm.trans hCopy.choose_spec))
  rcases h with ⟨hBefore | hPipe⟩ | hStore | hPipe
  · have h := hDone.symm.trans (hBefore.done hCommit)
    cases h
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hPipe
    cases apart _ hm.choose_spec
  · obtain ⟨_, _, _, hSt⟩ := hStore.1
    cases apart _ hSt.choose_spec
  · exact hPipe

omit hpre hX hs ht in
/-- A pending query copy cannot be a Tensor Memory load's read source. -/
theorem no_load_source_of_incomplete {g i : Nat} {w : EvId} {c : TcCopy.Spec}
    {addr : Nat} {vals : List Value} {shape : TcShape}
    (hCopy : X.CpIssue (g, i) c) (hCommit : CommitOk X)
    (hDone : X.async.mmaDone (g, i) = false) (hLoad : X.TLd w addr vals shape)
    (cell : TcMma.Cell) : ¬ TcMma.ReadSource L X .ld (g, i) w cell := by
  intro hSource
  obtain ⟨_, _, _, _, _, _, _, _, _, hMma, _⟩ :=
    incomplete_copy_pipeline hCopy hCommit hDone hSource.2.2.1
  have h := congrArg Event.kind (Option.some.inj (hLoad.choose_spec.symm.trans hMma.choose_spec))
  cases h

/-- The copy-to-A pipeline can reach only a QK consumer, whose query-copy wait already completed
every query copy in this CTA. -/
theorem no_a_source_of_incomplete {g i : Nat} {w : EvId} {c : TcCopy.Spec}
    (hCopy : X.CpIssue (g, i) c) (hDone : X.async.mmaDone (g, i) = false) (cell : TcMma.Cell)
    : ¬ TcMma.ReadSource L X .a (g, i) w cell := by
  intro hSource
  obtain ⟨hWarp, _, copy, dst, sp, accum, mask, _, _, hMma, hTmem⟩ :=
    incomplete_copy_pipeline hCopy hX.tcCommit hDone hSource.2.2.1
  obtain ⟨tag, he⟩ := hMma
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hState, hf⟩ :=
    RingSourceSites.fired_from_trace hX (hs w.1 hg).machine ht he (by simp)
  rcases Wg0ScoreSources.writer_fields hpre hg hf (.inl ⟨dst, sp, accum, mask, rfl⟩) with
    ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨d, k, rfl, hSite, _⟩ | ⟨_, _, _, _, h⟩
  · cases h
  · cases h
  · obtain ⟨j, _, tag', _, _, _, hWait, _⟩ :=
      QueryOperandHistory.wait_and_fence_before_qk hpre hX (hs w.1 hg).machine he hState hSite
    have hTrue := copy_done_of_wait hpre hX hs ht hCopy hWarp.1.2.2 hWait
    rw [hTrue] at hDone
    cases hDone
  · have hSpec := (TcKind.mma.inj (Kind.tc.inj h)).2.1
    rw [hSpec] at hTmem
    cases hTmem

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryCopy
