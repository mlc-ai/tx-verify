-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreRing
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QkWriteOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingQkExitHistory
import Lemmas.Tcgen05.TcFence
import Lemmas.Protocol.PollIndex

@[expose] public section

/-! # Query operands remain live through every actual QK read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandLifetime

open PTX PTX.Flow AsyncCopy Tmem.Pair MmaDataTrace GemmRing MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem block_count_eq {g h : Nat} (hc : ctaOf L g = ctaOf L h) :
    Wg1Mma.blocks P L g = Wg0.blocksOf P L h := by
  have hb : Wg1Mma.eOf L g = Wg0.eOf L h := by
    change ctaidY L g = ctaidY L h
    simp only [ctaidY, hc]
  have hpad (n : Nat) : Wg1Mma.pad64 n = Result.ceilToMultiple n Result.topkBlock := by
    unfold Wg1Mma.pad64 Result.ceilToMultiple Result.topkBlock
    rw [show n + 64 - 1 = n + 63 by omega]
  unfold Wg1Mma.blocks Wg1Mma.total Wg1Mma.len0 Wg1Mma.len1 Wg0.blocksOf
  rw [hb, hpad, hpad, Result.blocks_eq_kernel]
  rfl

/-- The closing lane has acquired each QK block in its CTA. -/
theorem qk_wait_before_closing {h b closing : Nat} {q : Wg0.D}
    {tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (h, closing) = some ⟨tag, .bar 12 none .sync⟩)
    (hq : Frame.stateAt (Machine.code P L) X h closing = some (some (.wg0 q)))
    (hsite : q.site = .everyone) (hb : b < Wg0.blocksOf P L h) :
    ∃ (w wt parity : Nat) (scope : MbarScope) (d : Wg0.D), w < closing ∧
      X.get (h, w) = some ⟨wt, .wait (qk L (ctaOf L h) (rawSlot b)) parity true true scope⟩ ∧
      Frame.stateAt (Machine.code P L) X h w = some (some (.wg0 d)) ∧
      d.site = .qkDone ∧ d.block = b := by
  have hg := Frame.lt_of_get hX he
  have htrace := (hs h hg).machine.produces (hX.thr h hg)
  obtain ⟨_, _, ⟨_, hinv⟩, _⟩ := htrace.fired_at he hq
  have hlast := hinv.epilogueLast (by rw [hsite]; rfl)
  have hcount := Wg0GemmTrace.composed_closing_qk_count hpre (rawSlot b) htrace hq hsite
  change okPolls (qk L (ctaOf L h) (rawSlot b)) ((X.tr h).take closing) =
    (q.block + 1 + (1 - b % 2)) / 2 at hcount
  have hle : b / 2 + 1 ≤ okPolls (qk L (ctaOf L h) (rawSlot b))
      ((X.tr h).take closing) := by
    rw [hcount]
    omega
  obtain ⟨w, wt, parity, acq, scope, hw, hew, hpoll⟩ := MbarRing.Poll.exists_nth hle
  obtain ⟨⟨_, d, hslot, _, hd, hst⟩, rfl⟩ :=
    GemmRing.poll (obj := .qkDone) hpre hX (hs h hg).machine ht hew rfl
  change d.block % 2 = b % 2 at hslot
  have hwcount := Wg0GemmTrace.composed_qk_counts hpre htrace hst hd
  rw [hslot] at hwcount
  change okPolls (qk L (ctaOf L h) (rawSlot b)) ((X.tr h).take w) = _ at hwcount
  exact ⟨w, wt, parity, scope, d, hw, hew, hst, hd, by omega⟩

/-- A softmax prefix covering all blocks observes a particular QK issue before its endpoint. -/
theorem qk_completion_before_endpoint
    {g i h release : Nat} {e : Event} {d : Wg1Mma.D} {issue : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, i) Wg1Mma.tmemP
      (qkOperands L g d.i issue) (qkAccum issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qkMma issue)
    (hr : X.get (h, release) = some e) (hc : ctaOf L g = ctaOf L h)
    (hv : wgOf L h = 0)
    (hCount : ∀ slot : Fin 2, (Wg0.blocksOf P L h + (1 - slot.val)) / 2 ≤
      okPolls (qk L (ctaOf L h) slot) ((X.tr h).take release)) :
    ∃ w < release, ∃ scope, AsyncObserved X (g, i) .mmaDone (h, w) true scope ∧
      ScopesMeet L .cluster g scope h ∧ baseCausality L X (h, w) (h, release) := by
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hh := Frame.lt_of_get hX hr
  let cta := ctaOf L g
  obtain ⟨_, _, ⟨_, hinv⟩, _⟩ :=
    ((hs g hg).machine.produces (hX.thr g hg)).fired_at hi.choose_spec hd
  have hb := hinv.i_lt (by rw [hsite]; trivial)
  rw [block_count_eq (P := P) hc] at hb
  have hCount := hCount (rawSlot d.i)
  have hLe : d.i / 2 + 1 ≤ okPolls (qk L (ctaOf L h) (rawSlot d.i))
      ((X.tr h).take release) := by
    change (Wg0.blocksOf P L h + (1 - d.i % 2)) / 2 ≤
      okPolls (qk L (ctaOf L h) (rawSlot d.i)) ((X.tr h).take release) at hCount
    omega
  obtain ⟨w, wt, parity, acq, scope, hw, hew, hOrd⟩ := MbarRing.Poll.exists_nth hLe
  obtain ⟨rfl, _⟩ := RingSourceSites.actual_wait_acquire hX hew rfl
  have hCta : ctaOf L h = cta := hc.symm
  obtain ⟨lane, hl⟩ := softmax_thread hpre hCta hv
  have hw' := hew
  rw [hCta, hl] at hw' hOrd
  obtain ⟨issuer, hmma⟩ := exists_issuer (cta := cta) hpre hX (fun t ht' => (hs t ht').machine)
  have his := hmma g i d rfl hd (by rw [hsite]; simp)
  rw [← his] at hmma
  obtain ⟨commit, cmTag, sp, rank, cd, hcommit, htarget, hcd, _, hcdsite, hcb, hobs⟩ :=
    ScoreReadback.commit_of_counted_qk_wait hpre hX hs hmma hw' hOrd
  obtain ⟨last, hlast, hls, hli⟩ :=
    QkIssueHistory.qk_issue_of_commit hpre hX hs hcommit hcd hcdsite 15
  have hil := QkWriteOrder.no_later_same_block_writer hli.choose_spec hls hd rfl hsite
    hcb.ge (PTX.len_of_get hi.choose_spec).le
  have htrack : TracksMma X (g, i) (g, commit) :=
    ⟨rfl, by simp at hlast; omega, .inl ⟨_, _, _, _, hi⟩, sp, cmTag, hcommit⟩
  rw [← hl] at hobs hw'
  obtain ⟨hnotify, hobserve⟩ := hobs.waitObserves_tcNotify hw'
  have hCluster : SameCluster L g h := ⟨hg, hh, congrArg L.clusterOfCta hc⟩
  have hscope : ScopesMeet L .cluster g scope h := by
    refine ⟨hCluster, ?_⟩
    cases scope <;> first
      | exact ⟨hh, hg, hc.symm⟩
      | exact ⟨hh, hg, hCluster.2.2.symm⟩
      | exact ⟨hh, hg⟩
  have hpo : po X (h, w) (h, release) :=
    po_of_source_not_access rfl (by omega) (PTX.len_of_get hr) (by rw [hew]; rfl)
  exact ⟨w, hw, scope, ⟨_, _, ⟨(g, commit), sp, rank, rfl, htrack, ⟨cmTag, hcommit⟩,
    htarget, hnotify⟩, hobserve⟩, hscope, .single (.inl hpo)⟩

/-- The deallocation lane already observed the commit of the actual QK issue's block. -/
theorem qk_completed_before_release
    {g i h release tag base n : Nat} {group : CtaGroup} {d : Wg1Mma.D} {issue : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, i) Wg1Mma.tmemP
      (qkOperands L g d.i issue) (qkAccum issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qkMma issue)
    (hr : X.get (h, release) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩)
    (hc : ctaOf L g = ctaOf L h) : TcMma.CompletedBefore L X (g, i) (h, release) := by
  obtain ⟨closing, hBefore, hClose, start, hStart, hAnchor⟩ :=
    actual_softmax_before_dealloc hpre hX hs hr
  have hh := Frame.lt_of_get hX hr
  have hWg : wgOf L h = 0 :=
    RingRoleGeometry.of_trace hX hh (hs h hh).machine hAnchor.choose_spec.2.2
  have hCounts (slot : Fin 2) : (Wg0.blocksOf P L h + (1 - slot.val)) / 2 ≤
      okPolls (qk L (ctaOf L h) slot) ((X.tr h).take release) := by
    have hPrior := actual_qk_count_before_gate slot hpre hX hs hAnchor hStart hClose
    change _ ≤ okPolls (qk L (ctaOf L h) slot) ((X.tr h).take closing) at hPrior
    have hTake : (X.tr h).take release =
        (X.tr h).take closing ++ ((X.tr h).drop closing).take (release - closing) := by
      rw [← List.take_add, Nat.add_sub_of_le hBefore.le]
    unfold okPolls at hPrior ⊢
    rw [hTake, List.countP_append]
    omega
  obtain ⟨w, _, scope, hObserved, hScopes, hPath⟩ :=
    qk_completion_before_endpoint hpre hX hs hi hd hsite hr hc hWg hCounts
  exact TcMma.CompletedBefore.of_mma hi (.inl ⟨(h, w), scope, hObserved, hScopes, hPath⟩)

/-- Every deallocation of a covering allocation follows this operation's completed A read. -/
theorem sourceLive_of_qk {g i : Nat} {d : Wg1Mma.D} {issue : Fin 16}
    {source : EvId} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, i) Wg1Mma.tmemP
      (qkOperands L g d.i issue) (qkAccum issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .qkMma issue) (hc : cell.cta = ctaOf L g) :
    TcMma.SourceLive L X source (g, i) cell := by
  intro c r hr hcover release hre
  obtain ⟨hcta, rtag, group, base, n, hget⟩ := ScoreLifetime.release_source hX hr hre
  obtain ⟨_, _, _, howner, _, _, _⟩ := hcover
  exact .inl (qk_completed_before_release hpre hX hs hi hd hsite hget
    (hc.symm.trans (howner.trans hcta.symm)))

/-- Every A cell of an actual QK chunk reads the matching query copy in the same tracked trace. -/
theorem query_copy_read_source {g j : Nat} {d : Wg1Mma.D} {issue : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, j) Wg1Mma.tmemP
      (qkOperands L g d.i issue) (qkAccum issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hsite : d.site = .qkMma issue) :
    ∃ i e q u, X.get (g, i) = some e ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
      q.site = .qCopy issue ∧ (Machine.machine P L g).Fired (some (.mma q)) e (some u) ∧
      X.CpIssue (g, i) (queryCopySpec L g issue) ∧ X.async.mmaDone (g, i) = true ∧
      ∀ (row : Fin 128) (k : Fin 16),
        TcMma.ReadSource L X .a (g, i) (g, j)
          ⟨ctaOf L g, row.val, Wg1Mma.qkACol issue + k.val / 2⟩ := by
  obtain ⟨i, e, q, u, he, hq, hqsite, hf, hcopy, hdone, hread⟩ :=
    QueryOperandSource.read_source_of_query_copy hpre hX hs hi hd hsite
  exact ⟨i, e, q, u, he, hq, hqsite, hf, hcopy, hdone,
    fun row k => hread row k (sourceLive_of_qk hpre hX hs hi hd hsite rfl)⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryOperandLifetime
