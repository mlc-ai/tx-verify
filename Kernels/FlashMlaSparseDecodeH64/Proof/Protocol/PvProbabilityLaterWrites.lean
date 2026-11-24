-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmCompletion
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity
import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # Later score-exchange and probability writes observe completion of the old PV read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource

open PTX PTX.Flow AsyncCopy MmaDataTrace GemmRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A later counted QK acquire makes the earlier PV read complete before the actual event. -/
theorem prior_pv_read_finished_of_count {g i h j index later : Nat} {d : Wg1Mma.D}
    {issue : Fin 8} {e : Event} {isB : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (hBlock : d.i < later)
    (he : X.get (h, j) = some e) (hWG : wgOf L h = 0) (hc : ctaOf L g = ctaOf L h)
    (hCount : later / 2 + 1 ≤
      okPolls (qk L (ctaOf L h) (rawSlot later)) ((X.tr h).take j)) :
    X.AsyncPresent (g, i) .mmaDone ∧ TcMma.DoneBefore L X (g, i) (h, j) ∧
      ∃ wait < j, AsyncFinished L X (g, i) (.mmaRead isB index) (h, wait) ∧
        baseCausality L X (h, wait) (h, j) := by
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hh := Frame.lt_of_get hX he
  let cta := ctaOf L g
  let m := qk L cta (rawSlot later)
  rw [← hc] at hCount
  change later / 2 + 1 ≤ okPolls m ((X.tr h).take j) at hCount
  obtain ⟨w, tag, parity, acq, scope, hwj, hw, hOrdinal⟩ := MbarRing.Poll.exists_nth hCount
  have hAcq := MachineTracking.actual_qk_wait_is_acquire hpre hX hs hWG hw
  subst acq
  obtain ⟨lane, hl⟩ := softmax_thread hpre hc.symm hWG
  have hw' : X.get (softmax L cta lane, w) =
      some ⟨tag, .wait m parity true true scope⟩ := by rwa [← hl]
  rw [hl] at hOrdinal
  obtain ⟨issuer, hmma⟩ := exists_issuer (cta := cta) hpre hX (fun t ht' => (hs t ht').machine)
  have his := hmma g i d rfl hd (by rw [hsite]; simp)
  rw [← his] at hmma
  obtain ⟨c, src, sp, rank, cd, hcommit, htarget, hcd, _, _, hCBlock, hobs⟩ :=
    ScoreReadback.commit_of_counted_qk_wait hpre hX hs hmma hw' hOrdinal
  have hBefore : i < c := by
    by_contra! hNot
    have hOrder := Wg1Mma.block_order hNot hcd hd
    omega
  have hTrack : TracksMma X (g, i) (g, c) :=
    ⟨rfl, hBefore, .inl ⟨_, _, _, _, hi⟩, sp, ⟨src, hcommit⟩⟩
  rw [← hl] at hw' hobs
  have hCluster : SameCluster L g h := ⟨hg, hh, congrArg L.clusterOfCta hc⟩
  have hScope : ScopesMeet L .cluster g scope h := by
    refine ⟨hCluster, ?_⟩
    cases scope <;> first
      | exact ⟨hh, hg, hc.symm⟩
      | exact ⟨hh, hg, hCluster.2.2.symm⟩
      | exact ⟨hh, hg⟩
  obtain ⟨hDone, hFinish⟩ := completed_read hX ⟨src, hcommit⟩ htarget hTrack hScope hw' hobs
  obtain ⟨hNotify, hObserve⟩ := hobs.waitObserves_tcNotify hw'
  have hBase : baseCausality L X (h, w) (h, j) :=
    .single (.inl (po_of_source_not_access rfl hwj (PTX.len_of_get he) (by rw [hw]; rfl)))
  have hDoneBefore : TcMma.DoneBefore L X (g, i) (h, j) :=
    .inl ⟨(h, w), scope,
      ⟨_, _, ⟨(g, c), sp, rank, rfl, hTrack, ⟨src, hcommit⟩, htarget, hNotify⟩, hObserve⟩,
      hScope, hBase⟩
  exact ⟨hDone, hDoneBefore, w, hwj, hFinish, hBase⟩

/-- The writer of a later exchange or probability byte already observed the earlier PV read's
completion on its own thread's successful QK poll. -/
theorem prior_pv_read_finished {g i h j index : Nat} {d : Wg1Mma.D} {q : Wg0.D}
    {issue : Fin 8} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (hBlock : d.i < q.block)
    (he : X.get (h, j) = some e)
    (hq : Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 q)))
    (hQSite : (∃ k : Fin 8, q.site = .exchStore k) ∨ (∃ k : Fin 4, q.site = .pStore k))
    (hc : ctaOf L g = ctaOf L h) :
    X.AsyncPresent (g, i) .mmaDone ∧
      ∃ wait < j, AsyncFinished L X (g, i) (.mmaRead false index) (h, wait) := by
  have hh := Frame.lt_of_get hX he
  let trace := (hs h hh).machine.produces (hX.thr h hh)
  have hCount : okPolls (qk L (ctaOf L h) (rawSlot q.block)) ((X.tr h).take j) =
      q.block / 2 + 1 := by
    rcases hQSite with ⟨k, hk⟩ | hp
    · exact Wg0GemmTrace.composed_exchange_qk_count hpre trace hq hk
    · exact (Wg0GemmTrace.composed_probability_counts hpre trace hq hp).2
  have hWG := RingRoleGeometry.of_trace hX hh (hs h hh).machine hq
  obtain ⟨hDone, _, w, hLt, hFinish, _⟩ :=
    prior_pv_read_finished_of_count hpre hX hs hi hd hsite hBlock he hWG hc hCount.ge
  exact ⟨hDone, w, hLt, hFinish⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilitySource
