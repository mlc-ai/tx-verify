-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcDrainTrace
import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # The actual closing acquire orders all asynchronous tensor-memory uses before release -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Protocol AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    {g i h j tag base n : Nat} {group : CtaGroup}
include hpre hX hs ht

/-- The actual final acquire that completes a Tensor Core issue precedes deallocation. -/
theorem tc_async_observed_before_dealloc (hi : X.TcAsync (g, i)) (hCta : ctaOf L g = ctaOf L h)
    (he : X.get (h, j) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    ∃ w < j, ∃ sc, AsyncObserved X (g, i) .mmaDone (h, w) true sc ∧
      ScopesMeet L .cluster g sc h := by
  obtain ⟨a, atag, out, ha, hbar, hState, hSite⟩ :=
    ScoreReleaseTrace.barrier_before_dealloc hpre hX hs ht he
  obtain ⟨issuer, hu⟩ := GemmRing.exists_issuer (cta := ctaOf L h) hpre hX
    (fun t ht' => (hs t ht').machine)
  obtain ⟨w, wt, c, ct, sc, sp, rank, pv, hwlt, hw, hc, htarget, hctai, hSitePv, hBlockPv,
    hPv, hObs, _⟩ :=
    StageAfterPv.final_commit_before_closing hpre hX hs ht hu hbar hState hSite
  obtain ⟨old, hOld, hOldSite⟩ := TcDrainTrace.async_site hpre hX hs ht hi
  have hNotElect : old.site ≠ .elect := by
    rcases hOldSite with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hIssuer := hu g i old hCta hOld hNotElect
  subst issuer
  obtain ⟨ev, hEv⟩ : ∃ ev, X.get (g, i) = some ev := by
    rcases hi with ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
    all_goals exact ⟨_, h⟩
  have hBefore : i < c := by
    rcases hOldSite with ⟨chunk, hs'⟩ | hMma
    · exact TcDrainTrace.copy_before_pv_commit hpre hX hs hEv hOld hPv hs' hSitePv
    · have hg := Frame.lt_of_get hX hEv
      obtain ⟨_, _, _, _, hMmaInv, _, _⟩ := Frame.fired_site hs hX hEv hOld
      obtain ⟨_, _, _, _, hOutInv, _, _⟩ := Frame.fired_site hs hX hbar hState
      have hLoop : Wg1Mma.LoopSite old.site := by
        rcases hMma with ⟨_, hs'⟩ | ⟨_, hs'⟩ <;> rw [hs'] <;> trivial
      have hBound := (show Wg1Mma.Inv P L g old from hMmaInv).i_lt hLoop
      have hLast := (show Wg0.Inv P L h out from hOutInv).epilogueLast (by rw [hSite]; rfl)
      rw [StageAfterPv.block_count_eq (P := P) hCta, ← hLast] at hBound
      let slot := rawSlot out.block
      have hSlot : pv.i % 2 = slot.val := by rw [hBlockPv]; rfl
      obtain ⟨hm, _, _⟩ :=
        GemmRing.notification hpre hX (hs g hg).machine ht hc rfl htarget
      rw [← hctai] at hm
      exact StageAfterPv.issue_before_final_commit hpre hX (hs g hg) hOld hMma
        (by omega) hc hPv hSitePv hSlot hm
  obtain ⟨hNotified, hUpdate⟩ := hObs.waitObserves_tcNotify hw
  have hTrack : TracksMma X (g, i) (g, c) := ⟨rfl, hBefore, hi, sp, ct, hc⟩
  have hg := Frame.lt_of_get hX hEv
  have hh := Frame.lt_of_get hX he
  have hScopes : ScopesMeet L .cluster g sc h := by
    refine ⟨⟨hg, hh, congrArg L.clusterOfCta hCta⟩, ?_⟩
    cases sc
    · exact ⟨hh, hg, hCta.symm⟩
    · exact ⟨hh, hg, congrArg L.clusterOfCta hCta.symm⟩
    · exact ⟨hh, hg⟩
    · exact ⟨hh, hg⟩
  refine ⟨w, by omega, sc, ⟨_, _, ⟨(g, c), sp, rank, rfl, hTrack, ⟨ct, hc⟩,
    htarget, hNotified⟩, hUpdate⟩, hScopes⟩

/-- Every issued Tensor Core operation of a CTA completes before its actual deallocation. -/
theorem tc_async_before_dealloc (hi : X.TcAsync (g, i)) (hCta : ctaOf L g = ctaOf L h)
    (he : X.get (h, j) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    TcMma.DoneBefore L X (g, i) (h, j) := by
  obtain ⟨w, hwlt, sc, hObs, hScopes⟩ :=
    tc_async_observed_before_dealloc hpre hX hs ht hi hCta he
  have ⟨_, _, _, ⟨wt, parity, hw⟩, _⟩ := hObs
  refine .inl ⟨(h, w), sc, hObs, hScopes, ?_⟩
  exact .single (.inl (po_of_source_not_access rfl hwlt (PTX.len_of_get he)
    (by rw [hw]; rfl)))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
