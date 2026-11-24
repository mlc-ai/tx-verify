-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.WaitOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressLastStorePoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarLastStoreFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0LastStoreTrace
import Lemmas.Clc.ClcExecution
import Lemmas.Protocol.NamedBarSources

public section

/-! # A pending last-store wait descends to an earlier softmax lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem early_last_store_priority {g h : Nat} {d : Machine.ThreadD}
    {t : Wg1Tma.D} (hEarly : Wg0LastStoreTrace.Early d) (ht : t.site = .waitLast) :
    priority P L h d < priority P L g (.tma t) := by
  cases hEarly
  case prologue s =>
    simp only [priority, gatherTime, ht, Bound.tmaOrdinal]
    omega
  case softmax q h =>
    cases hq : q.site <;> simp only [Wg0LastStoreTrace.Initial, hq] at h
    all_goals
      simp only [priority, softmaxTime, gatherTime, hq, ht, Bound.wg0Ordinal, Bound.tmaOrdinal]
      omega

/-- For a maximal execution at a released producer's last-store poll, some softmax lane of
its CTA has yet to arrive and has a strictly earlier dependency priority. -/
theorem pending_last_store_earlier
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) (hub : ¬ HasUb X)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d))
    {g : Nat} {t : Wg1Tma.D} (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.tma t)))
    (hSite : t.site = .waitLast) :
    ∃ other q, SameCta L g other ∧ Frame.Pending L X other ∧
      Frame.stateAt (Machine.code P L) X other (X.tr other).length = some (some q) ∧
      priority P L other q < priority P L g (.tma t) := by
  let cta := ctaOf L g
  let m : Loc := ⟨.shared, cta, L.sharedBase + 222768⟩
  classical
  by_cases hAll : ∀ k : Fin 128, ∃ i tag, X.get (cta * L.block + k.val, i) = some
      ⟨tag, .arrive m 0 1 true .cta⟩
  · obtain ⟨st, hFinal, hPhase⟩ :=
      Safety.last_store_phase_of_all_arrivals hpre hmax.1 hs ht hAll
    exact (hmax.not_grows (last_store_poll_extension hpre hs hmax.1 hub hp hrel
      hState hSite hFinal (by rw [hPhase]; decide))).elim
  · push Not at hAll
    obtain ⟨k, hMissing⟩ := hAll
    let other := cta * L.block + k.val
    have hK := k.isLt
    have hLane : k.val < L.block := by rw [hpre.block]; omega
    have hOther : other < L.threads := PTX.NamedBar.cta_thread_lt (PTX.NamedBar.cta_lt hp.1) hLane
    have hCta : ctaOf L other = cta := by
      simp only [ctaOf, other, hpre.block]
      omega
    have hWg : wgOf L other = 0 := by
      simp only [wgOf, tidOf_eq hpre, other, hpre.block]
      omega
    have hMissing : Wg0LastStoreTrace.Missing L X other := by
      intro i tag
      rw [hCta]
      exact hMissing i tag
    have hPending : Frame.Pending L X other := by
      refine ⟨hOther, ?_, fun tag =>
        Wg0LastStoreTrace.not_exited_of_missing hpre hmax.1 hs ht hWg hMissing⟩
      rintro ⟨_, _, hCancel⟩
      obtain ⟨i, s, targets, _, hIssue, _⟩ := hmax.1.clc.canceled_has_issue hCancel
      exact GlobalWrites.no_clc (i := i) (s := s) (tg := targets) hmax.1 hIssue
    obtain ⟨q, hQ⟩ := hLive other hPending
    have hEarly := Wg0LastStoreTrace.early_of_missing hpre hmax.1 hs ht hOther hWg hMissing
      le_rfl hQ
    exact ⟨other, q, ⟨hp.1, hOther, hCta.symm⟩, hPending, hQ,
      early_last_store_priority hEarly hSite⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
