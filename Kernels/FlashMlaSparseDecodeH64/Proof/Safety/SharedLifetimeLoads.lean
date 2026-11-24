-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetimeQuery
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingHandoffs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorLoadSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaGatherCounts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReuseHistory
import Lemmas.Protocol.PollIndex
import Lemmas.Protocol.NamedBarSources

public section

/-! # Each issued raw gather is observed by a dequantizer before CTA exit -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime

open PTX PTX.Flow PTX.AsyncCopy PTX.MbarRing Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem raw_gather_finished (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {g i address : Nat} {sp : TensorCopy.Spec} {d : Wg1Tma.D} {k : Fin 16}
    (hi : X.TensorIssue (g, i) address sp)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))) (hk : d.site = .issue k)
    (hx : CtaExited L X (ctaOf L g)) :
    SharedFinished L kernel Assumptions.all X (.async (g, i) (.notify .load)) (ctaOf L g) := by
  let c := ctaOf L g
  let slot := rawSlot d.block
  let m := RawRing.ready L c slot
  let lane : Fin 128 := 0
  let w := RawRing.consumer L c lane
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hc : c < L.grid := NamedBar.cta_lt hg
  have hSpan := Nat.mul_le_mul_right L.block (show c + 1 ≤ L.grid by omega)
  have hW : w < L.threads := by
    change c * L.block + 256 + 0 < L.grid * L.block
    rw [Nat.add_mul, Nat.one_mul] at hSpan
    have hSize := hpre.block
    omega
  have hCta : ctaOf L w = c := by
    simp [w, lane, RawRing.consumer, ctaOf, hpre.block, Nat.mul_comm c 384, Nat.mul_add_div]
  have hWg : wgOf L w = 2 := by
    simp [w, lane, RawRing.consumer, wgOf, tidOf_eq hpre, hpre.block, Nat.mul_comm c 384]
  obtain ⟨xt, hLast⟩ := hx w hW hCta
  rw [List.getLast?_eq_getElem?] at hLast
  have hExit : X.get (w, (X.tr w).length - 1) = some ⟨xt, .exit⟩ := hLast
  let hSound := fun t ht' => (hs t ht').machine
  obtain ⟨j, f, p, _, hf, hState, hSite, hTotal⟩ :=
    Wg2ReuseHistory.last_free_before_exit hpre hX hs ht hWg hExit
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hi.choose_spec hd
  have htma : Wg1Tma.Inv P L g d := hInv
  have hBound := htma.block_le.resolve_left (by simp [hk])
  have hB : d.block < totalBlocks (P.topkLen (Wg1Tma.eOf L g))
      (P.extraTopkLen (Wg1Tma.eOf L g)) := by
    have h := hBound.resolve_left (by simp [hk])
    simpa only [htma.len0, htma.len1] using h
  have hBatch : Wg1Tma.eOf L g = Wg2.eOf L w := by
    simp only [Wg1Tma.eOf, Wg2.eOf, ctaidY, hCta, c]
  rw [hBatch, ← hTotal] at hB
  have hPollCount := Wg2RawTrace.composed_raw_polls_through_free hpre slot
    ((hs w hW).machine.produces (hX.thr w hW)) hState hSite
  rw [hCta] at hPollCount
  change okPolls m ((X.tr w).take j) = _ at hPollCount
  have hEnough : d.block / 2 + 1 ≤ okPolls m ((X.tr w).take j) := by
    rw [hPollCount]
    change d.block / 2 + 1 ≤ (p.block + 1 + (1 - d.block % 2)) / 2
    omega
  obtain ⟨poll, t, parity, acq, sc, _, hPoll, hPollOrd⟩ :=
    MbarRing.Poll.exists_nth hEnough
  obtain ⟨leader, hLeader⟩ := Wg1TmaLeader.cta_issuer (cta := c) hpre hX hSound
  have hG := hLeader g i d rfl hd (by simp [hk])
  have hIssuer : RawRing.Issuer P L X c g := by
    intro h j d' hCta' hSt hRole
    have hNot : d'.site ≠ .elect := by
      rcases hRole with h | ⟨k', h⟩ <;> simp [h]
    exact (hLeader h j d' hCta' hSt hNot).trans hG.symm
  have hObs := RawRing.gather_acquired k hpre hX hSound ht hIssuer hPoll rfl
  change AsyncObserved X (g, nthEv X (issuesTo m) g
      (16 * okPolls m ((X.tr w).take poll) + k.val)) (.notify .load) (w, poll) true .cta at hObs
  rw [hPollOrd] at hObs
  have hMbar : sp.mbar = m := by
    obtain ⟨o, hf⟩ := ((hs g hg).machine.produces (hX.thr g hg)).fired_at hi.choose_spec hd
    exact (TmaGatherCounts.gather_event_fields hpre hk hf rfl).2.2.1
  have hPred : issuesTo m ⟨hi.choose, .tensorIssue address sp⟩ = true := by
    simp [issuesTo, hMbar]
  have hNth := nthEv_eq hi.choose_spec hPred
  have hCount := TmaGatherCounts.composed_issue_count hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hd hk
  change ((X.tr g).take i).countP (issuesTo m) = _ at hCount
  rw [hCount] at hNth
  rw [hNth] at hObs
  have hDone := load_notify_finished hX hObs (hCta ▸ hx)
  simpa only [hCta, c] using hDone

/-- Every query or gather notification has completed before an exit of its CTA. -/
theorem loads_notified (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    LoadNotified L X := by
  rintro ⟨g, i⟩ address sp hi hx
  rcases TensorLoadSources.issue_kind hpre hX hs ht hi with
    ⟨tile, rfl, rfl⟩ | ⟨d, k, hd, hk⟩
  · exact query_load_finished hpre hX hs ht hi hx
  · exact raw_gather_finished hpre hX hs ht hi hd hk hx

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime
