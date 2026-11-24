-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.RawReadyPhase
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaGatherCounts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaIndexTerminal
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLaunch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader
import Lemmas.Clc.ClcExecution

public section

/-! # A raw-ready wait descends to the elected gather producer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.MbarRing Protocol RawRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem gather_ready_priority {g h : Nat} {d : Wg2.D} {q : Wg1Tma.D}
    (hd : d.site = .rawReady) (hEnd : q.site ≠ .barrier ∧ q.site ≠ .exit)
    (hq : TmaRawTrace.begun q.site = true → q.block ≤ d.block) :
    priority P L h (.tma q) < priority P L g (.wg2 d) := by
  have hOrdinal : Bound.tmaOrdinal q.site ≤ 99 := by
    cases hQ : q.site <;> simp [Bound.tmaOrdinal] <;> omega
  cases hQ : q.site
  all_goals
    simp [hQ, TmaRawTrace.begun] at hEnd hq
  all_goals
    simp only [hQ, priority, quantTime, gatherTime, hd, blockTime,
      Bound.wg2Ordinal, Bound.tmaOrdinal]
    omega

/-- A maximal execution blocked on raw readiness has an earlier pending gather producer. -/
theorem pending_raw_ready_earlier {g : Nat} {d : Wg2.D}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.wg2 d))
    (hrel : PTX.Step.Released L X g) (hd : d.site = .rawReady) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.wg2 d) := by
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := ready L cta slot
  let hSound := fun k hk => (hs k hk).machine
  obtain ⟨lane, hSelected⟩ := Wg1TmaLeader.cta_election_lane (cta := cta) hpre hmax.1
  let h := cta * L.block + 160 + lane.val
  have hh : h < L.threads := by
    have hLane : 160 + lane.val < L.block := by
      rw [hpre.block]
      have := lane.isLt
      omega
    simpa only [h, Nat.add_assoc] using
      NamedBar.cta_thread_lt (c := cta) (NamedBar.cta_lt hp.1.1) hLane
  have hCta : ctaOf L h = cta := by
    have := lane.isLt
    simp only [ctaOf, h, hpre.block]
    omega
  have hWarp : warpOf L h = 5 := by
    have := lane.isLt
    simp only [warpOf, tidOf_eq hpre, h, hpre.block]
    omega
  have hLocal : PTX.laneOf L h = lane.val := by
    have := lane.isLt
    simp only [PTX.laneOf, h, hpre.block]
    omega
  have hKeep e (he : e ∈ X.tr h) inst leader
      (hk : e.kind = .elect 4294967295 inst leader) : leader = PTX.laneOf L h := by
    obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.mp he
    obtain ⟨tag, kind⟩ := e
    have hElect : X.Elect (h, i) tag 4294967295 inst leader := by
      change kind = _ at hk
      subst kind
      exact List.getElem?_eq_some_iff.mpr ⟨hi, hi'⟩
    exact (hSelected hCta hWarp hElect).trans hLocal.symm
  have hIssuer : RawRing.Issuer P L X cta h := by
    intro k i q hc hst hsite
    have hne : q.site ≠ .elect := by
      rcases hsite with hq | ⟨_, hq⟩ <;> simp [hq]
    obtain ⟨hw, j, _, e, inst, he, hk⟩ := Wg1TmaLeader.body_elected hmax.1 hSound hst hne
    obtain ⟨tag, kind⟩ := e
    have hElect : X.Elect (k, j) tag 4294967295 inst (PTX.laneOf L k) := by
      change kind = _ at hk
      subst kind
      exact he
    have hLane := hSelected hc hw hElect
    simp only [h, PTX.laneOf, hpre.block, ctaOf, warpOf, tidOf_eq hpre] at hLane hw hc ⊢
    omega
  have hRow : ctaidY L h = ctaidY L g := by simp only [ctaidY, hCta, cta]
  obtain ⟨_, hRun⟩ := Frame.run_some hmax.1 hub hp.1
  obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.end_at hs hp.1.1 hRun hp.2
  change Wg2.Inv P L g d at hi
  have hBlock := hi.block
  rw [hi.len0, hi.len1] at hBlock
  change d.block < Result.blocks P (ctaidY L g) at hBlock
  rw [← hRow] at hBlock
  let trace := (hSound h hh).produces (hmax.1.thr h hh)
  have hNoLater {i : Nat} {q : Wg1Tma.D}
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.tma q)))
      (hBegun : TmaRawTrace.begun q.site = true) (hLate : d.block < q.block) : False := by
    have hb : TmaGatherCounts.blockStarted q.site = true := hBegun
    have hPub := TmaRawTrace.composed_prior_publications hpre slot trace hq hBegun
    have hIssued := TmaGatherCounts.composed_prior_issues hpre slot trace hq hb
    rw [hCta] at hPub hIssued
    change _ ≤ arrivals m ((X.tr h).take i) at hPub
    change _ ≤ ((X.tr h).take i).countP (issuesTo m) at hIssued
    have hGen : d.block / 2 + 1 ≤ (q.block + (1 - slot.val)) / 2 := by
      change d.block / 2 + 1 ≤ (q.block + (1 - d.block % 2)) / 2
      omega
    have hMore : d.block / 2 + 1 ≤ arrivals m (X.tr h) :=
      hGen.trans (hPub.trans (List.take_sublist i (X.tr h)).countP_le)
    have hGather : 16 * (d.block / 2 + 1) ≤ (X.tr h).countP (issuesTo m) :=
      (Nat.mul_le_mul_left 16 hGen).trans (hIssued.trans (List.take_sublist i (X.tr h)).countP_le)
    exact no_pending_raw_ready_of_published hpre hmax hs ht hub hp hrel hd hIssuer hMore hGather
  have hNoEnd {i : Nat} {q : Wg1Tma.D}
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.tma q)))
      (hEnd : q.site = .barrier ∨ q.site = .exit) : False := by
    have hTotal : q.block = Result.blocks P (ctaidY L h) :=
      TmaIndexTrace.terminal_block trace hq hEnd
    exact hNoLater hq (by rcases hEnd with hq' | hq' <;> rw [hq'] <;> rfl) (by omega)
  have hNoArrival {i tag : Nat} (he : X.get (h, i) = some ⟨tag, .bar 12 none .sync⟩) :
      False := by
    obtain ⟨q, hq, hSite, _, _⟩ := ScoreClosingGate.closing_at hpre hmax.1 hs ht he
    rcases Wg1Tma.elected_state_of_warp hWarp trace hq hKeep with
        ⟨s, rfl⟩ | rfl | ⟨u, rfl⟩ | rfl
    · exact hSite
    · exact hSite
    · exact hNoEnd hq (.inl hSite)
    · exact hSite
  have hPending : Frame.Pending L X h := by
    refine ⟨hh, ?_, ?_⟩
    · rintro ⟨_, _, hCancel⟩
      obtain ⟨i, sp, targets, _, hIssue, _⟩ := hmax.1.clc.canceled_has_issue hCancel
      exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hmax.1 hIssue
    · intro tag hLast
      rw [List.getLast?_eq_getElem?] at hLast
      obtain ⟨_, _, _, he⟩ := ClosingOrder.arrival_before_exit hpre hmax.1 hs ht hLast
      exact hNoArrival he
  obtain ⟨q, hq⟩ := pending_followed hpre hmax.1 hs ht hPending
  refine ⟨h, q, ⟨hPending, hq⟩, ?_⟩
  rcases Wg1Tma.elected_state_of_warp hWarp trace hq hKeep with
      ⟨s, rfl⟩ | rfl | ⟨u, rfl⟩ | rfl
  · simp only [priority, quantTime, hd, blockTime, Bound.wg2Ordinal]
    omega
  · simp only [priority, quantTime, hd, blockTime, Bound.wg2Ordinal]
    omega
  · refine gather_ready_priority hd ⟨fun hb => hNoEnd hq (.inl hb),
      fun he => hNoEnd hq (.inr he)⟩ fun hb => ?_
    by_contra! hLate
    exact hNoLater hq hb hLate
  · obtain ⟨_, _, _, he⟩ := ClosingOrder.arrival_before_state hpre hmax.1
      (hSound h hh) hh hq trivial
    exact (hNoArrival he).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
