-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressIndexPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarIndexFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.IndexRingTerminal
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexLaunch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0IndexTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaIndexTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Lemmas.MBarrier.MBarrierInitOrder
import Lemmas.Protocol.UnitReachBlocker
import Lemmas.Protocol.UnitRingGate
import Lemmas.Clc.ClcExecution

public section

/-! # An index-ready wait descends to an earlier producer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.MbarRing PTX.MBarrier Protocol IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem ready_poll_counts {g block : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hub : ¬ HasUb X)
    (hp : PendingState P L X g d) (hd : IndexWait d false block) :
    PTX.Flow.okPolls (indexWaitObject L g false block) (X.tr g) = block / 4 ∧
      block < Result.blocks P (ctaidY L g) := by
  have hg := hp.1.1
  have hTrace := (hs g hg).machine.produces (hX.thr g hg)
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp.1
  cases hd with
  | @softmax q hSite =>
    obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.end_at hs hg hRun hp.2
    change Wg0.Inv P L g q at hi
    have h := Wg0IndexTrace.composed_ready_counts hpre hTrace hp.2 hSite
    rw [List.take_length] at h
    exact ⟨h, hi.blockLt⟩
  | @gather q hSite =>
    obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.end_at hs hg hRun hp.2
    change Wg1Tma.Inv P L g q at hi
    have h := TmaIndexTrace.composed_ready_counts hpre hTrace hp.2 hSite
    rw [List.take_length] at h
    refine ⟨h, ?_⟩
    rcases hi.block_le with h | h | h
    · rw [hSite] at h
      cases h
    · rw [hSite] at h
      cases h
    · rw [hi.len0, hi.len1] at h
      exact h

private theorem ready_consumer {g block : Nat} {d : Machine.ThreadD} {lane : Fin 32}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hp : PendingState P L X g d)
    (hd : IndexWait d false block)
    (hLeader : ∀ t i (v : Wg1Tma.D), ctaOf L t = ctaOf L g →
      Frame.stateAt (Machine.code P L) X t i = some (some (.tma v)) →
      v.site ≠ .elect → t = ctaOf L g * L.block + 160 + lane.val) :
    ∃ b, g = consumerThread L (ctaOf L g) lane b := by
  cases hd
  case softmax q hSite =>
    have hWg : wgOf L g = 0 := RingRoleGeometry.of_trace hX hp.1.1 (hs g hp.1.1).machine hp.2
    obtain ⟨b, _, h⟩ := consumer_of_wg0 hpre rfl hWg lane
    exact ⟨b, h⟩
  case gather q hSite =>
    refine ⟨⟨128, by decide⟩, ?_⟩
    simpa [consumerThread, Nat.add_assoc] using hLeader g _ q rfl hp.2 (by simp [hSite])

private theorem unit_rec_eq (g : Nat) : Unit.unitRec g = Unit.unitsOf g := by
  funext r
  cases ha : r.action <;> cases hf : r.fault <;>
    simp [Unit.unitRec, Unit.unitsOf, countedArrive, ha, hf]

/-- If the ready poll is pending in a maximal execution, some index lane has not yet
published this block. The count also covers the first use of a slot. -/
theorem pending_index_ready_short {g block : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g d) (hrel : PTX.Step.Released L X g)
    (hd : IndexWait d false block) :
    ∃ a : Fin 32, arrivals (indexWaitObject L g false block)
      (X.tr (producerThread L (ctaOf L g) a)) ≤ block / 4 := by
  let cta := ctaOf L g
  let slot := indexWaitSlot block
  let m := IndexRing.ready L cta slot
  have hc := NamedBar.cta_lt hp.1.1
  let hSound := fun k hk => (hs k hk).machine
  obtain ⟨lane, hLeader⟩ := Wg1TmaLeader.cta_issuer (cta := cta) hpre hmax.1 hSound
  have hLane : IndexRing.TmaConsumer P L X cta lane := by
    intro g i e d _ hc hd hst
    rw [hLeader g i d hc hst (by simp [hd])]
    unfold laneOf
    rw [tidOf_eq hpre, hpre.block]
    have := lane.isLt
    omega
  let R := IndexRing.unit_ring_of_lane (slot := slot) hpre hmax.1 hc hSound ht hLane
  have hRole : ∀ s, d ≠ .prologue s := by cases hd <;> intro s h <;> cases h
  obtain ⟨_, hInit⟩ := MachineTracking.table_init_of_followed_tail hpre hmax.1 hs
    hp.1.1 hp.2 hRole (IndexRing.readyEntry slot)
  rw [IndexRing.ready_entry_count, IndexRing.ready_entry_loc] at hInit
  obtain ⟨_, r, hr, _, _, _, _⟩ := init_record_of_consistent hmax.1 hInit
  have hNe : X.objects m ≠ [] := by
    intro h
    have hmem := List.mem_of_getElem? hr
    change r ∈ X.objects m at hmem
    rw [h] at hmem
    exact List.not_mem_nil hmem
  obtain ⟨before, hState⟩ := Unit.final_of_init hmax.1 R.F.init R.F.noInval hNe
  have hPar : before.phase % 2 = indexWaitParity false block % 2 := by
    by_contra hDifferent
    exact hmax.not_grows (index_poll_extension hpre hs hmax.1 hub hp.1 hrel hp.2 hd
      hState hDifferent)
  obtain ⟨hCount, _⟩ := ready_poll_counts hpre hmax.1 hs hub hp hd
  change PTX.Flow.okPolls m (X.tr g) = _ at hCount
  have hGateParity : before.phase % 2 = (PTX.Flow.okPolls m (X.tr g) + 0) % 2 := by
    rw [hCount]
    simpa [indexWaitParity] using hPar
  obtain ⟨hPhase, a, hShort⟩ := (R.fullGate hmax.1).blocked hmax.1
    (ready_consumer hpre hmax.1 hs hp hd hLeader) hState hGateParity
  have hClean := Safety.index_ready_fault_free (slot := slot) hpre hmax.1 hc hSound ht
  have hLe := Unit.arrivals_le_unitRec hmax.1 hClean (producerThread L cta a)
  change arrivals m (X.tr (producerThread L cta a)) ≤
    (X.objects m).countP (Unit.unitRec (producerThread L cta a)) at hLe
  rw [unit_rec_eq] at hLe
  change (X.objects m).countP (Unit.unitsOf (producerThread L cta a)) = before.phase at hShort
  change before.phase + 0 = PTX.Flow.okPolls m (X.tr g) at hPhase
  rw [hCount, Nat.add_zero] at hPhase
  rw [hShort, hPhase] at hLe
  exact ⟨a, hLe⟩

private theorem ready_priority {g h block : Nat} {d : Machine.ThreadD} {q : Wg1Index.D}
    (hd : IndexWait d false block) (hq : q.block ≤ block) (hb : q.site ≠ .barrier) :
    priority P L h (.index q) < priority P L g d := by
  have ho : Bound.indexOrdinal q.site ≤ 15 := by
    cases hs : q.site
    case pair ext fst hi => cases fst <;> cases hi <;> simp [Bound.indexOrdinal]
    case coord ext hi => cases hi <;> simp [Bound.indexOrdinal]
    all_goals simp [Bound.indexOrdinal]
  cases hd <;> rename_i w hSite <;> cases hs : q.site <;>
    simp only [priority, softmaxTime, gatherTime, indexTime, hSite, hs, blockTime,
      Bound.indexOrdinal, Bound.tmaOrdinal, Bound.wg0Ordinal] at *
  all_goals first | contradiction | omega

private theorem ready_start_priority {g h block : Nat} {d q : Machine.ThreadD}
    (hd : IndexWait d false block) (hq : (∃ s, q = .prologue s) ∨ q = .head) :
    priority P L h q < priority P L g d := by
  rcases hq with ⟨s, rfl⟩ | rfl <;> cases hd <;> rename_i w hSite <;>
    simp only [priority, softmaxTime, gatherTime, hSite, Bound.wg0Ordinal,
      Bound.tmaOrdinal, blockTime] <;> omega

/-- A maximal execution with a pending index-ready poll has a strictly earlier pending
producer of the same CTA. This covers both the softmax and tensor gather consumers. -/
theorem pending_index_ready_earlier {g block : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g d) (hrel : PTX.Step.Released L X g)
    (hd : IndexWait d false block) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
  obtain ⟨a, hShort⟩ := pending_index_ready_short hpre hmax hs ht hub hp hrel hd
  let cta := ctaOf L g
  let slot := indexWaitSlot block
  let h := producerThread L cta a
  let m := IndexRing.ready L cta slot
  obtain ⟨hh, hc, hw⟩ := producerThread_facts hpre (NamedBar.cta_lt hp.1.1) a
  have hRow : ctaidY L h = ctaidY L g := by
    change ctaOf L h = ctaOf L g at hc
    simp only [ctaidY, hc]
  have hBlock := (ready_poll_counts hpre hmax.1 hs hub hp hd).2
  rw [← hRow] at hBlock
  let hTrace := (hs h hh).machine.produces (hmax.1.thr h hh)
  have hIdxCount {q : Wg1Index.D} {i : Nat}
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.index q))) :
      (q.block + (if q.site = .barrier then 1 else 0) + (3 - slot.val)) / 4 ≤ block / 4 := by
    have hCount := IndexRingTrace.composed_publications hpre slot hTrace hq
    change ctaOf L h = cta at hc
    have hEq : (⟨.shared, ctaOf L h, L.sharedBase + Wg1Index.readyOff slot.val⟩ : Loc) = m := by
      rw [hc]
      rfl
    rw [hEq] at hCount
    change arrivals m (X.tr h) ≤ _ at hShort
    rw [← hCount]
    exact ((List.take_sublist i (X.tr h)).countP_le (p := arrivesOn m)).trans hShort
  have hNoClose {q : Wg1Index.D} {i : Nat}
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.index q))) :
      q.site ≠ .barrier := by
    intro hb
    have hDone := IndexRingTrace.terminal_block hTrace hq hb
    have hTotal : q.block + 1 = Result.blocks P (ctaidY L h) := hDone
    have hCount := hIdxCount hq
    rw [ite_eq_left hb] at hCount
    change (q.block + 1 + (3 - block % 4)) / 4 ≤ block / 4 at hCount
    omega
  have hNoArrival {i tag : Nat} (he : X.get (h, i) = some ⟨tag, .bar 12 none .sync⟩) :
      False := by
    obtain ⟨q, hq, hSite, _, _⟩ := ScoreClosingGate.closing_at hpre hmax.1 hs ht he
    rcases Wg1Index.state_of_warp hw hTrace hq with ⟨s, rfl⟩ | rfl | ⟨u, rfl⟩ | rfl
    · exact hSite
    · exact hSite
    · exact hNoClose hq hSite
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
  rcases Wg1Index.state_of_warp hw hTrace hq with ⟨s, rfl⟩ | rfl | ⟨u, rfl⟩ | rfl
  · exact ready_start_priority hd (.inl ⟨s, rfl⟩)
  · exact ready_start_priority hd (.inr rfl)
  · have hNo := hNoClose hq
    have hCount := hIdxCount hq
    rw [ite_eq_right hNo, Nat.add_zero] at hCount
    change (u.block + (3 - block % 4)) / 4 ≤ block / 4 at hCount
    exact ready_priority hd (by omega) hNo
  · obtain ⟨_, _, _, he⟩ :=
      ClosingOrder.arrival_before_state hpre hmax.1 (hs h hh).machine hh hq trivial
    exact (hNoArrival he).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
