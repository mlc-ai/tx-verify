-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressIndexPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingRecordSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarIndexFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaIndexTerminal
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLaunch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader
import Lemmas.Clc.ClcExecution
import Lemmas.MBarrier.MBarrierInitOrder
import Lemmas.Protocol.UnitReachBlocker
import Lemmas.Protocol.UnitRingGate

public section

/-! # The older consumer release needed by a pending index-free poll -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.MbarRing PTX.MBarrier Protocol IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem free_poll_counts {g block : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hub : ¬ HasUb X)
    (hp : PendingState P L X g d) (hd : IndexWait d true block) :
    let n := PTX.Flow.okPolls (indexWaitObject L g true block) (X.tr g)
    n = block / 4 ∧ indexWaitParity true block = (n + 1) % 2 ∧
      block < Result.blocks P (ctaidY L g) := by
  have hg := hp.1.1
  have hTrace := (hs g hg).machine.produces (hX.thr g hg)
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp.1
  cases hd with
  | @producer q extra hSite =>
    obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.end_at hs hg hRun hp.2
    change Wg1Index.Inv P L g q at hi
    have h := IndexRingTrace.composed_free_counts hpre hTrace hp.2 hSite
    simp only [List.take_length] at h
    have hb := hi.block
    rw [hi.len0, hi.len1] at hb
    exact ⟨h.1, h.2, hb⟩

/-- A pending index-free poll needs an older slot release from an actual consumer.
The initially empty slot is always available for its first use. -/
theorem pending_index_free_short {g block : Nat} {d : Machine.ThreadD} {lane : Fin 32}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g d) (hrel : PTX.Step.Released L X g)
    (hd : IndexWait d true block) (hLane : IndexRing.TmaConsumer P L X (ctaOf L g) lane) :
    ∃ b : Fin 129, arrivals (indexWaitObject L g true block)
      (X.tr (consumerThread L (ctaOf L g) lane b)) < block / 4 := by
  let cta := ctaOf L g
  let slot := indexWaitSlot block
  let m := IndexRing.free L cta slot
  have hc := NamedBar.cta_lt hp.1.1
  let hSound := fun k hk => (hs k hk).machine
  let R := IndexRing.unit_ring_of_lane (slot := slot) hpre hmax.1 hc hSound ht hLane
  have hRole : ∀ s, d ≠ .prologue s := by
    cases hd
    intro s h
    cases h
  obtain ⟨_, hInit⟩ := MachineTracking.table_init_of_followed_tail hpre hmax.1 hs
    hp.1.1 hp.2 hRole (IndexRing.freeEntry slot)
  rw [IndexRing.free_entry_count, IndexRing.free_entry_loc] at hInit
  obtain ⟨_, r, hr, _, _, _, _⟩ := init_record_of_consistent hmax.1 hInit
  have hNe : X.objects m ≠ [] := by
    intro h
    have hmem := List.mem_of_getElem? hr
    change r ∈ X.objects m at hmem
    rw [h] at hmem
    exact List.not_mem_nil hmem
  obtain ⟨before, hState⟩ := Unit.final_of_init hmax.1 R.E.init R.E.noInval hNe
  have hPar : before.phase % 2 = indexWaitParity true block % 2 := by
    by_contra hDifferent
    exact hmax.not_grows (index_poll_extension hpre hs hmax.1 hub hp.1 hrel hp.2 hd
      hState hDifferent)
  obtain ⟨hCount, hParity, _⟩ := free_poll_counts hpre hmax.1 hs hub hp hd
  change PTX.Flow.okPolls m (X.tr g) = _ at hCount
  change indexWaitParity true block = (PTX.Flow.okPolls m (X.tr g) + 1) % 2 at hParity
  have hGateParity : before.phase % 2 = (PTX.Flow.okPolls m (X.tr g) + 1) % 2 := by
    rw [hParity, Nat.mod_mod] at hPar
    exact hPar
  have hProd : ∃ a, g = producerThread L cta a := by
    cases hd
    exact producer_of_warp hpre rfl (RingRoleGeometry.of_trace hmax.1 hp.1.1
      (hSound g hp.1.1) hp.2)
  have hPhase := ((R.emptyGate hmax.1).blocked hmax.1 hProd hState hGateParity).1
  change before.phase + 1 = PTX.Flow.okPolls m (X.tr g) at hPhase
  rw [hCount] at hPhase
  obtain ⟨b, hb⟩ := R.E.blocked hmax.1 hState
  have hClean := Safety.index_free_fault_free (slot := slot) hpre hmax.1 hc hSound ht
  have hLe := Unit.arrivals_le_unitRec hmax.1 hClean (consumerThread L cta lane b)
  exact ⟨b, lt_of_le_of_lt (hLe.trans hb) (by omega)⟩

private theorem softmax_epilogue_released {q : Wg0.D} (hq : q.site.inEpilogue = true) :
    Wg0IndexTrace.released q = q.block + 1 := by
  cases hs : q.site <;>
    simp [hs, Wg0.Site.inEpilogue, Wg0IndexTrace.released, Wg0IndexTrace.returned] at *

private theorem softmax_release_priority {g h block : Nat} {d : Machine.ThreadD} {q : Wg0.D}
    (hd : IndexWait d true block) (hPast : 4 ≤ block)
    (hCount : Wg0IndexTrace.released q ≤ block - 4)
    (hBlock : block < Result.blocks P (ctaidY L h)) (hi : Wg0.Inv P L h q) :
    priority P L h (.wg0 q) < priority P L g d := by
  have hNoEpi : q.site.inEpilogue = false := by
    cases he : q.site.inEpilogue
    · rfl
    · rw [softmax_epilogue_released he] at hCount
      have hEnd := hi.epilogueLast he
      change q.block + 1 = Result.blocks P (ctaidY L h) at hEnd
      omega
  have hs := hi.subLt
  have hSub : q.sub < 4 := by cases hQ : q.site <;> simp [hQ, Wg0.Site.elems] at hs <;> omega
  have hOrdinal : Bound.wg0Ordinal q.site ≤ 162 := by
    cases hQ : q.site <;> simp [Bound.wg0Ordinal] <;> omega
  cases hd with
  | @producer v extra hv =>
    cases hQ : q.site <;>
      simp only [hQ, priority, softmaxTime, indexTime, hv, blockTime, Bound.indexOrdinal,
        Bound.wg0Ordinal, Wg0.Site.inEpilogue, Wg0IndexTrace.released,
        Wg0IndexTrace.returned, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte] at *
    all_goals omega

private theorem gather_release_priority {g h block : Nat} {d : Machine.ThreadD} {q : Wg1Tma.D}
    (hd : IndexWait d true block) (hPast : 4 ≤ block)
    (hCount : TmaIndexTrace.released q ≤ block - 4)
    (hEnd : q.site ≠ .barrier ∧ q.site ≠ .exit) :
    priority P L h (.tma q) < priority P L g d := by
  have hOrdinal : Bound.tmaOrdinal q.site ≤ 99 := by
    cases hQ : q.site <;> simp [Bound.tmaOrdinal] <;> omega
  cases hd with
  | @producer v extra hv =>
    cases hQ : q.site <;>
      simp only [hQ, priority, gatherTime, indexTime, hv, blockTime, Bound.indexOrdinal,
        Bound.tmaOrdinal, TmaIndexTrace.released, TmaIndexTrace.begun,
        Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false, and_false, false_and] at *
    all_goals omega

private theorem reuse_start_priority {g h block : Nat} {d q : Machine.ThreadD}
    (hd : IndexWait d true block) (hStart : (∃ s, q = .prologue s) ∨ q = .head) :
    priority P L h q < priority P L g d := by
  rcases hStart with ⟨s, rfl⟩ | rfl
  all_goals cases hd with
    | @producer v extra hv =>
      simp only [priority, indexTime, hv, blockTime, Bound.indexOrdinal]
      omega

/-- A maximal execution blocked on index reuse has an earlier pending consumer of an old block. -/
theorem pending_index_free_earlier {g block : Nat} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g d) (hrel : PTX.Step.Released L X g)
    (hd : IndexWait d true block) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g d := by
  let cta := ctaOf L g
  let slot := indexWaitSlot block
  let m := IndexRing.free L cta slot
  let hSound := fun k hk => (hs k hk).machine
  obtain ⟨lane, hLeader⟩ := Wg1TmaLeader.cta_election_lane (cta := cta) hpre hmax.1
  have hLane : IndexRing.TmaConsumer P L X cta lane := by
    intro h i e q _ hc hd hState
    obtain ⟨hw, k, _, e', inst, he', heKind⟩ :=
      Wg1TmaLeader.body_elected hmax.1 hSound hState (by simp [hd])
    obtain ⟨tag, kind⟩ := e'
    have hElect : X.Elect (h, k) tag 4294967295 inst (PTX.laneOf L h) := by
      change kind = _ at heKind
      subst kind
      exact he'
    simpa only [PTX.laneOf, laneOf, tidOf_eq hpre, hpre.block] using hLeader hc hw hElect
  obtain ⟨b, hShort⟩ := pending_index_free_short hpre hmax hs ht hub hp hrel hd hLane
  let h := consumerThread L cta lane b
  obtain ⟨hh, hc⟩ := consumerThread_facts hpre (NamedBar.cta_lt hp.1.1) lane b
  change ctaOf L h = cta at hc
  have hRow : ctaidY L h = ctaidY L g := by
    change ctaOf L h = ctaOf L g at hc
    simp only [ctaidY, hc]
  have hBlock := (free_poll_counts hpre hmax.1 hs hub hp hd).2.2
  rw [← hRow] at hBlock
  have hPast : 4 ≤ block := by omega
  let trace := (hSound h hh).produces (hmax.1.thr h hh)
  have hClass {k : Nat} {q : Machine.ThreadD}
      (hq : Frame.stateAt (Machine.code P L) X h k = some (some q)) :
      (∃ s, q = .prologue s) ∨ q = .head ∨ (∃ w, q = .wg0 w) ∨ (∃ t, q = .tma t) ∨
        q = .done := by
    by_cases hb : b.val < 128
    · have hw : wgOf L h = 0 := by
        simp [h, consumerThread, hb, wgOf, tidOf_eq hpre, hpre.block]
        omega
      rcases Wg0.state_of_wg hw trace hq with hy | hy | hy
      · exact .inl hy
      · exact .inr (.inr (.inl hy))
      · exact .inr (.inr (.inr (.inr hy)))
    · have hw : warpOf L h = 5 := by
        have := lane.isLt
        simp [h, consumerThread, hb, warpOf, tidOf_eq hpre, hpre.block]
        omega
      have hLocal : PTX.laneOf L h = lane.val := by
        have := lane.isLt
        simp [h, consumerThread, hb, PTX.laneOf, hpre.block]
        omega
      have hKeep e (he : e ∈ X.tr h) inst leader
          (hk : e.kind = .elect 4294967295 inst leader) : leader = PTX.laneOf L h := by
        obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.mp he
        obtain ⟨tag, kind⟩ := e
        have hElect : X.Elect (h, i) tag 4294967295 inst leader := by
          change kind = _ at hk
          subst kind
          exact List.getElem?_eq_some_iff.mpr ⟨hi, hi'⟩
        exact (hLeader hc hw hElect).trans hLocal.symm
      rcases Wg1Tma.elected_state_of_warp hw trace hq hKeep with hy | hy | hy | hy
      · exact .inl hy
      · exact .inr (.inl hy)
      · exact .inr (.inr (.inr (.inl hy)))
      · exact .inr (.inr (.inr (.inr hy)))
  have hCount {k used : Nat}
      (hk : arrivals m ((X.tr h).take k) = (used + (3 - slot.val)) / 4) :
      used ≤ block - 4 := by
    have hle : arrivals m ((X.tr h).take k) ≤ arrivals m (X.tr h) :=
      (List.take_sublist k (X.tr h)).countP_le
    rw [hk] at hle
    change arrivals m (X.tr h) < block / 4 at hShort
    change (used + (3 - block % 4)) / 4 ≤ _ at hle
    omega
  have hSoft {k : Nat} {q : Wg0.D}
      (hq : Frame.stateAt (Machine.code P L) X h k = some (some (.wg0 q))) :
      Wg0IndexTrace.released q ≤ block - 4 := by
    apply hCount
    have hc' := Wg0IndexTrace.composed_release_count hpre slot trace hq
    rw [hc] at hc'
    exact hc'
  have hTma {k : Nat} {q : Wg1Tma.D}
      (hq : Frame.stateAt (Machine.code P L) X h k = some (some (.tma q))) :
      TmaIndexTrace.released q ≤ block - 4 := by
    apply hCount
    have hc' := TmaIndexTrace.composed_release_count hpre slot trace hq
    rw [hc] at hc'
    exact hc'
  have hTmaLive {k : Nat} {q : Wg1Tma.D}
      (hq : Frame.stateAt (Machine.code P L) X h k = some (some (.tma q))) :
      q.site ≠ .barrier ∧ q.site ≠ .exit := by
    have he (hEnd : q.site = .barrier ∨ q.site = .exit) : False := by
      have hTotal : q.block = Result.blocks P (ctaidY L h) :=
        TmaIndexTrace.terminal_block trace hq hEnd
      have hr := hTma hq
      rcases hEnd with hu | hu <;> simp [hu, TmaIndexTrace.released, TmaIndexTrace.begun] at hr
      all_goals omega
    exact ⟨fun h => he (.inl h), fun h => he (.inr h)⟩
  have hNoArrival {i tag : Nat} (he : X.get (h, i) = some ⟨tag, .bar 12 none .sync⟩) :
      False := by
    obtain ⟨q, hq, hSite, _, _⟩ := ScoreClosingGate.closing_at hpre hmax.1 hs ht he
    rcases hClass hq with ⟨s, rfl⟩ | rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩ | rfl
    · exact hSite
    · exact hSite
    · change u.site = .everyone at hSite
      obtain ⟨_, _, ⟨_, hi⟩, _⟩ := RingEvents.fired_of_trace hmax.1 (hSound h hh) he hq
      change Wg0.Inv P L h u at hi
      have hEnd := hi.epilogueLast (by rw [hSite]; rfl)
      have hRelease := hSoft hq
      rw [softmax_epilogue_released (by rw [hSite]; rfl), hEnd] at hRelease
      change _ ≤ block - 4 at hRelease
      have hEq : Wg0.blocksOf P L h = Result.blocks P (ctaidY L h) := rfl
      omega
    · exact (hTmaLive hq).1 hSite
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
  rcases hClass hq with ⟨s, rfl⟩ | rfl | ⟨u, rfl⟩ | ⟨u, rfl⟩ | rfl
  · exact reuse_start_priority hd (.inl ⟨s, rfl⟩)
  · exact reuse_start_priority hd (.inr rfl)
  · obtain ⟨_, hRun⟩ := Frame.run_some hmax.1 hub hPending
    obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.end_at hs hh hRun hq
    exact softmax_release_priority hd hPast (hSoft hq) hBlock hi
  · exact gather_release_priority hd hPast (hTma hq) (hTmaLive hq)
  · obtain ⟨_, _, _, he⟩ := ClosingOrder.arrival_before_state hpre hmax.1
      (hSound h hh) hh hq trivial
    exact (hNoArrival he).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
