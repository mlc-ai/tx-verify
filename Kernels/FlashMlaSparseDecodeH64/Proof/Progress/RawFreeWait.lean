-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressRawPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.LiveState
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarRawFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitPublication
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReuseHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Lemmas.MBarrier.MBarrierInitOrder
import Lemmas.Protocol.UnitReachBlocker
import Lemmas.Clc.ClcExecution

public section

/-! # A raw reuse wait descends to an earlier dequantization consumer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.MbarRing PTX.MBarrier Protocol RawRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxRecDepth 4096

private theorem reuse_count_and_block {g : Nat} {d : Wg1Tma.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hub : ¬ HasUb X)
    (hp : PendingState P L X g (.tma d)) (hd : d.site = .waitFree) :
    PTX.Flow.okPolls (free L (ctaOf L g) (rawSlot d.block)) (X.tr g) = d.block / 2 ∧
      d.block < Result.blocks P (ctaidY L g) := by
  have hg := hp.1.1
  have trace := (hs g hg).machine.produces (hX.thr g hg)
  have hCount := TmaRawTrace.composed_reuse_count hpre trace hp.2 hd
  rw [List.take_length] at hCount
  obtain ⟨_, hRun⟩ := Frame.run_some hX hub hp.1
  obtain ⟨_, _, _, _, hi, _, _⟩ := Frame.end_at hs hg hRun hp.2
  change Wg1Tma.Inv P L g d at hi
  refine ⟨hCount, ?_⟩
  have hb := hi.block_le
  rw [hi.len0, hi.len1] at hb
  change d.block < totalBlocks (P.topkLen (Wg1Tma.eOf L g)) (P.extraTopkLen (Wg1Tma.eOf L g))
  simpa [hd] using hb

private theorem first_reuse_phase {g cta : Nat} {slot : Fin 2} {before : State}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hIssuer : RawRing.Issuer P L X cta g)
    (hState : stateBefore (X.objects (free L cta slot)) (X.objects (free L cta slot)).length =
      some before) (hZero : PTX.Flow.okPolls (free L cta slot) (X.tr g) = 0) :
    before.phase = 0 := by
  let R := items (slot := slot) g hpre hX hs ht hIssuer
  let O := free_obj hpre hX hs ht (cta := cta) (slot := slot)
  have hNoItem (x : Fin 128 × Nat) (hx : x ∈ Unit.S X (free L cta slot) (consumer L cta)) :
      False := by
    have hGuard := guard_empty_item hpre hX hs ht hx (j := x.2) le_rfl
    have hPres := Round.Slot.present_of_guard hGuard
    obtain ⟨hy, _⟩ := R.observes_full (b := x.1) (j := x.2) hX.depAcyclic hPres 0
    have hReuse := guard_full_item hpre hX hs ht hy (n := 0) (Nat.zero_le _)
    have hFirst := Poll.nth_present.mp (Round.Slot.present_of_guard hReuse)
    change 0 < PTX.Flow.okPolls (free L cta slot) (X.tr g) at hFirst
    omega
  have hNoArrival {k c tx : Nat} {r : Record AsyncCopy.Ref}
      (hr : (X.objects (free L cta slot))[k]? = some r)
      (hOk : r.fault = none) (ha : r.action = .arrive c tx) : False := by
    obtain ⟨x, hx, _⟩ := O.rec_S hr hOk ha
    exact hNoItem x hx
  by_contra hn
  obtain ⟨_, _, _, _, hr, hOk, ha, _, _, _⟩ := O.phase_all hX le_rfl hState
    (show 0 < before.phase by omega)
    (fun _ _ _ _ _ _ _ hr hOk ha _ _ => (hNoArrival hr hOk ha).elim) 0
  exact hNoArrival hr hOk ha

/-- A pending raw-free poll needs a release of its previous slot generation. -/
theorem pending_raw_free_short {g : Nat} {d : Wg1Tma.D}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.tma d))
    (hrel : PTX.Step.Released L X g) (hd : d.site = .waitFree) :
    ∃ lane : Fin 128, arrivals (free L (ctaOf L g) (rawSlot d.block))
      (X.tr (consumer L (ctaOf L g) lane)) < d.block / 2 := by
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := free L cta slot
  let hSound := fun k hk => (hs k hk).machine
  obtain ⟨lane, hLeader⟩ := Wg1TmaLeader.cta_issuer (cta := cta) hpre hmax.1 hSound
  have hThis := hLeader g _ d rfl hp.2 (by simp [hd])
  have hIssuer : RawRing.Issuer P L X cta g := by
    intro h i q hc hState hSite
    rw [hThis]
    apply hLeader h i q hc hState
    rcases hSite with hq | ⟨_, hq⟩ <;> simp [hq]
  let R := items (slot := slot) g hpre hmax.1 hSound ht hIssuer
  let O := free_obj hpre hmax.1 hSound ht (cta := cta) (slot := slot)
  have hReach : Unit.Reach L kernel Assumptions.all X m 128 (consumer L cta) 1 g := by
    intro x hx j hj
    exact (R.reach hmax.1.depAcyclic).2 0 x hx (j + 1) (by omega) (by omega)
  obtain ⟨_, hInit⟩ := MachineTracking.table_init_of_followed_tail hpre hmax.1 hs
    hp.1.1 hp.2 (by intro s h; cases h) (freeEntry slot)
  obtain ⟨hl, hc⟩ := free_entry L cta slot
  rw [hl, hc] at hInit
  obtain ⟨_, _, hr, _, _, _, _⟩ := init_record_of_consistent hmax.1 hInit
  have hNe : X.objects m ≠ [] := by
    intro h
    have hmem := List.mem_of_getElem? hr
    change _ ∈ X.objects m at hmem
    rw [h] at hmem
    exact List.not_mem_nil hmem
  obtain ⟨before, hState⟩ := Unit.final_of_init hmax.1 O.init O.noInval hNe
  have hPar : before.phase % 2 = (1 - d.block / 2 % 2) % 2 := by
    by_contra hDifferent
    exact hmax.not_grows (raw_free_poll_extension hpre hs hmax.1 hub hp.1 hrel hp.2 hd
      hState hDifferent)
  obtain ⟨hCount, _⟩ := reuse_count_and_block hpre hmax.1 hs hub hp hd
  change PTX.Flow.okPolls m (X.tr g) = _ at hCount
  have hOlder : 1 ≤ PTX.Flow.okPolls m (X.tr g) := by
    by_contra! hn
    have hZero : PTX.Flow.okPolls m (X.tr g) = 0 := by omega
    have hPhase := first_reuse_phase hpre hmax.1 hSound ht hIssuer hState hZero
    omega
  have hGateParity : before.phase % 2 = (PTX.Flow.okPolls m (X.tr g) + 1) % 2 := by omega
  have hClean := Safety.raw_free_fault_free (cta := cta) (slot := slot) hpre hmax.1 hSound ht
  obtain ⟨hPhase, b, hb⟩ := O.reach_short hmax.1 hReach hClean hState hOlder hGateParity
  change before.phase + 1 = PTX.Flow.okPolls m (X.tr g) at hPhase
  rw [hCount] at hPhase
  exact ⟨b, lt_of_le_of_lt hb (by omega)⟩

private theorem earlier_dequant_priority {g h : Nat} {d : Wg1Tma.D} {q : Wg2.D}
    (hd : d.site = .waitFree) (hPast : 2 ≤ d.block)
    (hu : Wg2RawTrace.released q ≤ d.block - 2) (hClosing : q.site ≠ .barrier) :
    priority P L h (.wg2 q) < priority P L g (.tma d) := by
  have hOrdinal : Bound.wg2Ordinal q.site ≤ 99 := by
    cases hq : q.site <;> simp [Bound.wg2Ordinal]
    all_goals first | omega | (split <;> omega)
  cases hq : q.site <;>
    simp only [hq, hd, priority, gatherTime, quantTime, blockTime, Bound.tmaOrdinal,
      Wg2RawTrace.released, ne_eq, not_true_eq_false] at *
  all_goals omega

/-- Any maximal trace waiting to reuse a raw slot has a dequantization lane of lower priority. -/
theorem pending_raw_free_earlier {g : Nat} {d : Wg1Tma.D}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hub : ¬ HasUb X) (hp : PendingState P L X g (.tma d))
    (hrel : PTX.Step.Released L X g) (hd : d.site = .waitFree) :
    ∃ h q, PendingState P L X h q ∧ priority P L h q < priority P L g (.tma d) := by
  obtain ⟨lane, hShort⟩ := pending_raw_free_short hpre hmax hs ht hub hp hrel hd
  let cta := ctaOf L g
  let slot := rawSlot d.block
  let m := free L cta slot
  let h := consumer L cta lane
  have hLane : 256 + lane.val < L.block := by
    obtain ⟨_, hlt⟩ := lane
    rw [hpre.block]
    omega
  have hh : h < L.threads := by
    simpa only [h, consumer, Nat.add_assoc] using
      NamedBar.cta_thread_lt (c := cta) (NamedBar.cta_lt hp.1.1) hLane
  have hc : ctaOf L h = cta := by
    have := lane.isLt
    simp only [h, cta, ctaOf, consumer, hpre.block]
    omega
  have hw : wgOf L h = 2 := by
    have := lane.isLt
    simp only [h, cta, consumer, wgOf, tidOf_eq hpre, hpre.block]
    omega
  have hRow : ctaidY L h = ctaidY L g := by simp only [ctaidY, hc, cta]
  have hBlock := (reuse_count_and_block hpre hmax.1 hs hub hp hd).2
  rw [← hRow] at hBlock
  have hPast : 2 ≤ d.block := by omega
  let trace := (hs h hh).machine.produces (hmax.1.thr h hh)
  have hUsed {i : Nat} {q : Wg2.D}
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.wg2 q))) :
      Wg2RawTrace.released q ≤ d.block - 2 := by
    have hCount := Wg2RawTrace.composed_release_count hpre slot trace hq
    rw [hc] at hCount
    change arrivals m ((X.tr h).take i) = _ at hCount
    have hle : arrivals m ((X.tr h).take i) ≤ arrivals m (X.tr h) :=
      (List.take_sublist i (X.tr h)).countP_le
    rw [hCount] at hle
    change arrivals m (X.tr h) < d.block / 2 at hShort
    change (Wg2RawTrace.released q + (1 - d.block % 2)) / 2 ≤ _ at hle
    omega
  have hNoFinalFree {i : Nat} {q : Wg2.D}
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.wg2 q)))
      (hSite : q.site = .free)
      (hLast : q.block + 1 = totalBlocks (P.topkLen (Wg2.eOf L h))
        (P.extraTopkLen (Wg2.eOf L h))) : False := by
    have hUse := hUsed hq
    rw [show Wg2RawTrace.released q = q.block by simp [Wg2RawTrace.released, hSite]] at hUse
    change q.block + 1 = Result.blocks P (ctaidY L h) at hLast
    omega
  have hNoBar {i : Nat} {q : Wg2.D} (hi : i ≤ (X.tr h).length)
      (hq : Frame.stateAt (Machine.code P L) X h i = some (some (.wg2 q))) :
      q.site ≠ .barrier := by
    intro hClose
    obtain ⟨_, _, _, _, _, hState, hFree, hLast⟩ :=
      Wg2ReuseHistory.last_free_before_barrier_state hmax.1 hs ht hh hi hq hClose
    exact hNoFinalFree hState hFree hLast
  have hNoArrival {i tag : Nat} (he : X.get (h, i) = some ⟨tag, .bar 12 none .sync⟩) :
      False := by
    obtain ⟨q, hq, hSite, _, _⟩ := ScoreClosingGate.closing_at hpre hmax.1 hs ht he
    rcases Wg2ReuseHistory.role_state hpre hmax.1 hs hh hw hq with ⟨s, rfl⟩ | ⟨u, rfl⟩ | rfl
    · exact hSite
    · exact hNoBar (PTX.len_of_get he).le hq hSite
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
  rcases Wg2ReuseHistory.role_state hpre hmax.1 hs hh hw hq with ⟨s, rfl⟩ | ⟨u, rfl⟩ | rfl
  · simp only [priority, gatherTime, hd, blockTime, Bound.tmaOrdinal]
    omega
  · exact earlier_dequant_priority hd hPast (hUsed hq) (hNoBar le_rfl hq)
  · obtain ⟨_, _, _, _, _, hState, hFree, hLast⟩ :=
      Wg2ReuseHistory.last_free_before_done hpre hmax.1 hs ht hh le_rfl hw hq
    exact (hNoFinalFree hState hFree hLast).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
