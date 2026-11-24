-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields

@[expose] public section

/-! # Softmax GEMM-ring prefix counts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0GemmTrace

open PTX PTX.Flow Ledger
open Wg0 (D)

def held : Wg0.Site → Bool
  | .fenceLoad | .scoreLoad .. | .scoreWait | .fenceBefore | .maskRead | .exchStore _ | .pairBar
  | .peerRead _ | .rowMax | .wg0Sync2 | .validFree | .maxRead | .rescaleVote | .pStore _
  | .rescaleFence | .rescaleLoad _ | .rescaleWait _ | .rescaleStore _ | .rescaleWaitSt _
  | .rescaleFenceB | .soFence | .soReady => true
  | _ => false

/-- The number of blocks whose probability publication precedes this state. -/
def publishedBlocks (d : D) : Nat :=
  match d.site with
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore => 0
  | _ => d.block + if d.site.inEpilogue then 1 else 0

private def readyLoc (L : Launch) (g : Nat) (s : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff s.val⟩

private def freeLoc (L : Launch) (g : Nat) (s : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg0.soReadyOff s.val⟩

private def counts (L : Launch) (g : Nat) (slot : Fin 2) (d : D) (n : Cls → Nat) : Prop :=
  n (.arrive (freeLoc L g slot)) = ringUses 2 slot (publishedBlocks d) ∧
    n (.poll (readyLoc L g slot)) = ringUses 2 slot (publishedBlocks d) +
      if d.block % 2 = slot.val ∧ held d.site = true then 1 else 0

private theorem add_no_counts {L : Launch} {g : Nat} {slot : Fin 2}
    {e : Event} {n : Cls → Nat} {d d' : D}
    (hc : counts L g slot d n) (ha : arrivesOn (freeLoc L g slot) e = false)
    (hp : okPoll (readyLoc L g slot) e = false)
    (hb : publishedBlocks d' = publishedBlocks d)
    (hh : (d'.block % 2 = slot.val ∧ held d'.site = true) ↔
      (d.block % 2 = slot.val ∧ held d.site = true)) :
    counts L g slot d' (bump n e) := by
  obtain ⟨h1, h2⟩ := hc
  simp [counts, Cls.test, h1, h2, ha, hp, hb, hh]

private theorem arrive_outside_score {L : Launch} {g : Nat} {slot : Fin 2} {e : Event}
    {off : Nat} (hoff : off < 222920)
    (hk : e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + off⟩ 0 1 true .cta) :
    arrivesOn (freeLoc L g slot) e = false ∧ okPoll (readyLoc L g slot) e = false := by
  have hne : (⟨.shared, ctaOf L g, L.sharedBase + off⟩ : Loc) ≠ freeLoc L g slot := by
    intro heq
    have he := congrArg Loc.addr heq
    simp [freeLoc, Wg0.soReadyOff] at he
    omega
  simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem poll_outside_qk {L : Launch} {g : Nat} {slot : Fin 2} {e : Event}
    {off p : Nat} {ok acq : Bool} {sc : MbarScope} (hoff : off < 222904 ∨ 222920 ≤ off)
    (hk : e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ p ok acq sc) :
    arrivesOn (freeLoc L g slot) e = false ∧ okPoll (readyLoc L g slot) e = false := by
  have hne : (⟨.shared, g / L.block, L.sharedBase + off⟩ : Loc) ≠ readyLoc L g slot := by
    intro heq
    have he := congrArg Loc.addr heq
    have := slot.isLt
    simp [readyLoc, Wg0.qkDoneOff] at he
    omega
  cases ok <;> simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem counts_step {slot : Fin 2} {d d' : D} {e : Event} {n : Cls → Nat}
    {o : Option TState} (hpre : Pre P L mem0) (hc : counts L g slot d n)
    (hf : (Wg0.code P L g).toMachine.Fired (some d) e o) (hn : Wg0.next P L g d e = some (some d'))
    :
    counts L g slot d' (bump n e) := by
  cases hd : d.site <;> cases hk : e.kind <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep,
      hd, hk, Option.some.injEq, reduceCtorEq] at hn
  case lastStore.arrive =>
    have hblock := ((Exists.choose_spec hf).1.2 : Wg0.Inv P L g d).preloop (.inr hd) |>.1
    have hoff : Wg0.lastStoreOff < 222920 := by decide
    have he := arrive_outside_score (slot := slot) hoff (RingEvents.lastStore_arrive hpre hd hf)
    cases hn
    apply add_no_counts hc he.1 he.2 <;>
      simp [publishedBlocks, Wg0.Site.inEpilogue, held, hd, hblock]
  case qkDone.wait m p ok acq sc =>
    obtain ⟨ok', _, he⟩ := RingEvents.gemmDone_wait_exact hpre (Or.inl hd) hf
    rw [ite_eq_left hd] at he
    have hok : ok = ok' := by rw [hk] at he; exact (Kind.wait.inj he).2.2.1
    subst ok'
    have hep : okPoll (readyLoc L g slot) e = (ok && decide (d.block % 2 = slot.val)) := by
      cases ok <;> simp [okPoll, sourceWaitSuccess, he, readyLoc, Wg0.qkDoneOff, ctaOf]
    obtain ⟨h1, h2⟩ := hc
    cases ok <;> cases hn <;> simp [counts, Cls.test, h1, h2, hep, publishedBlocks,
      Wg0.Site.inEpilogue, held, hd, hk, arrivesOn, sourceArrive]
  case svDone.wait m p ok acq sc =>
    obtain ⟨_, _, he⟩ := RingEvents.gemmDone_wait_exact hpre (Or.inr hd) hf
    have hne : d.site ≠ .qkDone := by simp [hd]
    rw [ite_eq_right hne] at he
    have hoff : 222920 ≤ Wg0.svDoneOff (d.block % 2) := by
      unfold Wg0.svDoneOff
      omega
    have h := poll_outside_qk (slot := slot) (.inr hoff) he
    cases ok <;> cases hn <;> apply add_no_counts hc h.1 h.2
    all_goals simp [publishedBlocks, Wg0.Site.inEpilogue, held, hd]
  case maskReady.wait m p ok acq sc =>
    obtain ⟨_, he⟩ := RingEvents.maskReady_wait hpre hd hf
    have hoff : Wg0.validReadyOff (d.block % 4) < 222904 := by
      unfold Wg0.validReadyOff
      omega
    have h := poll_outside_qk (slot := slot) (.inl hoff) he
    cases ok <;> cases hn <;> apply add_no_counts hc h.1 h.2
    all_goals simp [publishedBlocks, Wg0.Site.inEpilogue, held, hd]
  case validFree.arrive =>
    have hoff : Wg0.validFreeOff (d.block % 4) < 222920 := by
      unfold Wg0.validFreeOff
      omega
    have he := arrive_outside_score (slot := slot) hoff (RingEvents.maskFree_arrive hpre hd hf)
    cases hn
    apply add_no_counts hc he.1 he.2 <;> simp [publishedBlocks, Wg0.Site.inEpilogue, held, hd]
  case maxRead.rd =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, hpeer, rfl⟩ := Option.map_eq_some_iff.mp hmap
      have hb := (Wg0.peer_preserves_sub hpeer).1
      apply add_no_counts hc <;>
        simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk,
          publishedBlocks, Wg0.Site.inEpilogue, held, hd, hb]
    · cases hn
  case rescaleVote.voteMode =>
    obtain ⟨_, hrv, hmap⟩ := Option.bind_eq_some_iff.mp hn
    obtain ⟨_, hp, rfl⟩ := Option.map_eq_some_iff.mp hmap
    have hb := (Wg0.probability_preserves_sub hp).1.trans (Wg0.vote_preserves_sub hrv).1
    apply add_no_counts hc <;>
      simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk,
        publishedBlocks, Wg0.Site.inEpilogue, held, hd, hb]
  case soReady.arrive =>
    have he := RingEvents.scores_arrive hpre hd hf
    have ha : arrivesOn (freeLoc L g slot) e = decide (d.block % 2 = slot.val) := by
      simp [arrivesOn, sourceArrive, he, freeLoc, Wg0.soReadyOff, ctaOf]
    obtain ⟨h1, h2⟩ := hc
    split at hn <;> cases hn <;>
      simp [counts, Cls.test, h1, h2, ha, ringUses_succ slot.isLt, publishedBlocks,
        Wg0.Site.inEpilogue, held, hd, hk, okPoll,
        sourceWaitSuccess]
  all_goals
    repeat' split at hn
    all_goals try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    all_goals cases hn
    all_goals
      apply add_no_counts hc
      all_goals simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk,
        publishedBlocks, Wg0.Site.inEpilogue, held, hd, Wg0.loadScores, Wg0.afterScoreSite,
        Wg0.afterLen, Wg0.afterSink, Wg0.epiAfterBar, Wg0.loadOutput]
      all_goals (try split_ifs) <;> simp_all

private theorem counts_at (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) : counts L g slot d (count es i) := by
  refine Ledger.wg0 (fun _ _ _ _ => ring_prologue) ht (counts L g slot) (fun n hn => ?_)
    (fun _ _ _ _ _ hf hs hc => counts_step hpre hc hf hs) hs
  unfold Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen
  split_ifs <;> simp [counts, publishedBlocks, held, hn _ ⟨_, .inl rfl⟩, hn _ ⟨_, .inr (.inl rfl)⟩,
    ringUses_zero slot.isLt]
/-- Each slot receives exactly one score publication per completed block on that slot. -/
theorem score_arrivals_of_state (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.soReadyOff slot.val⟩ (es.take i) =
      (publishedBlocks d + (1 - slot.val)) / 2 :=
  (counts_at hpre slot ht hs).1

/-- A followed state identifies every QK acquisition in its own trace prefix. -/
theorem qk_successes_of_state (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff slot.val⟩ (es.take i) =
      (publishedBlocks d + (1 - slot.val)) / 2 +
        (if d.block % 2 = slot.val ∧ held d.site = true then 1 else 0) :=
  (counts_at hpre slot ht hs).2

/-- No QK slot has been acquired at entry to the first mask acquire. -/
theorem qk_successes_at_first_mask (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .maskReady) (hFirst : d.block = 0) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff slot.val⟩ (es.take i) = 0 := by
  obtain ⟨_, hCount⟩ := counts_at hpre slot ht hs
  simp only [publishedBlocks, hd, Wg0.Site.inEpilogue, Bool.false_eq_true, ↓reduceIte,
    hFirst, held, and_false, Nat.add_zero, ringUses_zero slot.isLt] at hCount
  exact hCount

/-- The softmax lane has waited for QK once per earlier use of the current slot. -/
theorem composed_qk_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .qkDone) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff (d.block % 2)⟩
      (es.take i) = d.block / 2 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (readyLoc L g slot)) = d.block / 2
  obtain ⟨_, hp⟩ := counts_at hpre slot ht hs
  have hb : publishedBlocks d = d.block := by simp [publishedBlocks, hd, Wg0.Site.inEpilogue]
  rw [hp, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [held, hd]

/-- The score-ready arrival follows the successful QK poll for the current use. -/
theorem composed_score_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .soReady) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.soReadyOff (d.block % 2)⟩
        (es.take i) = d.block / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (freeLoc L g slot)) = _ ∧ count es i (.poll (readyLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : publishedBlocks d = d.block := by simp [publishedBlocks, hd, Wg0.Site.inEpilogue]
  rw [ha, hp, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]


/-- A probability store is after QK completion and before probability publication. -/
theorem composed_probability_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : Wg0.D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : ∃ k, d.site = .pStore k) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.soReadyOff (d.block % 2)⟩
        (es.take i) = d.block / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 := by
  obtain ⟨k, hd⟩ := hd
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (freeLoc L g slot)) = _ ∧ count es i (.poll (readyLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : publishedBlocks d = d.block := by simp [publishedBlocks, Wg0.Site.inEpilogue, hd]
  rw [ha, hp, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]

/-- Rescaling precedes its probability publication and follows its QK acquire. -/
theorem composed_in_rescale_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : Wg0.D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site.inRescale = true) (slot : Fin 2) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.soReadyOff slot.val⟩ (es.take i) =
        (d.block + (1 - slot.val)) / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 := by
  let current : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  have ⟨hb, hh⟩ : publishedBlocks d = d.block ∧ held d.site = true := by
    cases hsite : d.site <;>
      simp_all [Wg0.Site.inRescale, publishedBlocks, Wg0.Site.inEpilogue, held]
  have ha := (counts_at hpre slot ht hs).1
  have hp := (counts_at hpre current ht hs).2
  change count es i (.arrive (freeLoc L g slot)) = _ ∧
    count es i (.poll (readyLoc L g current)) = _
  rw [ha, hp, hb, ringUses_here (S := 2) (s := current) (k := d.block) rfl current.isLt]
  simp [ringUses, current, hh]

/-- Rescaling precedes its probability publication and follows its QK acquire. -/
theorem composed_rescale_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : Wg0.D}
    {k : Fin 4} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .rescaleStore k) (slot : Fin 2) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.soReadyOff slot.val⟩ (es.take i) =
        (d.block + (1 - slot.val)) / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 :=
  composed_in_rescale_counts hpre ht hs (by rw [hd]; rfl) slot

/-- A score-exchange write follows QK completion for its block. -/
theorem composed_exchange_qk_count (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    {grp : Fin 8} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .exchStore grp) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff (d.block % 2)⟩
      (es.take i) = d.block / 2 + 1 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (readyLoc L g slot)) = _
  rw [(counts_at hpre slot ht hs).2]
  simp [publishedBlocks, Wg0.Site.inEpilogue, held, hd,
    ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt, slot]

/-- A score load follows earlier score publications of its slot. -/
theorem composed_scoreLoad_arrivals {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .scoreLoad arm part) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.soReadyOff (d.block % 2)⟩
      (es.take i) = d.block / 2 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (freeLoc L g slot)) = _
  have ha := (counts_at hpre slot ht hs).1
  have hb : publishedBlocks d = d.block := by simp [publishedBlocks, Wg0.Site.inEpilogue, hd]
  rw [ha, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]

/-- A score-load wait follows earlier publications of its slot, with this block still held. -/
theorem composed_scoreWait_arrivals (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .scoreWait) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.soReadyOff (d.block % 2)⟩
      (es.take i) = d.block / 2 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (freeLoc L g slot)) = _
  have ha := (counts_at hpre slot ht hs).1
  have hb : publishedBlocks d = d.block := by simp [publishedBlocks, Wg0.Site.inEpilogue, hd]
  rw [ha, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]

/-- A lane reaching the closing barrier has acquired QK completion for every block. -/
theorem composed_closing_qk_count (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .everyone) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff slot.val⟩ (es.take i) =
      (d.block + 1 + (1 - slot.val)) / 2 := by
  change count es i (.poll (readyLoc L g slot)) = _
  rw [(counts_at hpre slot ht hs).2]
  simp [publishedBlocks, Wg0.Site.inEpilogue, held, hd, ringUses]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0GemmTrace
