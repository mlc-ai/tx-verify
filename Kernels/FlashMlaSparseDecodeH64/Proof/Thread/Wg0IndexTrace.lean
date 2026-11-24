-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields

@[expose] public section

/-! # Softmax index-ring prefix counts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0IndexTrace

open PTX PTX.Flow Ledger
open Wg0 (D)

private def held : Wg0.Site → Bool
  | .qkDone | .fenceLoad | .scoreLoad .. | .scoreWait | .fenceBefore | .maskRead
  | .exchStore _ | .pairBar | .peerRead _ | .rowMax | .wg0Sync2 | .validFree => true
  | _ => false

def returned : Wg0.Site → Bool
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore | .wg0Sync | .maskReady
  | .qkDone | .fenceLoad | .scoreLoad .. | .scoreWait | .fenceBefore | .maskRead
  | .exchStore _ | .pairBar | .peerRead _ | .rowMax | .wg0Sync2 | .validFree => false
  | _ => true

/-- Number of index blocks already released by a softmax lane at this site. -/
def released (d : D) : Nat :=
  match d.site with
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore => 0
  | _ => d.block + if returned d.site then 1 else 0

private def readyLoc (L : Launch) (g : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validReadyOff s.val⟩

private def freeLoc (L : Launch) (g : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validFreeOff s.val⟩

private def counts (L : Launch) (g : Nat) (slot : Fin 4) (d : D) (n : Cls → Nat) : Prop :=
  n (.arrive (freeLoc L g slot)) = ringUses 4 slot (released d) ∧
    n (.poll (readyLoc L g slot)) = ringUses 4 slot (released d) +
      if d.block % 4 = slot.val ∧ held d.site = true then 1 else 0

private theorem add_no_counts {L : Launch} {g : Nat} {slot : Fin 4}
    {e : Event} {n : Cls → Nat} {d d' : D}
    (hc : counts L g slot d n) (ha : arrivesOn (freeLoc L g slot) e = false)
    (hp : okPoll (readyLoc L g slot) e = false)
    (hb : released d' = released d)
    (hh : (d'.block % 4 = slot.val ∧ held d'.site = true) ↔
      (d.block % 4 = slot.val ∧ held d.site = true)) :
    counts L g slot d' (bump n e) := by
  obtain ⟨h1, h2⟩ := hc
  simp [counts, Cls.test, h1, h2, ha, hp, hb, hh]

private theorem arrive_outside_free {L : Launch} {g : Nat} {slot : Fin 4} {e : Event}
    {off : Nat} (hoff : off < 222872 ∨ 222904 ≤ off)
    (hk : e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + off⟩ 0 1 true .cta) :
    arrivesOn (freeLoc L g slot) e = false ∧ okPoll (readyLoc L g slot) e = false := by
  have hne : (⟨.shared, ctaOf L g, L.sharedBase + off⟩ : Loc) ≠ freeLoc L g slot := by
    intro heq
    have he := congrArg Loc.addr heq
    have := slot.isLt
    simp [freeLoc, Wg0.validFreeOff] at he
    omega
  simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem gemm_wait_outside_ready {slot : Fin 4} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .qkDone ∨ d.site = .svDone)
    (hf : (Wg0.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (freeLoc L g slot) e = false ∧ okPoll (readyLoc L g slot) e = false := by
  obtain ⟨off, _, ok, _, ho, hk⟩ := RingEvents.gemmDone_wait hpre hd hf
  have hmin : 222904 ≤ off := by
    rcases ho with rfl | rfl <;> first
      | unfold Wg0.qkDoneOff; omega
      | unfold Wg0.svDoneOff; omega
  have hne : (⟨.shared, g / L.block, L.sharedBase + off⟩ : Loc) ≠ readyLoc L g slot := by
    intro heq
    have he := congrArg Loc.addr heq
    have := slot.isLt
    simp [readyLoc, Wg0.validReadyOff] at he
    omega
  cases ok <;> simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem counts_step {slot : Fin 4} {d d' : D} {e : Event} {n : Cls → Nat}
    {o : Option TState} (hpre : Pre P L mem0) (hc : counts L g slot d n)
    (hf : (Wg0.code P L g).toMachine.Fired (some d) e o) (hn : Wg0.next P L g d e = some (some d'))
    :
    counts L g slot d' (bump n e) := by
  cases hd : d.site <;> cases hk : e.kind <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep,
      hd, hk, Option.some.injEq, reduceCtorEq] at hn
  case lastStore.arrive =>
    have hblock := ((Exists.choose_spec hf).1.2 : Wg0.Inv P L g d).preloop (.inr hd) |>.1
    have hoff : Wg0.lastStoreOff < 222872 := by decide
    have he := arrive_outside_free (slot := slot) (Or.inl hoff)
      (RingEvents.lastStore_arrive hpre hd hf)
    cases hn
    apply add_no_counts hc he.1 he.2 <;> simp [released, returned, held, hd, hblock]
  case qkDone.wait m p ok acq sc =>
    have he := gemm_wait_outside_ready (slot := slot) hpre (Or.inl hd) hf
    cases ok <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, returned, held, hd]
  case svDone.wait m p ok acq sc =>
    have he := gemm_wait_outside_ready (slot := slot) hpre (Or.inr hd) hf
    cases ok <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, returned, held, hd]
  case maskReady.wait m p ok acq sc =>
    obtain ⟨ok', he⟩ := RingEvents.maskReady_wait hpre hd hf
    have hok : ok = ok' := by rw [hk] at he; exact (Kind.wait.inj he).2.2.1
    subst ok'
    have hep : okPoll (readyLoc L g slot) e = (ok && decide (d.block % 4 = slot.val)) := by
      cases ok <;> simp [okPoll, sourceWaitSuccess, he, readyLoc, Wg0.validReadyOff, ctaOf]
    obtain ⟨h1, h2⟩ := hc
    cases ok <;> cases hn <;> simp [counts, Cls.test, h1, h2, hep, released, returned, held, hd,
      hk, arrivesOn, sourceArrive]
  case validFree.arrive =>
    have he := RingEvents.maskFree_arrive hpre hd hf
    have ha : arrivesOn (freeLoc L g slot) e = decide (d.block % 4 = slot.val) := by
      simp [arrivesOn, sourceArrive, he, freeLoc, Wg0.validFreeOff, ctaOf]
    cases hn
    obtain ⟨h1, h2⟩ := hc
    simp [counts, Cls.test, h1, h2, ha, ringUses_succ slot.isLt, released, returned, held, hd, hk,
      okPoll, sourceWaitSuccess]
  case maxRead.rd =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, hpeer, rfl⟩ := Option.map_eq_some_iff.mp hmap
      have hb := (Wg0.peer_preserves_sub hpeer).1
      apply add_no_counts hc <;>
        simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, released, returned, held,
          hd, hb]
    · cases hn
  case rescaleVote.voteMode =>
    obtain ⟨_, hrv, hmap⟩ := Option.bind_eq_some_iff.mp hn
    obtain ⟨_, hp, rfl⟩ := Option.map_eq_some_iff.mp hmap
    have hb := (Wg0.probability_preserves_sub hp).1.trans (Wg0.vote_preserves_sub hrv).1
    apply add_no_counts hc <;>
      simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, released, returned, held,
        hd, hb]
  case soReady.arrive =>
    have ho : 222904 ≤ Wg0.soReadyOff (d.block % 2) := by
      unfold Wg0.soReadyOff
      omega
    have he := arrive_outside_free (slot := slot) (Or.inr ho) (RingEvents.scores_arrive hpre hd hf)
    split at hn <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, returned, held, hd]
  all_goals
    repeat' split at hn
    all_goals try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    all_goals cases hn
    all_goals
      apply add_no_counts hc
      all_goals simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk,
        released, returned, held, hd, Wg0.loadScores, Wg0.afterScoreSite,
        Wg0.afterLen, Wg0.afterSink, Wg0.epiAfterBar, Wg0.loadOutput]
      all_goals (try split_ifs) <;> simp_all

private theorem counts_at (hpre : Pre P L mem0) (slot : Fin 4) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) : counts L g slot d (count es i) := by
  refine Ledger.wg0 (fun _ _ _ _ => ring_prologue) ht (counts L g slot) (fun n hn => ?_)
    (fun _ _ _ _ _ hf hs hc => counts_step hpre hc hf hs) hs
  unfold Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen
  split_ifs <;> simp [counts, released, held, hn _ ⟨_, .inl rfl⟩, hn _ ⟨_, .inr (.inl rfl)⟩,
    ringUses_zero slot.isLt]
/-- The softmax lane has waited once for each earlier use of the current index slot. -/
theorem composed_ready_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .maskReady) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validReadyOff (d.block % 4)⟩
      (es.take i) = d.block / 4 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (readyLoc L g slot)) = d.block / 4
  obtain ⟨_, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, hd, returned]
  rw [hp, hb, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  simp [held, hd]

/-- Each consumed block contributes one release to its own slot. -/
theorem composed_release_count (hpre : Pre P L mem0) (slot : Fin 4) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validFreeOff slot.val⟩
      (es.take i) = (released d + (3 - slot.val)) / 4 :=
  (counts_at hpre slot ht hs).1

/-- The softmax lane's release follows the successful ready poll for the current use. -/
theorem composed_free_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .validFree) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validFreeOff (d.block % 4)⟩
        (es.take i) = d.block / 4 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validReadyOff (d.block % 4)⟩
        (es.take i) = d.block / 4 + 1 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (freeLoc L g slot)) = _ ∧ count es i (.poll (readyLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, hd, returned]
  rw [ha, hp, hb, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]


/-- The softmax mask read follows the acquire of its slot and precedes the release. -/
theorem composed_mask_read_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : Wg0.D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg0 d))) (hd : d.site = .maskRead) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validFreeOff (d.block % 4)⟩
        (es.take i) = d.block / 4 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg0.validReadyOff (d.block % 4)⟩
        (es.take i) = d.block / 4 + 1 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (freeLoc L g slot)) = _ ∧ count es i (.poll (readyLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, returned, hd]
  rw [ha, hp, hb, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0IndexTrace
