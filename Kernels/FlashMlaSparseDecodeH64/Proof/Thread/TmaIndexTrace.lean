-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger

@[expose] public section

/-! # The TMA consumer's index-ring prefix counts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaIndexTrace

open PTX PTX.Flow Ledger
open Wg1Tma (D)

def begun : Wg1Tma.Site → Bool
  | .elect | .lenOrig | .lenExtra | .waitQ | .waitLast => false
  | _ => true

private def held : Wg1Tma.Site → Bool
  | .waitFree | .coord .. | .issue _ | .rawReady | .coordFree => true
  | _ => false

/-- Number of index blocks already released by the gather producer at this site. -/
def released (d : D) : Nat := if begun d.site then d.block else 0

private def readyLoc (L : Launch) (g : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.readyOff s.val⟩

private def freeLoc (L : Launch) (g : Nat) (s : Fin 4) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.coordFreeOff s.val⟩

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

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem entry_outside_ready {slot : Fin 4} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .waitQ ∨ d.site = .waitLast)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (freeLoc L g slot) e = false ∧ okPoll (readyLoc L g slot) e = false := by
  obtain ⟨off, ok, hOff, hk⟩ := RingEvents.tmaEntry_wait hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + off⟩ : Loc) ≠ readyLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    have hslot := slot.isLt
    rcases hOff with rfl | rfl <;>
      simp [readyLoc, Wg1Tma.readyOff, Wg1Tma.qUtccpOff, Wg1Tma.lastStoreOff] at he <;> omega
  cases ok <;> simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem raw_wait_outside_ready {slot : Fin 4} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .waitFree)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (freeLoc L g slot) e = false ∧ okPoll (readyLoc L g slot) e = false := by
  obtain ⟨ok, hk⟩ := RingEvents.rawFree_wait hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + Wg1Tma.rawFreeOff (d.block % 2)⟩ : Loc) ≠
      readyLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    simp [readyLoc, Wg1Tma.readyOff, Wg1Tma.rawFreeOff] at he
    omega
  cases ok <;> simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem raw_arrive_outside_free {slot : Fin 4} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .rawReady)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (freeLoc L g slot) e = false ∧ okPoll (readyLoc L g slot) e = false := by
  have hk := RingEvents.rawReady_expectTx hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + Wg1Tma.rawReadyOff (d.block % 2)⟩ : Loc) ≠
      freeLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    simp [freeLoc, Wg1Tma.coordFreeOff, Wg1Tma.rawReadyOff] at he
    omega
  simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem release_delta {d : D} :
    released (Wg1Tma.afterFree d) = d.block + 1 ∧ held (Wg1Tma.afterFree d).site = false := by
  unfold Wg1Tma.afterFree
  split <;> simp [released, begun, held]

private theorem counts_step {slot : Fin 4} {d d' : D} {e : Event} {n : Cls → Nat}
    {o : Option TState} (hpre : Pre P L mem0) (hc : counts L g slot d n)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o)
    (hn : Wg1Tma.next P L g d e = some (some d')) :
    counts L g slot d' (bump n e) := by
  cases hd : d.site <;> cases hk : e.kind <;>
    simp only [Wg1Tma.next, hd, hk, Option.some.injEq, reduceCtorEq] at hn
  case elect.elect =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · unfold Wg1Tma.firstLenSite
      split_ifs <;> simp [released, hd, begun]
    · unfold Wg1Tma.firstLenSite
      split_ifs <;> simp [hd, held]
  case lenOrig.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · split <;> simp [released, begun, hd]
    · split <;> simp [held, hd]
  case lenExtra.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · simp [released, begun, hd]
    · simp [held, hd]
  case waitQ.wait m p ok acq sc =>
    have he := entry_outside_ready (slot := slot) hpre (Or.inl hd) hf
    cases ok <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, begun, held, hd]
  case waitLast.wait m p ok acq sc =>
    have he := entry_outside_ready (slot := slot) hpre (Or.inr hd) hf
    have hpos := Nat.ne_of_gt (totalBlocks_pos d.len0 d.len1)
    simp only [hpos, ↓reduceIte] at hn
    cases ok <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, begun, held, hd, Wg1Tma.beginLoop]
  case waitCoord.wait m p ok acq sc =>
    obtain ⟨ok', he⟩ := RingEvents.validReady_wait hpre hd hf
    have hok : ok = ok' := by rw [hk] at he; exact (Kind.wait.inj he).2.2.1
    subst ok'
    have hep : okPoll (readyLoc L g slot) e = (ok && decide (d.block % 4 = slot.val)) := by
      cases ok <;> simp [okPoll, sourceWaitSuccess, he, readyLoc, Wg1Tma.readyOff, ctaOf]
    obtain ⟨h1, h2⟩ := hc
    cases ok <;> cases hn <;> simp [counts, Cls.test, h1, h2, hep, released, begun, held, hd, hk,
      arrivesOn, sourceArrive]
  case waitFree.wait m p ok acq sc =>
    have he := raw_wait_outside_ready (slot := slot) hpre hd hf
    cases ok <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, begun, held, hd]
  case coord.rd =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · unfold Wg1Tma.afterCoord
      split_ifs <;> simp [released, begun, hd]
    · unfold Wg1Tma.afterCoord
      split_ifs <;> simp [held, hd]
  case issue.tensorIssue =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · unfold Wg1Tma.afterIssue
      split_ifs <;> simp [released, begun, hd]
    · unfold Wg1Tma.afterIssue
      split_ifs <;> simp [held, hd]
  case rawReady.arrive =>
    have he := raw_arrive_outside_free (slot := slot) hpre hd hf
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc he.1 he.2 <;> simp [released, begun, held, hd]
  case coordFree.arrive =>
    have he := RingEvents.validFree_arrive hpre hd hf
    have ha : arrivesOn (freeLoc L g slot) e = decide (d.block % 4 = slot.val) := by
      simp [arrivesOn, sourceArrive, he, freeLoc, Wg1Tma.coordFreeOff, ctaOf]
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    obtain ⟨h1, h2⟩ := hc
    simp only [counts, bump_apply, Cls.test]
    simp only [h1, h2, ha, release_delta.1, release_delta.2]
    simp [ringUses_succ slot.isLt, released, begun, held, hd, hk, okPoll, sourceWaitSuccess]
  case barrier.bar =>
    split at hn <;> cases hn <;> apply add_no_counts hc
    all_goals simp [released, begun, held, hd, hk, okPoll, sourceWaitSuccess,
      arrivesOn, sourceArrive]

private theorem counts_at (hpre : Pre P L mem0) (slot : Fin 4) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) : counts L g slot d (count es i) := by
  refine Ledger.tma (fun _ _ _ _ => ring_prologue) ht (counts L g slot) (fun n hn => ?_)
    (fun _ _ _ _ _ hf hs hc => counts_step hpre hc hf hs) hs
  simp [counts, Wg1Tma.init, released, begun, held, hn _ ⟨_, .inl rfl⟩, hn _ ⟨_, .inr (.inl rfl)⟩,
    ringUses_zero slot.isLt]
/-- The TMA consumer has waited once for each earlier use of the current index slot. -/
theorem composed_ready_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hd : d.site = .waitCoord) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.readyOff (d.block % 4)⟩
      (es.take i) = d.block / 4 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (readyLoc L g slot)) = d.block / 4
  obtain ⟨_, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, hd, begun]
  rw [hp, hb, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  simp [held, hd]

/-- Each consumed block contributes one release to its own slot. -/
theorem composed_release_count (hpre : Pre P L mem0) (slot : Fin 4) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.coordFreeOff slot.val⟩
      (es.take i) = (released d + (3 - slot.val)) / 4 :=
  (counts_at hpre slot ht hs).1

/-- The TMA consumer's release follows the successful ready poll for the current use. -/
theorem composed_free_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hd : d.site = .coordFree) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.coordFreeOff (d.block % 4)⟩
        (es.take i) = d.block / 4 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.readyOff (d.block % 4)⟩
        (es.take i) = d.block / 4 + 1 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (freeLoc L g slot)) = _ ∧ count es i (.poll (readyLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, hd, begun]
  rw [ha, hp, hb, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]


/-- A TMA coordinate read follows the acquire of its current slot and precedes its return. -/
theorem composed_coord_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D} {k : Fin 16}
    {j : Fin 4} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hd : d.site = .coord k j) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.coordFreeOff (d.block % 4)⟩
        (es.take i) = d.block / 4 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.readyOff (d.block % 4)⟩
        (es.take i) = d.block / 4 + 1 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (freeLoc L g slot)) = _ ∧ count es i (.poll (readyLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, hd, begun]
  rw [ha, hp, hb, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaIndexTrace
