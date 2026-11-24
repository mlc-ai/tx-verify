-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger

@[expose] public section

/-! # The TMA producer's raw-ring prefix counts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaRawTrace

open PTX PTX.Flow Ledger
open Wg1Tma (D)

/-- The gather role has entered its block loop or is past it. -/
def begun : Wg1Tma.Site → Bool
  | .elect | .lenOrig | .lenExtra | .waitQ | .waitLast => false
  | _ => true

private def published : Wg1Tma.Site → Bool
  | .coordFree => true
  | _ => false

private def held : Wg1Tma.Site → Bool
  | .coord .. | .issue _ | .rawReady | .coordFree => true
  | _ => false

private def released (d : D) : Nat := if begun d.site then d.block else 0

private def pollLoc (L : Launch) (g : Nat) (s : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawFreeOff s.val⟩

private def arriveLoc (L : Launch) (g : Nat) (s : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff s.val⟩

private def counts (L : Launch) (g : Nat) (slot : Fin 2) (d : D) (n : Cls → Nat) : Prop :=
  n (.arrive (arriveLoc L g slot)) = ringUses 2 slot (released d) +
      (if d.block % 2 = slot.val ∧ published d.site = true then 1 else 0) ∧
    n (.poll (pollLoc L g slot)) = ringUses 2 slot (released d) +
      if d.block % 2 = slot.val ∧ held d.site = true then 1 else 0

private theorem add_no_counts {L : Launch} {g : Nat} {slot : Fin 2}
    {e : Event} {n : Cls → Nat} {d d' : D}
    (hc : counts L g slot d n) (ha : arrivesOn (arriveLoc L g slot) e = false)
    (hp : okPoll (pollLoc L g slot) e = false)
    (hb : released d' = released d)
    (hpub : (d'.block % 2 = slot.val ∧ published d'.site = true) ↔
      (d.block % 2 = slot.val ∧ published d.site = true))
    (hh : (d'.block % 2 = slot.val ∧ held d'.site = true) ↔
      (d.block % 2 = slot.val ∧ held d.site = true)) :
    counts L g slot d' (bump n e) := by
  obtain ⟨h1, h2⟩ := hc
  simp [counts, Cls.test, h1, h2, ha, hp, hb, hpub, hh]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem entry_outside_ready {slot : Fin 2} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .waitQ ∨ d.site = .waitLast)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (arriveLoc L g slot) e = false ∧ okPoll (pollLoc L g slot) e = false := by
  obtain ⟨off, ok, hOff, hk⟩ := RingEvents.tmaEntry_wait hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + off⟩ : Loc) ≠ pollLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    have hslot := slot.isLt
    rcases hOff with rfl | rfl <;>
      simp [pollLoc, Wg1Tma.rawFreeOff, Wg1Tma.qUtccpOff, Wg1Tma.lastStoreOff] at he <;> omega
  cases ok <;> simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem index_wait_outside_free {slot : Fin 2} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .waitCoord)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (arriveLoc L g slot) e = false ∧ okPoll (pollLoc L g slot) e = false := by
  obtain ⟨ok, hk⟩ := RingEvents.validReady_wait hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + Wg1Tma.readyOff (d.block % 4)⟩ : Loc) ≠
      pollLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    simp [pollLoc, Wg1Tma.rawFreeOff, Wg1Tma.readyOff] at he
    omega
  cases ok <;> simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem release_index_outside_raw {slot : Fin 2} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .coordFree)
    (hf : (Wg1Tma.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (arriveLoc L g slot) e = false ∧ okPoll (pollLoc L g slot) e = false := by
  have hk := RingEvents.validFree_arrive hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + Wg1Tma.coordFreeOff (d.block % 4)⟩ : Loc) ≠
      arriveLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    simp [arriveLoc, Wg1Tma.rawReadyOff, Wg1Tma.coordFreeOff] at he
    omega
  simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem release_delta {d : D} :
    released (Wg1Tma.afterFree d) = d.block + 1 ∧
      published (Wg1Tma.afterFree d).site = false ∧ held (Wg1Tma.afterFree d).site = false := by
  unfold Wg1Tma.afterFree
  split <;> simp [released, begun, published, held]

private theorem counts_step {slot : Fin 2} {d d' : D} {e : Event} {n : Cls → Nat}
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
      split_ifs <;> simp [hd, published]
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
    · split <;> simp [published, hd]
    · split <;> simp [held, hd]
  case lenExtra.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · simp [released, begun, hd]
    · simp [published, hd]
    · simp [held, hd]
  case waitQ.wait m p ok acq sc =>
    have he := entry_outside_ready (slot := slot) hpre (Or.inl hd) hf
    cases ok <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, begun, published, held, hd]
  case waitLast.wait m p ok acq sc =>
    have he := entry_outside_ready (slot := slot) hpre (Or.inr hd) hf
    have hpos := Nat.ne_of_gt (totalBlocks_pos d.len0 d.len1)
    simp only [hpos, ↓reduceIte] at hn
    cases ok <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, begun, published, held, hd, Wg1Tma.beginLoop]
  case waitCoord.wait m p ok acq sc =>
    have he := index_wait_outside_free (slot := slot) hpre hd hf
    cases ok <;> cases hn <;> apply add_no_counts hc he.1 he.2
    all_goals simp [released, begun, published, held, hd]
  case waitFree.wait m p ok acq sc =>
    obtain ⟨ok', he⟩ := RingEvents.rawFree_wait hpre hd hf
    have hok : ok = ok' := by rw [hk] at he; exact (Kind.wait.inj he).2.2.1
    subst ok'
    have hep : okPoll (pollLoc L g slot) e = (ok && decide (d.block % 2 = slot.val)) := by
      cases ok <;> simp [okPoll, sourceWaitSuccess, he, pollLoc, Wg1Tma.rawFreeOff, ctaOf]
    obtain ⟨h1, h2⟩ := hc
    cases ok <;> cases hn <;> simp [counts, Cls.test, h1, h2, hep, released, begun, published,
      held, hd, hk, arrivesOn, sourceArrive]
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
      split_ifs <;> simp [published, hd]
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
      split_ifs <;> simp [published, hd]
    · unfold Wg1Tma.afterIssue
      split_ifs <;> simp [held, hd]
  case rawReady.arrive =>
    have he := RingEvents.rawReady_expectTx hpre hd hf
    have ha : arrivesOn (arriveLoc L g slot) e = decide (d.block % 2 = slot.val) := by
      simp [arrivesOn, sourceArrive, he, arriveLoc, Wg1Tma.rawReadyOff, ctaOf]
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    obtain ⟨h1, h2⟩ := hc
    simp [counts, Cls.test, h1, h2, ha, released, begun, published, held, hd, hk, okPoll,
      sourceWaitSuccess]
  case coordFree.arrive =>
    have he := release_index_outside_raw (slot := slot) hpre hd hf
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    obtain ⟨h1, h2⟩ := hc
    simp only [counts, bump_apply, Cls.test]
    simp only [h1, h2, he.1, he.2, release_delta.1, release_delta.2.1, release_delta.2.2]
    simp [ringUses_succ slot.isLt, released, begun, published, held, hd]
  case barrier.bar =>
    split at hn <;> cases hn <;> apply add_no_counts hc
    all_goals simp [released, begun, published, held, hd, hk, okPoll, sourceWaitSuccess,
      arrivesOn, sourceArrive]

private theorem counts_at (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) : counts L g slot d (count es i) := by
  refine Ledger.tma (fun _ _ _ _ => ring_prologue) ht (counts L g slot) (fun n hn => ?_)
    (fun _ _ _ _ _ hf hs hc => counts_step hpre hc hf hs) hs
  simp [counts, Wg1Tma.init, released, begun, held, published, hn _ ⟨_, .inl rfl⟩, hn _ ⟨_,
    .inr (.inl rfl)⟩,
    ringUses_zero slot.isLt]
/-- A TMA producer polls for reuse after one successful poll per prior generation. -/
theorem composed_reuse_count (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hd : d.site = .waitFree) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawFreeOff (d.block % 2)⟩
      (es.take i) = d.block / 2 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (pollLoc L g slot)) = d.block / 2
  obtain ⟨_, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, hd, begun]
  rw [hp, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [held, hd]

/-- Each preceding block has already published its raw-ready arrival. -/
theorem composed_prior_publications (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hb : begun d.site = true) :
    (d.block + (1 - slot.val)) / 2 ≤
      arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff slot.val⟩ (es.take i) := by
  obtain ⟨ha, _⟩ := counts_at hpre slot ht hs
  change _ ≤ count es i (.arrive (arriveLoc L g slot))
  rw [ha]
  simp [released, hb, ringUses]

/-- A raw-ready arrival follows the successful reuse poll of its buffer's generation. -/
theorem composed_publish_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hd : d.site = .rawReady) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawReadyOff (d.block % 2)⟩
        (es.take i) = d.block / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawFreeOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (arriveLoc L g slot)) = _ ∧ count es i (.poll (pollLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, hd, begun]
  rw [ha, hp, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, published, held, hd]

/-- Each gather is guarded by the current generation's successful reuse poll. -/
theorem composed_gather_reuse_count (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    {k : Fin 16} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.tma d))) (hd : d.site = .issue k) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg1Tma.rawFreeOff (d.block % 2)⟩
      (es.take i) = d.block / 2 + 1 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (pollLoc L g slot)) = _
  obtain ⟨_, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by simp [released, hd, begun]
  rw [hp, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaRawTrace
