-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger

@[expose] public section

/-! # Index producer counts for each slot of the ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.IndexRingTrace

open PTX PTX.Flow Ledger
open Wg1Index (D)

private def held : Wg1Index.Site → Bool
  | .quad1 _ | .quad2 _ | .coord _ _ | .valid _ | .ready _ => true
  | _ => false

private def processed (d : D) : Nat :=
  d.block + if d.site = .barrier then 1 else 0

private def readyLoc (L : Launch) (g : Nat) (slot : Fin 4) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + Wg1Index.readyOff slot.val⟩

private def freeLoc (L : Launch) (g : Nat) (slot : Fin 4) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + Wg1Index.freeOff slot.val⟩

private def counts (L : Launch) (g : Nat) (slot : Fin 4) (d : D) (n : Cls → Nat) : Prop :=
  n (.arrive (readyLoc L g slot)) = ringUses 4 slot (processed d) ∧
    n (.poll (freeLoc L g slot)) = ringUses 4 slot (processed d) +
      if d.block % 4 = slot.val ∧ held d.site = true then 1 else 0

private theorem afterReady_processed (d : D) : processed (Wg1Index.afterReady d) = d.block + 1 := by
  unfold Wg1Index.afterReady
  dsimp only
  split_ifs <;> simp [processed]

private theorem afterReady_not_held (d : D) : held (Wg1Index.afterReady d).site = false := by
  unfold Wg1Index.afterReady
  dsimp only
  split_ifs <;> simp [held]

private theorem ready_count_event {L : Launch} {g : Nat} {slot : Fin 4}
    {d : D} {e : Event}
    (he : e.kind = .arrive
      ⟨.shared, g / L.block, L.sharedBase + Wg1Index.readyOff (d.block % 4)⟩ 0 1 true .cta) :
    arrivesOn (readyLoc L g slot) e = decide (d.block % 4 = slot.val) := by
  simp [arrivesOn, sourceArrive, he, readyLoc, Wg1Index.readyOff]

private theorem free_count_event {L : Launch} {g : Nat} {slot : Fin 4}
    {d : D} {e : Event} {ok : Bool}
    (he : e.kind = .wait
      ⟨.shared, g / L.block, L.sharedBase + Wg1Index.freeOff (d.block % 4)⟩
      (1 - d.block / 4 % 2) ok true .cta) :
    okPoll (freeLoc L g slot) e = (ok && decide (d.block % 4 = slot.val)) := by
  cases ok <;> simp [okPoll, sourceWaitSuccess, he, freeLoc, Wg1Index.freeOff]

variable {P : Params} {L : Launch} {mem0 : Mem0}

private theorem counts_step {g : Nat} {slot : Fin 4} {d d' : D} {e : Event} {n : Cls → Nat}
    {o : Option TState} (hpre : Pre P L mem0) (h : counts L g slot d n)
    (hf : (Wg1Index.code P L g).toMachine.Fired (some d) e o)
    (hn : Wg1Index.next P L g d e = some (some d')) :
    counts L g slot d' (bump n e) := by
  obtain ⟨harr, hwait⟩ := h
  simp only [counts, bump_apply, Cls.test, harr, hwait]
  cases hd : d.site <;> cases hk : e.kind <;>
    simp only [Wg1Index.next, Wg1Index.nextSite, hd, hk, Option.some.injEq, reduceCtorEq] at hn
  case lenOrig.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    cases P.extraTopkLenBase.isSome <;>
      simp [hd, hk, processed, held, arrivesOn, sourceArrive, okPoll, sourceWaitSuccess]
  case lenExtra.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    simp [hd, hk, processed, held, arrivesOn, sourceArrive, okPoll, sourceWaitSuccess]
  case pair.nc extra first hi ac bs =>
    cases extra <;> cases first <;> cases hi <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false] at hn
    all_goals split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    all_goals split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    all_goals cases hn
    all_goals simp [hd, hk, processed, held, Wg1Index.afterPairFirst, arrivesOn, sourceArrive,
      okPoll, sourceWaitSuccess]
    all_goals split <;> simp
  case waitFree.wait extra m p ok acq sc =>
    obtain ⟨ok', he⟩ := RingEvents.validFree_wait hpre hd hf
    have hok : ok = ok' := by rw [hk] at he; exact (Kind.wait.inj he).2.2.1
    subst ok'
    have hcount := free_count_event (slot := slot) (d := d) he
    cases ok <;> cases hn <;>
      simp [hd, hk, hcount, processed, held, arrivesOn, sourceArrive]
  case quad1.shfl =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    simp [hd, hk, processed, held, arrivesOn, sourceArrive, okPoll, sourceWaitSuccess]
  case quad2.shfl =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    simp [hd, hk, processed, held, arrivesOn, sourceArrive, okPoll, sourceWaitSuccess]
  case coord.wr extra hi a bs =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    cases hi <;> simp [hd, hk, processed, held, arrivesOn, sourceArrive, okPoll, sourceWaitSuccess]
    split <;> simp
  case valid.wr extra a bs =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    simp [hd, hk, processed, held, arrivesOn, sourceArrive, okPoll, sourceWaitSuccess]
  case ready.arrive extra m tx count release scope =>
    have he := RingEvents.validReady_arrive hpre hd hf
    have hcount := ready_count_event (slot := slot) (d := d) he
    cases hn
    have hd0 : processed d = d.block := by simp [processed, hd]
    rw [afterReady_not_held]
    simp [hk, hcount, hd0, held, afterReady_processed, ringUses_succ, okPoll, sourceWaitSuccess]


private theorem counts_at {g : Nat} (hpre : Pre P L mem0) (slot : Fin 4) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.index d))) : counts L g slot d (count es i) := by
  refine Ledger.index (fun _ _ _ _ => ring_prologue) ht (counts L g slot) (fun n hn => ?_)
    (fun _ _ _ _ _ hf hs hc => counts_step hpre hc hf hs) hs
  have hi : processed (Wg1Index.init P L g) = 0 ∧ held (Wg1Index.init P L g).site = false := by
    unfold Wg1Index.init Wg1Index.firstSite
    split_ifs <;> simp [processed, held]
  simp [counts, hi.1, hi.2, hn _ ⟨_, .inl rfl⟩, hn _ ⟨_, .inr (.inl rfl)⟩,
    ringUses_zero slot.isLt]

/-- At an index publication, the composed thread has published exactly the earlier uses of
the slot and has acquired the slot for this use. -/
theorem composed_ready_counts {g : Nat} (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    {extra : Bool} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.index d))) (hd : d.site = .ready extra) :
    arrivals ⟨.shared, g / L.block, L.sharedBase + Wg1Index.readyOff (d.block % 4)⟩
        (es.take i) = d.block / 4 ∧
      okPolls ⟨.shared, g / L.block, L.sharedBase + Wg1Index.freeOff (d.block % 4)⟩
        (es.take i) = d.block / 4 + 1 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (readyLoc L g slot)) = _ ∧ count es i (.poll (freeLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hd0 : processed d = d.block := by simp [processed, hd]
  rw [ha, hp, hd0, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, hd, held]

/-- The index lane has polled once in every earlier use of the current slot.
Its next free poll uses the opposite parity. -/
theorem composed_free_counts {g : Nat} (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    {extra : Bool} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.index d))) (hd : d.site = .waitFree extra) :
    let prior := okPolls ⟨.shared, g / L.block, L.sharedBase + Wg1Index.freeOff (d.block % 4)⟩
      (es.take i)
    prior = d.block / 4 ∧ 1 - d.block / 4 % 2 = (prior + 1) % 2 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (freeLoc L g slot)) = d.block / 4 ∧
    1 - d.block / 4 % 2 = (count es i (.poll (freeLoc L g slot)) + 1) % 2
  obtain ⟨_, hp⟩ := counts_at hpre slot ht hs
  have hd0 : processed d = d.block := by simp [processed, hd]
  rw [hp, hd0, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  simp only [hd, held, Bool.false_eq_true, and_false, ↓reduceIte, Nat.add_zero, true_and]
  omega

/-- The index lane's coordinate and mask writes are within the current slot use. -/
theorem composed_write_counts {g : Nat} (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.index d)))
    (hd : (∃ extra hi, d.site = .coord extra hi) ∨ ∃ extra, d.site = .valid extra) :
    arrivals ⟨.shared, g / L.block, L.sharedBase + Wg1Index.readyOff (d.block % 4)⟩
        (es.take i) = d.block / 4 ∧
      okPolls ⟨.shared, g / L.block, L.sharedBase + Wg1Index.freeOff (d.block % 4)⟩
        (es.take i) = d.block / 4 + 1 := by
  let slot : Fin 4 := ⟨d.block % 4, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (readyLoc L g slot)) = _ ∧ count es i (.poll (freeLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : processed d = d.block := by
    rcases hd with ⟨_, _, h⟩ | ⟨_, h⟩ <;> simp [processed, h]
  rw [ha, hp, hb, ringUses_here (S := 4) (s := slot) (k := d.block) rfl slot.isLt]
  rcases hd with ⟨_, _, h⟩ | ⟨_, h⟩ <;> simp [slot, h, held]

/-- Every reached index state counts completed publications for an arbitrary ring slot. -/
theorem composed_publications {g i : Nat} {es : List Event} {d : D} (hpre : Pre P L mem0)
    (slot : Fin 4) (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.index d))) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg1Index.readyOff slot.val⟩ (es.take i) =
      (d.block + (if d.site = .barrier then 1 else 0) + (3 - slot.val)) / 4 :=
  (counts_at hpre slot ht hs).1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.IndexRingTrace
