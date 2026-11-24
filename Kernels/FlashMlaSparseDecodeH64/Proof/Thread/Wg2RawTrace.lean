-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger

@[expose] public section

/-! # The dequantizer's raw-ring prefix counts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2RawTrace

open PTX PTX.Flow Ledger
open Wg2 (D)

private def held : Wg2.Site → Bool
  | .svDone | .scale .. | .raw .. | .store .. | .fence | .ready | .free => true
  | _ => false

/-- Number of raw blocks already released by this dequantization lane. -/
def released (d : D) : Nat :=
  match d.site with
  | .lenOrig | .lenExtra | .qUtccp => 0
  | .barrier => d.block + 1
  | _ => d.block

private def pollLoc (L : Launch) (g : Nat) (s : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff s.val⟩

private def arriveLoc (L : Launch) (g : Nat) (s : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff s.val⟩

private def counts (L : Launch) (g : Nat) (slot : Fin 2) (d : D) (n : Cls → Nat) : Prop :=
  n (.arrive (arriveLoc L g slot)) = ringUses 2 slot (released d) ∧
    n (.poll (pollLoc L g slot)) = ringUses 2 slot (released d) +
      if d.block % 2 = slot.val ∧ held d.site = true then 1 else 0

private theorem add_no_counts {L : Launch} {g : Nat} {slot : Fin 2}
    {e : Event} {n : Cls → Nat} {d d' : D}
    (hc : counts L g slot d n) (ha : arrivesOn (arriveLoc L g slot) e = false)
    (hp : okPoll (pollLoc L g slot) e = false)
    (hb : released d' = released d)
    (hh : (d'.block % 2 = slot.val ∧ held d'.site = true) ↔
      (d.block % 2 = slot.val ∧ held d.site = true)) :
    counts L g slot d' (bump n e) := by
  obtain ⟨h1, h2⟩ := hc
  simp [counts, Cls.test, h1, h2, ha, hp, hb, hh]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem entry_outside_raw {slot : Fin 2} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .qUtccp ∨ d.site = .svDone)
    (hf : (Wg2.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (arriveLoc L g slot) e = false ∧ okPoll (pollLoc L g slot) e = false := by
  obtain ⟨off, _, ok, hOff, hk⟩ := RingEvents.dequant_wait_object hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + off⟩ : Loc) ≠ pollLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    have hslot := slot.isLt
    rcases hOff with rfl | rfl <;>
      simp [pollLoc, Wg2.rawReadyOff, Wg2.qUtccpOff, Wg2.svDoneOff] at he <;> omega
  cases ok <;> simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem publication_outside_raw {slot : Fin 2} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hd : d.site = .ready)
    (hf : (Wg2.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (arriveLoc L g slot) e = false ∧ okPoll (pollLoc L g slot) e = false := by
  have hk := RingEvents.dequantReady_arrive hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + Wg2.dequantReadyOff (d.block % 2)⟩ : Loc) ≠
      arriveLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    have hslot := slot.isLt
    simp [arriveLoc, Wg2.rawFreeOff, Wg2.dequantReadyOff] at he
    omega
  simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem released_after_free {d : D} :
    released (Wg2.afterFree d) = d.block + 1 ∧ held (Wg2.afterFree d).site = false := by
  unfold Wg2.afterFree
  split <;> simp [released, held]

private theorem counts_step {slot : Fin 2} {d d' : D} {e : Event} {n : Cls → Nat}
    {o : Option TState} (hpre : Pre P L mem0) (hc : counts L g slot d n)
    (hf : (Wg2.code P L g).toMachine.Fired (some d) e o) (hn : Wg2.next P L g d e = some (some d'))
    :
    counts L g slot d' (bump n e) := by
  cases hd : d.site <;> cases hk : e.kind <;>
    simp only [Wg2.next, Wg2.nextSite, hd, hk, Option.some.injEq, reduceCtorEq] at hn
  case lenOrig.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · unfold Wg2.lenOrigNext
      split_ifs <;> simp [released, hd]
    · unfold Wg2.lenOrigNext
      split_ifs <;> simp [held, hd]
  case lenExtra.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · simp [released, hd, Wg2.lenExtraNext]
    · simp [held, hd, Wg2.lenExtraNext]
  case qUtccp.wait m p ok acq sc =>
    have h := entry_outside_raw (slot := slot) hpre (.inl hd) hf
    have hinv : Wg2.Inv P L g d := hf.choose_spec.1.2
    have hzero := hinv.qUtccpBlock hd
    cases ok <;> cases hn <;> apply add_no_counts hc h.1 h.2
    all_goals simp [released, held, hd, hzero]
  case rawReady.wait m p ok acq sc =>
    obtain ⟨ok', he⟩ := RingEvents.rawReady_wait hpre hd hf
    have hok : ok = ok' := by rw [hk] at he; exact (Kind.wait.inj he).2.2.1
    subst ok'
    have hep : okPoll (pollLoc L g slot) e = (ok && decide (d.block % 2 = slot.val)) := by
      cases ok <;> simp [okPoll, sourceWaitSuccess, he, pollLoc, Wg2.rawReadyOff, ctaOf]
    obtain ⟨h1, h2⟩ := hc
    cases ok <;> cases hn <;> simp [counts, Cls.test, h1, h2, hep, released, held, hd, hk,
      arrivesOn, sourceArrive]
  case svDone.wait m p ok acq sc =>
    have h := entry_outside_raw (slot := slot) hpre (.inr hd) hf
    cases ok <;> cases hn <;> apply add_no_counts hc h.1 h.2
    all_goals simp [released, held, hd]
  case scale.rd =>
    repeat' first
      | split at hn
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · unfold Wg2.afterScale
      split_ifs <;> simp [released, hd]
    · unfold Wg2.afterScale
      split_ifs <;> simp [held, hd]
  case raw.rd =>
    repeat' first
      | split at hn
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    all_goals cases hn
    all_goals
      apply add_no_counts hc (by simp [arrivesOn, sourceArrive, hk])
        (by simp [okPoll, sourceWaitSuccess, hk])
    all_goals unfold Wg2.afterRaw
    all_goals split_ifs
    all_goals simp [released, held, hd]
  case store.wr =>
    repeat' first
      | split at hn
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    all_goals cases hn
    all_goals
      apply add_no_counts hc (by simp [arrivesOn, sourceArrive, hk])
        (by simp [okPoll, sourceWaitSuccess, hk])
    all_goals unfold Wg2.afterStore
    all_goals split_ifs <;> simp [released, held, hd]
  case fence.fenceProxy =>
    cases hn
    apply add_no_counts hc (by simp [arrivesOn, sourceArrive, hk])
      (by simp [okPoll, sourceWaitSuccess, hk])
    · simp [released, hd]
    · simp [held, hd]
  case ready.arrive =>
    have h := publication_outside_raw (slot := slot) hpre hd hf
    cases hn
    apply add_no_counts hc h.1 h.2
    all_goals simp [released, held, hd]
  case free.arrive =>
    have he := RingEvents.rawFree_arrive hpre hd hf
    have ha : arrivesOn (arriveLoc L g slot) e = decide (d.block % 2 = slot.val) := by
      simp [arrivesOn, sourceArrive, he, arriveLoc, Wg2.rawFreeOff, ctaOf]
    cases hn
    obtain ⟨h1, h2⟩ := hc
    simp only [counts, bump_apply, Cls.test]
    simp only [h1, h2, ha, released_after_free.1, released_after_free.2]
    simp [ringUses_succ slot.isLt, released, held, hd, hk, okPoll, sourceWaitSuccess]

private theorem counts_at (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) : counts L g slot d (count es i) := by
  refine Ledger.wg2 (fun _ _ _ _ => ring_prologue) ht (counts L g slot) (fun n hn => ?_)
    (fun _ _ _ _ _ hf hs hc => counts_step hpre hc hf hs) hs
  unfold Wg2.init Wg2.firstSite
  split_ifs <;> simp [counts, released, held, hn _ ⟨_, .inl rfl⟩, hn _ ⟨_, .inr (.inl rfl)⟩,
    ringUses_zero slot.isLt]
/-- Each completed raw block contributes a release on its own slot. -/
theorem composed_release_count (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff slot.val⟩ (es.take i) =
      (released d + (1 - slot.val)) / 2 :=
  (counts_at hpre slot ht hs).1

/-- A raw-ready poll follows exactly one successful poll per earlier generation of this buffer. -/
theorem composed_raw_ready_count (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) (hd : d.site = .rawReady) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff (d.block % 2)⟩
      (es.take i) = d.block / 2 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (pollLoc L g slot)) = _
  obtain ⟨_, hp⟩ := counts_at hpre slot ht hs
  rw [hp, show released d = d.block by simp [released, hd],
    ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [held, hd]

/-- The dequantizer releases the buffer only after its successful ready poll for that use. -/
theorem composed_raw_free_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) (hd : d.site = .free) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff (d.block % 2)⟩
        (es.take i) = d.block / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (arriveLoc L g slot)) = _ ∧ count es i (.poll (pollLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  rw [ha, hp, show released d = d.block by simp [released, hd],
    ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]

/-- At raw-slot release, every generation through this block has acquired both raw rings as used. -/
theorem composed_raw_polls_through_free (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event}
    {i : Nat} {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) (hd : d.site = .free) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff slot.val⟩ (es.take i) =
      (d.block + 1 + (1 - slot.val)) / 2 := by
  change count es i (.poll (pollLoc L g slot)) = ringUses 2 slot (d.block + 1)
  obtain ⟨_, h⟩ := counts_at hpre slot ht hs
  rw [h, ringUses_succ slot.isLt, show released d = d.block by simp [released, hd]]
  simp [held, hd]

/-- The raw-byte and scale-byte reads of the dequantizer. -/
def RawAccess (s : Wg2.Site) : Prop :=
  (∃ r j, s = .scale r j) ∨ ∃ r k, s = .raw r k

/-- Every raw access is between the generation's ready acquire and free release. -/
theorem composed_raw_access_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : Wg2.D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) (hd : RawAccess d.site) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff (d.block % 2)⟩
        (es.take i) = d.block / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (arriveLoc L g slot)) = _ ∧ count es i (.poll (pollLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  have hb : released d = d.block := by
    rcases hd with ⟨r, j, h⟩ | ⟨r, k, h⟩ <;> simp [released, h]
  rw [ha, hp, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  rcases hd with ⟨r, j, h⟩ | ⟨r, k, h⟩ <;> simp [slot, held, h]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2RawTrace
