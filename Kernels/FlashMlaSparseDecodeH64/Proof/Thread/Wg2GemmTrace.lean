-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger

@[expose] public section

/-! # The dequantizer's GEMM-ring prefix counts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2GemmTrace

open PTX PTX.Flow Ledger
open Wg2 (D)

private def held : Wg2.Site → Bool
  | .scale .. | .raw .. | .store .. | .fence | .ready => true
  | _ => false

/-- The number of dequantization blocks published before this state. -/
def publishedBlocks (d : D) : Nat :=
  match d.site with
  | .lenOrig | .lenExtra | .qUtccp => 0
  | .free | .barrier => d.block + 1
  | _ => d.block

private def pollLoc (L : Launch) (g : Nat) (s : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg2.svDoneOff s.val⟩

private def arriveLoc (L : Launch) (g : Nat) (s : Fin 2) : Loc :=
  ⟨.shared, ctaOf L g, L.sharedBase + Wg2.dequantReadyOff s.val⟩

private def counts (L : Launch) (g : Nat) (slot : Fin 2) (d : D) (n : Cls → Nat) : Prop :=
  n (.arrive (arriveLoc L g slot)) = ringUses 2 slot (publishedBlocks d) ∧
    n (.poll (pollLoc L g slot)) = ringUses 2 slot (publishedBlocks d) +
      if d.block % 2 = slot.val ∧ held d.site = true then 1 else 0

private theorem add_no_counts {L : Launch} {g : Nat} {slot : Fin 2}
    {e : Event} {n : Cls → Nat} {d d' : D}
    (hc : counts L g slot d n) (ha : arrivesOn (arriveLoc L g slot) e = false)
    (hp : okPoll (pollLoc L g slot) e = false)
    (hb : publishedBlocks d' = publishedBlocks d)
    (hh : (d'.block % 2 = slot.val ∧ held d'.site = true) ↔
      (d.block % 2 = slot.val ∧ held d.site = true)) :
    counts L g slot d' (bump n e) := by
  obtain ⟨h1, h2⟩ := hc
  simp [counts, Cls.test, h1, h2, ha, hp, hb, hh]

private theorem wait_outside_reuse {L : Launch} {g off parity : Nat}
    {slot : Fin 2} {e : Event} {ok : Bool}
    (hoff : off < 222936)
    (hk : e.kind = .wait ⟨.shared, g / L.block, L.sharedBase + off⟩ parity ok true .cta) :
    arrivesOn (arriveLoc L g slot) e = false ∧ okPoll (pollLoc L g slot) e = false := by
  have hne : (⟨.shared, g / L.block, L.sharedBase + off⟩ : Loc) ≠ pollLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    simp [pollLoc, Wg2.svDoneOff] at he
    omega
  cases ok <;> simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem free_outside_ready {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {slot : Fin 2} {d : D} {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hd : d.site = .free) (hf : (Wg2.code P L g).toMachine.Fired (some d) e o) :
    arrivesOn (arriveLoc L g slot) e = false ∧ okPoll (pollLoc L g slot) e = false := by
  have hk := RingEvents.rawFree_arrive hpre hd hf
  have hne : (⟨.shared, g / L.block, L.sharedBase + Wg2.rawFreeOff (d.block % 2)⟩ : Loc) ≠
      arriveLoc L g slot := by
    intro same
    have he := congrArg Loc.addr same
    have hslot := slot.isLt
    simp [arriveLoc, Wg2.rawFreeOff, Wg2.dequantReadyOff] at he
    omega
  simp [arrivesOn, sourceArrive, okPoll, sourceWaitSuccess, hk, hne]

private theorem released_after_free {d : D} :
    publishedBlocks (Wg2.afterFree d) = d.block + 1 ∧ held (Wg2.afterFree d).site = false := by
  unfold Wg2.afterFree
  split <;> simp [publishedBlocks, held]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem counts_step {slot : Fin 2} {d d' : D} {e : Event} {n : Cls → Nat}
    {o : Option TState} (hpre : Pre P L mem0)
    (hf : (Wg2.code P L g).toMachine.Fired (some d) e o) (hn : Wg2.next P L g d e = some (some d'))
    (hc : counts L g slot d n) : counts L g slot d' (bump n e) := by
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
      split_ifs <;> simp [publishedBlocks, hd]
    · unfold Wg2.lenOrigNext
      split_ifs <;> simp [held, hd]
  case lenExtra.nc =>
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    split at hn <;> try (simp only [Option.some.injEq, reduceCtorEq] at hn)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · simp [publishedBlocks, hd, Wg2.lenExtraNext]
    · simp [held, hd, Wg2.lenExtraNext]
  case qUtccp.wait m p ok acq sc =>
    obtain ⟨_, he⟩ := RingEvents.dequant_wait_exact hpre (.inl hd) hf
    simp only [hd, ↓reduceIte] at he
    have h := wait_outside_reuse (slot := slot) (by decide : Wg2.qUtccpOff < 222936) he
    have hinv : Wg2.Inv P L g d := hf.choose_spec.1.2
    have hzero := hinv.qUtccpBlock hd
    cases ok <;> cases hn <;> apply add_no_counts hc h.1 h.2
    all_goals simp [publishedBlocks, held, hd, hzero]
  case rawReady.wait m p ok acq sc =>
    obtain ⟨_, he⟩ := RingEvents.rawReady_wait hpre hd hf
    have h := wait_outside_reuse (slot := slot)
      (by unfold Wg2.rawReadyOff; omega : Wg2.rawReadyOff (d.block % 2) < 222936) he
    cases ok <;> cases hn <;> apply add_no_counts hc h.1 h.2
    all_goals simp [publishedBlocks, held, hd]
  case svDone.wait m p ok acq sc =>
    obtain ⟨ok', he⟩ := RingEvents.dequant_wait_exact hpre (.inr hd) hf
    simp [hd] at he
    have hok : ok = ok' := by rw [hk] at he; exact (Kind.wait.inj he).2.2.1
    subst ok'
    have hep : okPoll (pollLoc L g slot) e = (ok && decide (d.block % 2 = slot.val)) := by
      cases ok <;> simp [okPoll, sourceWaitSuccess, he, pollLoc, Wg2.svDoneOff, ctaOf]
    obtain ⟨h1, h2⟩ := hc
    cases ok <;> cases hn <;>
      simp [counts, Cls.test, h1, h2, hep, publishedBlocks, held, hd, hk, arrivesOn, sourceArrive]
  case scale.rd =>
    repeat' first
      | split at hn
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    cases hn
    apply add_no_counts hc
    · simp [arrivesOn, sourceArrive, hk]
    · simp [okPoll, sourceWaitSuccess, hk]
    · unfold Wg2.afterScale
      split_ifs <;> simp [publishedBlocks, hd]
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
    all_goals simp [publishedBlocks, held, hd]
  case store.wr =>
    repeat' first
      | split at hn
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    all_goals cases hn
    all_goals
      apply add_no_counts hc (by simp [arrivesOn, sourceArrive, hk])
        (by simp [okPoll, sourceWaitSuccess, hk])
    all_goals unfold Wg2.afterStore
    all_goals split_ifs <;> simp [publishedBlocks, held, hd]
  case fence.fenceProxy =>
    cases hn
    apply add_no_counts hc (by simp [arrivesOn, sourceArrive, hk])
      (by simp [okPoll, sourceWaitSuccess, hk])
    · simp [publishedBlocks, hd]
    · simp [held, hd]
  case ready.arrive =>
    have he := RingEvents.dequantReady_arrive hpre hd hf
    have ha : arrivesOn (arriveLoc L g slot) e = decide (d.block % 2 = slot.val) := by
      simp [arrivesOn, sourceArrive, he, arriveLoc, Wg2.dequantReadyOff, ctaOf]
    cases hn
    obtain ⟨h1, h2⟩ := hc
    simp [counts, Cls.test, h1, h2, ha, ringUses_succ slot.isLt, publishedBlocks, held, hd, hk,
      okPoll, sourceWaitSuccess]
  case free.arrive =>
    have h := free_outside_ready (slot := slot) hpre hd hf
    cases hn
    apply add_no_counts hc h.1 h.2
    · rw [(released_after_free (d := d)).1]
      simp [publishedBlocks, hd]
    · rw [(released_after_free (d := d)).2]
      simp [held, hd]

private theorem counts_at (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) : counts L g slot d (count es i) := by
  refine Ledger.wg2 (fun _ _ _ _ => ring_prologue) ht (counts L g slot) (fun n hn => ?_)
    (fun _ _ _ _ _ hf hs => counts_step hpre hf hs) hs
  have := slot.isLt
  unfold Wg2.init Wg2.firstSite
  split_ifs <;> simp [counts, publishedBlocks, held, hn _ ⟨_, .inl rfl⟩, hn _ ⟨_, .inr (.inl rfl)⟩,
    ringUses_zero slot.isLt]

/-- Each slot receives exactly one dequantization publication per completed block on that slot. -/
theorem dequant_arrivals_of_state (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event} {i : Nat}
    {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg2.dequantReadyOff slot.val⟩ (es.take i) =
      (publishedBlocks d + (1 - slot.val)) / 2 :=
  (counts_at hpre slot ht hs).1

/-- There is one successful reuse poll per earlier generation of the dequantized buffer. -/
theorem composed_reuse_count (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) (hd : d.site = .svDone) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.svDoneOff (d.block % 2)⟩
      (es.take i) = d.block / 2 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.poll (pollLoc L g slot)) = _
  obtain ⟨_, hp⟩ := counts_at hpre slot ht hs
  rw [hp, show publishedBlocks d = d.block by simp [publishedBlocks, hd],
    ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [held, hd]

/-- The raw release follows the PV-reuse polls of every slot used through this block. -/
theorem composed_reuse_polls_through_free (hpre : Pre P L mem0) (slot : Fin 2) {es : List Event}
    {i : Nat} {d : D} (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) (hd : d.site = .free) :
    okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.svDoneOff slot.val⟩ (es.take i) =
      (d.block + 1 + (1 - slot.val)) / 2 := by
  change count es i (.poll (pollLoc L g slot)) = ringUses 2 slot (d.block + 1)
  obtain ⟨_, h⟩ := counts_at hpre slot ht hs
  rw [h, show publishedBlocks d = d.block + 1 by simp [publishedBlocks, hd]]
  simp [held, hd]

/-- The dequantizer publishes after the reuse acquire for this buffer use. -/
theorem composed_publication_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) (hd : d.site = .ready) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg2.dequantReadyOff (d.block % 2)⟩
        (es.take i) = d.block / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.svDoneOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (arriveLoc L g slot)) = _ ∧ count es i (.poll (pollLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  rw [ha, hp, show publishedBlocks d = d.block by simp [publishedBlocks, hd],
    ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]

/-- Every dequantized write follows the reuse acquire and precedes publication for the slot use. -/
theorem composed_write_counts (hpre : Pre P L mem0) {es : List Event} {i : Nat} {d : Wg2.D}
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init es)
    (hs : (Machine.machine P L g).after (Machine.machine P L g).init (es.take i) =
      some (some (.wg2 d))) (hd : ∃ r k, d.site = .store r k) :
    arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg2.dequantReadyOff (d.block % 2)⟩
        (es.take i) = d.block / 2 ∧
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.svDoneOff (d.block % 2)⟩
        (es.take i) = d.block / 2 + 1 := by
  let slot : Fin 2 := ⟨d.block % 2, Nat.mod_lt _ (by decide)⟩
  change count es i (.arrive (arriveLoc L g slot)) = _ ∧ count es i (.poll (pollLoc L g slot)) = _
  obtain ⟨ha, hp⟩ := counts_at hpre slot ht hs
  obtain ⟨r, k, hd⟩ := hd
  have hb : publishedBlocks d = d.block := by simp [publishedBlocks, hd]
  rw [ha, hp, hb, ringUses_here (S := 2) (s := slot) (k := d.block) rfl slot.isLt]
  simp [slot, held, hd]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2GemmTrace
