-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingProducerReuse
import Lemmas.Order.CausalObjectWaitCount

public section

/-! # Actual checked free-slot phases of the index producer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The free-slot poll at an index use, together with its checked object record. -/
structure ProducerFreePoll (X : Execution) (g i use : Nat) (m : Loc) where
  pos : Nat
  tag : Nat
  index : Nat
  record : Record Ref
  before : State
  pos_lt : pos < i
  event : X.get (g, pos) = some ⟨tag, .wait m (1 - use % 2) true true .cta⟩
  count : PTX.Flow.okPolls m ((X.tr g).take pos) = use
  get_record : (X.objects m)[index]? = some record
  id : record.id = .thread (g, pos)
  state : stateBefore (X.objects m) index = some before
  expected : before.expected = 129
  clean : record.fault = none
  response : record.reply.waited = some true
  parity : before.phase % 2 = use % 2
  observed : observedAt (X.objects m) index =
    if 0 < before.phase then some (before.phase - 1) else none

private theorem producer_free_poll_record_of_event {g i use q tag : Nat} {z : Wg1Index.D}
    {slot : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hq : q < i)
    (hWait : X.get (g, q) = some
      ⟨tag, .wait (free L (ctaOf L g) slot) (1 - use % 2) true true .cta⟩)
    (hz : Frame.stateAt (Machine.code P L) X g q = some (some (.index z)))
    (hCount : okPolls (free L (ctaOf L g) slot) ((X.tr g).take q) = use) :
    Nonempty (ProducerFreePoll X g i use (free L (ctaOf L g) slot)) := by
  let m := free L (ctaOf L g) slot
  let entry := freeEntry slot
  have hm : initTable.loc L (ctaOf L g) entry = m :=
    free_entry_loc L (ctaOf L g) slot
  have hAtEntry : X.get (g, q) = some
      ⟨tag, .wait (initTable.loc L (ctaOf L g) entry) (1 - use % 2) true true .cta⟩ :=
    hm ▸ hWait
  obtain ⟨idx, r, before, hi, hId, hBefore, hExp, hAct, hClean, hResponse⟩ :=
    wait_after_table_init hpre hX hs hz (by intro s h; cases h) entry hAtEntry
  rw [hm] at hi hBefore
  change before.expected = initCount entry at hExp
  rw [free_entry_count] at hExp
  obtain ⟨_, parity, hState', hAct', hNe, hCompletion⟩ :=
    (X.objects_checked hX m).okPoll hi hResponse
  rw [hBefore] at hState'
  obtain rfl := Option.some.inj hState'
  rw [hAct] at hAct'
  obtain ⟨rfl, _⟩ := Action.pollParity.inj hAct'
  have hObs : observedAt (X.objects m) idx =
      if 0 < before.phase then some (before.phase - 1) else none := by
    simp only [observedAt, hi, Option.bind_some, hCompletion]
  exact ⟨⟨q, tag, idx, r, before, hq, hWait, hCount, hi, hId, hBefore, hExp, hClean,
    hResponse, by omega, hObs⟩⟩

/-- A followed producer publication has actual free waits through its publication generation. -/
theorem producer_free_poll_record {g i use : Nat} {d : Wg1Index.D} {e : Event} {extra : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hReady : d.site = .ready extra) (hUse : use ≤ d.block / 4) :
    Nonempty (ProducerFreePoll X g i use (free L (ctaOf L g) (indexSlot d.block))) := by
  obtain ⟨q, tag, z, _, hq, hWait, hz, _, _, hCount⟩ :=
    producer_free_acquire hpre hX (hs g (Frame.lt_of_get hX he)).machine he hState hReady hUse
  exact producer_free_poll_record_of_event hpre hX hs hq hWait hz hCount

/-- Each index store follows an actual free poll from its own use or an earlier one. -/
theorem index_store_free_poll_record {g i use : Nat} {d : Wg1Index.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hStore : (∃ extra high, d.site = .coord extra high) ∨ ∃ extra, d.site = .valid extra)
    (hUse : use ≤ d.block / 4) :
    Nonempty (ProducerFreePoll X g i use (free L (ctaOf L g) (indexSlot d.block))) := by
  obtain ⟨q, tag, z, _, hq, hWait, hz, _, _, hCount⟩ :=
    index_store_free_acquire hpre hX (hs g (Frame.lt_of_get hX he)).machine
      he hState hStore hUse
  exact producer_free_poll_record_of_event hpre hX hs hq hWait hz hCount

/-- Consecutive waits have strictly increasing phases in the checked history. -/
theorem ProducerFreePoll.phase_lt_succ {g i use : Nat} {m : Loc}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (a : ProducerFreePoll X g i use m) (b : ProducerFreePoll X g i (use + 1) m) :
    a.before.phase < b.before.phase := by
  have hPos : a.pos < b.pos := by
    by_contra! hLe
    have hMono := countP_take_mono (PTX.Flow.okPoll m) (X.tr g) hLe
    change PTX.Flow.okPolls m ((X.tr g).take b.pos) ≤ PTX.Flow.okPolls m ((X.tr g).take a.pos)
      at hMono
    rw [a.count, b.count] at hMono
    omega
  have hIdx := (hX.object_thread_index_iff a.get_record b.get_record a.id b.id).2 hPos
  obtain ⟨st, hs, hMono⟩ := (X.objects_checked hX m).phase_mono
    (objects_single_lifetime hX m) hIdx.le (List.getElem?_eq_some_iff.mp b.get_record).1.le a.state
  rw [b.state] at hs
  obtain rfl := Option.some.inj hs
  have ha := a.parity
  have hb := b.parity
  omega

private theorem producer_free_phase_lower_of_polls {g i use : Nat} {m : Loc}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hPolls : ∀ k ≤ use, Nonempty (ProducerFreePoll X g i k m))
    (r : ProducerFreePoll X g i use m) : use ≤ r.before.phase := by
  induction use with
  | zero => omega
  | succ n ih =>
    obtain ⟨prev⟩ := hPolls n (Nat.le_succ n)
    have hLower := ih (fun k hk => hPolls k (hk.trans (Nat.le_succ n))) prev
    have hLt := prev.phase_lt_succ hX r
    omega

/-- Each noninitial use observes a completed phase, with no repeated phase along a producer. -/
theorem producer_free_phase_lower {g i use : Nat} {d : Wg1Index.D} {e : Event} {extra : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hReady : d.site = .ready extra) (hUse : use ≤ d.block / 4)
    (r : ProducerFreePoll X g i use (free L (ctaOf L g) (indexSlot d.block))) :
    use ≤ r.before.phase :=
  producer_free_phase_lower_of_polls hX
    (fun _ hk => producer_free_poll_record hpre hX hs he hState hReady (hk.trans hUse)) r

/-- An index store in use `n` requires a poll through at least phase `n`. -/
theorem index_store_free_phase_lower {g i use : Nat} {d : Wg1Index.D} {e : Event}
    (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hStore : (∃ extra high, d.site = .coord extra high) ∨ ∃ extra, d.site = .valid extra)
    (hUse : use ≤ d.block / 4)
    (r : ProducerFreePoll X g i use (free L (ctaOf L g) (indexSlot d.block))) :
    use ≤ r.before.phase :=
  producer_free_phase_lower_of_polls hX
    (fun _ hk => index_store_free_poll_record hpre hX hs he hState hStore (hk.trans hUse)) r

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
