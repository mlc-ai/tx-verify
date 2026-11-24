-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingWaitInitialization
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Lemmas.Order.OrderWaits

@[expose] public section

/-! # Actual softmax acquires observe initialized barrier phases -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem first_mask_event_is_wait {start : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hAnchor : FirstMaskAnchor P L X g start) (he : X.get (g, start) = some e) :
    (X.get (g, start)).bind Event.acc = none := by
  obtain ⟨d, hSite, _, hd⟩ := hAnchor
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX (hs g (Frame.lt_of_get hX he)).machine he hd
  obtain ⟨ok, hKind⟩ := RingEvents.maskReady_wait hpre hSite hFire
  rw [he]
  change e.acc = none
  cases e with
  | mk pc kind =>
    change kind = _ at hKind
    subst kind
    rfl

private theorem softmax_init_before_actual_wait {start q : Nat} {w : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hAnchor : FirstMaskAnchor P L X g start) (hq : start ≤ q)
    (hw : X.get (g, q) = some w) (entry : Fin 23) :
    ∃ init, X.MbInit init (initTable.loc L (ctaOf L g) entry) (initCount entry) ∧
      baseCausality L X init (g, q) := by
  have hStartLen : start < (X.tr g).length := hq.trans_lt (PTX.len_of_get hw)
  obtain ⟨e, he⟩ : ∃ e, X.get (g, start) = some e :=
    ⟨_, List.getElem?_eq_getElem hStartLen⟩
  have hNoAcc := first_mask_event_is_wait hpre hX hs hAnchor he
  obtain ⟨d, _, _, hd⟩ := hAnchor
  obtain ⟨init, hInit, hBefore⟩ :=
    completed_init_before_followed_role hpre hX hs he hd (by intro s h; cases h) entry
  refine ⟨init, hInit, ?_⟩
  rcases Nat.eq_or_lt_of_le hq with rfl | hLt
  · exact hBefore
  · exact hBefore.trans (.single (.inl (po_of_source_not_access rfl hLt
      (PTX.len_of_get hw) hNoAcc)))

/-- Object history of an actual successful mask poll, after its CTA initialization. -/
structure ActualMaskPhase (X : Execution) (m : Loc) (g q parity : Nat) where
  pos : Nat
  record : Record Ref
  before : State
  get : (X.objects m)[pos]? = some record
  source : record.id = .thread (g, q)
  clean : record.fault = none
  waited : record.reply.waited = some true
  state : stateBefore (X.objects m) pos = some before
  expected : before.expected = 32
  nextParity : before.phase % 2 ≠ parity % 2
  completion : record.reply.completed = if 0 < before.phase then some (before.phase - 1) else none

/-- Every successful mask poll from the concrete loop has the initialized phase record,
including polls after a dismissed numerical guard. -/
theorem actual_mask_phase {start q pc parity : Nat} {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hAnchor : FirstMaskAnchor P L X g start) (hq : start ≤ q)
    (hw : X.get (g, q) = some ⟨pc, .wait (ready L (ctaOf L g) slot) parity true true .cta⟩) :
    Nonempty (ActualMaskPhase X (ready L (ctaOf L g) slot) g q parity) := by
  let entry := readyEntry slot
  have hLoc := ready_entry_loc L (ctaOf L g) slot
  have hWait : X.get (g, q) = some
      ⟨pc, .wait (initTable.loc L (ctaOf L g) entry) parity true true .cta⟩ := hLoc ▸ hw
  obtain ⟨init, hInit, hBefore⟩ := softmax_init_before_actual_wait hpre hX hs hAnchor hq hw entry
  obtain ⟨i, r, s, hi, hid, hState, hExpect, hAction, hClean, hWaited⟩ :=
    wait_after_init_publication hpre hX hs entry hWait hInit hBefore
  rw [hLoc] at hi hState
  change s.expected = initCount (readyEntry slot) at hExpect
  rw [ready_entry_count] at hExpect
  obtain ⟨v, p, hv, hp, hParity, hCompletion⟩ :=
    (X.objects_checked hX (ready L (ctaOf L g) slot)).okPoll hi hWaited
  rw [hState] at hv
  obtain rfl := Option.some.inj hv
  rw [hAction] at hp
  obtain ⟨rfl, _⟩ := Action.pollParity.inj hp
  exact ⟨⟨i, r, s, hi, hid, hClean, hWaited, hState, hExpect, hParity, hCompletion⟩⟩

/-- Successive uses of a slot with opposite parity observe strictly increasing phases. -/
theorem ActualMaskPhase.phase_lt {m : Loc} {q q' n : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hOrder : q < q')
    (a : ActualMaskPhase X m g q (n % 2))
    (b : ActualMaskPhase X m g q' ((n + 1) % 2)) :
    a.before.phase < b.before.phase := by
  have hi := (hX.object_thread_index_iff a.get b.get a.source b.source).mpr hOrder
  obtain ⟨v, hv, hMon⟩ := (X.objects_checked hX m).phase_mono (objects_single_lifetime hX m) hi.le
    (List.getElem?_eq_some_iff.mp b.get).1.le a.state
  rw [b.state] at hv
  obtain rfl := Option.some.inj hv
  have hA := a.nextParity
  have hB := b.nextParity
  omega

/-- A completed iteration of the actual softmax loop, including its mask acquire. -/
structure ActualSoftmaxVisit (L : Launch) (X : Execution) (g start block : Nat) where
  releasePos : Nat
  released : Event
  fromStart : start ≤ releasePos
  getRelease : X.get (g, releasePos) = some released
  releaseSite : released.pc = Wg0.Site.validFree.pc
  ordinal : block =
    (((X.tr g).drop start).take (releasePos - start)).countP isProbabilityPublication
  pollPos : Nat
  pollFromStart : start ≤ pollPos
  pollBefore : pollPos < releasePos
  getPoll : X.get (g, pollPos) = some
    ⟨264, .wait (ready L (ctaOf L g) (indexSlot block)) (block / 4 % 2) true true .cta⟩
  earlierReleases : ∀ b < block, ∃ j, start ≤ j ∧ j < pollPos ∧ ∃ r,
    X.get (g, j) = some r ∧ r.pc = Wg0.Site.validFree.pc ∧
    b = (((X.tr g).drop start).take (j - start)).countP isProbabilityPublication

/-- Every block through this actual release has an observed mask poll in the same lane. -/
theorem actual_softmax_visits {start i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hStart : start ≤ i)
    (hAnchor : FirstMaskAnchor P L X g start) (hTag : e.pc = Wg0.Site.validFree.pc) :
    let last := (((X.tr g).drop start).take (i - start)).countP isProbabilityPublication
    ∀ b ≤ last, Nonempty (ActualSoftmaxVisit L X g start b) := by
  obtain ⟨last, hLast, _, _, q, hqStart, hq, hPoll, hHistory⟩ :=
    actual_softmax_return_ordinal hpre hX hs he hStart hAnchor hTag
  dsimp only
  rw [← hLast]
  intro b hb
  rcases Nat.eq_or_lt_of_le hb with rfl | hLt
  · exact ⟨⟨i, e, hStart, he, hTag, hLast, q, hqStart, hq, hPoll, hHistory⟩⟩
  · obtain ⟨j, hjStart, _, r, hr, hTag', hbCount⟩ := hHistory b hLt
    obtain ⟨visit, hCount, _, _, a, haStart, ha, hWait, hEarlier⟩ :=
      actual_softmax_return_ordinal hpre hX hs hr hjStart hAnchor hTag'
    rw [← hbCount] at hCount
    subst visit
    exact ⟨⟨j, r, hjStart, hr, hTag', hbCount, a, haStart, ha, hWait, hEarlier⟩⟩

/-- Blocks with larger ordinals have later acquires on the same lane. -/
theorem ActualSoftmaxVisit.poll_lt {start a b : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hLt : a < b)
    (r : ActualSoftmaxVisit L X g start a) (s : ActualSoftmaxVisit L X g start b) :
    r.pollPos < s.pollPos := by
  obtain ⟨j, hjStart, hj, e, he, hTag, hCount⟩ := s.earlierReleases a hLt
  have hEq : j = r.releasePos := by
    rcases lt_trichotomy j r.releasePos with h | h | h
    · have hh := actual_softmax_return_count_lt hX he r.getRelease hTag r.releaseSite hjStart h
      rw [← hCount, ← r.ordinal] at hh
      omega
    · exact h
    · have hh := actual_softmax_return_count_lt hX r.getRelease he r.releaseSite hTag r.fromStart h
      rw [← hCount, ← r.ordinal] at hh
      omega
  exact r.pollBefore.trans (hEq ▸ hj)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
