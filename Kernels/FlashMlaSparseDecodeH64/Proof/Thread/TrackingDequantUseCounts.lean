-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantTurns
import Lemmas.Flow.RunInv

@[expose] public section

/-! # Counts of raw-ring generations in an actual dequantizer trace -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

/-- Whether the projected event advances the selected raw slot's acquire count. -/
def rawAcquireOn (slot : Fin 2) : RawSignal → Bool
  | .acquire s _ => decide (s = slot.val)
  | .release _ => false

/-- Whether the projected event advances the selected raw slot's release count. -/
def rawReleaseOn (slot : Fin 2) : RawSignal → Bool
  | .acquire .. => false
  | .release s => decide (s = slot.val)

private def rawUses (slot : Fin 2) (block : Nat) : Nat := (block + (1 - slot.val)) / 2

private def rawHeld (slot : Fin 2) (block : Nat) (held : Bool) : Nat :=
  if held = true ∧ block % 2 = slot.val then 1 else 0

private theorem raw_uses_succ (slot : Fin 2) (block : Nat) :
    rawUses slot (block + 1) = rawUses slot block + if block % 2 = slot.val then 1 else 0 := by
  have hs := slot.isLt
  unfold rawUses
  split <;> omega

private theorem raw_turn_boundary (slot : Fin 2) {block : Nat} {held : Bool}
    {past future : List RawSignal} (ht : RawTurns block held (past ++ future)) :
    ∃ b h, RawTurns b h future ∧
      rawUses slot block + rawHeld slot block held + past.countP (rawAcquireOn slot) =
        rawUses slot b + rawHeld slot b h ∧
      rawUses slot block + past.countP (rawReleaseOn slot) = rawUses slot b := by
  induction past generalizing block held with
  | nil =>
    exact ⟨block, held, ht, by simp, by simp⟩
  | cons a past ih =>
    simp only [List.cons_append] at ht
    cases ht with
    | acquire hNext =>
      obtain ⟨b, h, hTail, hAcq, hRel⟩ := ih hNext
      refine ⟨b, h, hTail, ?_, ?_⟩
      · simp only [rawHeld, Bool.false_eq_true, false_and, ↓reduceIte, Nat.add_zero,
          List.countP_cons, rawAcquireOn, decide_eq_true_eq, true_and] at hAcq ⊢
        omega
      · simpa [rawReleaseOn] using hRel
    | release hNext =>
      obtain ⟨b, h, hTail, hAcq, hRel⟩ := ih hNext
      refine ⟨b, h, hTail, ?_, ?_⟩
      · simp only [raw_uses_succ, rawHeld, Bool.false_eq_true, false_and, ↓reduceIte,
          Nat.add_zero, List.countP_cons, rawAcquireOn, true_and] at hAcq ⊢
        omega
      · simp only [raw_uses_succ, List.countP_cons, rawReleaseOn, decide_eq_true_eq] at hRel ⊢
        omega

private theorem raw_turn_head {block : Nat} {held : Bool} {s : RawSignal} {es : List RawSignal}
    (h : RawTurns block held (s :: es)) :
    (held = false ∧ s = .acquire (block % 2) (block / 2 % 2)) ∨
      (held = true ∧ s = .release (block % 2)) := by
  cases h
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- Each projected acquire has the parity of its earlier successful acquires on this slot. -/
theorem raw_turn_acquire_parity {slot : Fin 2} {p : Nat} {past future : List RawSignal}
    (ht : RawTurns 0 false (past ++ .acquire slot.val p :: future)) :
    p % 2 = past.countP (rawAcquireOn slot) % 2 := by
  obtain ⟨b, h, hTail, hAcq, _⟩ := raw_turn_boundary slot ht
  rcases raw_turn_head hTail with ⟨rfl, he⟩ | ⟨_, he⟩
  · have hs := slot.isLt
    obtain ⟨hm, hp⟩ := RawSignal.acquire.inj he
    simp only [rawUses, rawHeld, Bool.false_eq_true, false_and, ↓reduceIte,
      Nat.zero_add, Nat.add_zero] at hAcq
    omega
  · cases he

/-- Each projected release has one more successful acquire than prior releases on its slot. -/
theorem raw_turn_release_count {slot : Fin 2} {past future : List RawSignal}
    (ht : RawTurns 0 false (past ++ .release slot.val :: future)) :
    past.countP (rawAcquireOn slot) = past.countP (rawReleaseOn slot) + 1 := by
  obtain ⟨b, h, hTail, hAcq, hRel⟩ := raw_turn_boundary slot ht
  rcases raw_turn_head hTail with ⟨_, he⟩ | ⟨rfl, he⟩
  · cases he
  · have hs := slot.isLt
    have hm := RawSignal.release.inj he
    simp only [rawHeld, Bool.false_eq_true, false_and, ↓reduceIte, true_and,
      hm, Nat.add_zero] at hAcq
    have hZero : rawUses slot 0 = 0 := by unfold rawUses; omega
    omega


private theorem acquire_predicate {L : Launch} {g : Nat} (slot : Fin 2) (e : Event) :
    ((rawSignal L g e).map (rawAcquireOn slot)).getD false =
      okPoll ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff slot.val⟩ e := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    cases hm : rawSignal L g e with
    | none => rw [hm] at h; cases h
    | some s =>
      cases s with
      | release => rw [hm] at h; cases h
      | acquire b p =>
        simp only [hm, Option.map_some, Option.getD_some, rawAcquireOn, decide_eq_true_eq] at h
        subst b
        obtain ⟨acq, scope, hk⟩ := raw_signal_acquire_iff.mp hm
        obtain ⟨pc, kind⟩ := e
        change kind = _ at hk
        subst kind
        simp [okPoll, sourceWaitSuccess]
  · intro h
    obtain ⟨p, acq, scope, hk⟩ := okPoll_wait_form h
    have hMark := raw_signal_acquire_iff.mpr ⟨acq, scope, hk⟩
    simp [hMark, rawAcquireOn]

private theorem release_predicate {L : Launch} {g : Nat} (slot : Fin 2) (e : Event) :
    ((rawSignal L g e).map (rawReleaseOn slot)).getD false =
      arrivesOn ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff slot.val⟩ e := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    cases hm : rawSignal L g e with
    | none => rw [hm] at h; cases h
    | some s =>
      cases s with
      | acquire => rw [hm] at h; cases h
      | release b =>
        simp only [hm, Option.map_some, Option.getD_some, rawReleaseOn, decide_eq_true_eq] at h
        subst b
        obtain ⟨tx, count, rel, scope, hk⟩ := raw_signal_release_iff.mp hm
        obtain ⟨pc, kind⟩ := e
        change kind = _ at hk
        subst kind
        simp [arrivesOn, sourceArrive]
  · intro h
    obtain ⟨tx, count, rel, scope, hk⟩ := arrivesOn_form h
    have hMark := raw_signal_release_iff.mpr ⟨tx, count, rel, scope, hk⟩
    simp [hMark, rawReleaseOn]

/-- Projecting the actual trace preserves the successful polls of a selected raw-ready slot. -/
theorem raw_signal_ready_count (L : Launch) (g : Nat) (slot : Fin 2) (es : List Event) :
    (es.filterMap (rawSignal L g)).countP (rawAcquireOn slot) =
      okPolls ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff slot.val⟩ es := by
  simp only [List.countP_filterMap, acquire_predicate, okPolls]

/-- Projecting the actual trace preserves the arrivals on a selected raw-free slot. -/
theorem raw_signal_free_count (L : Launch) (g : Nat) (slot : Fin 2) (es : List Event) :
    (es.filterMap (rawSignal L g)).countP (rawReleaseOn slot) =
      arrivals ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff slot.val⟩ es := by
  simp only [List.countP_filterMap, release_predicate, arrivals]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
