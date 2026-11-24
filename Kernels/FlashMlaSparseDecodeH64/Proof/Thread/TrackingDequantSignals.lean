-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantBody
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantBarrierAddress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

@[expose] public section

/-! # Successful raw acquires and raw releases in the actual dequantizer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- Only the two raw-ring operations which advance the consumer's use count. -/
inductive RawSignal where
  | acquire (slot parity : Nat)
  | release (slot : Nat)

/-- Match a location to one of the two slots in a raw-ring object family. -/
def rawSlotAt (loc : Nat → Loc) (m : Loc) : Option Nat :=
  if m = loc 0 then some 0 else if m = loc 1 then some 1 else none

private theorem raw_slot_at_iff {loc : Nat → Loc} {m : Loc}
    (hDifferent : loc 0 ≠ loc 1) (slot : Fin 2) :
    rawSlotAt loc m = some slot.val ↔ m = loc slot.val := by
  fin_cases slot
  · by_cases hFirst : m = loc 0
    · simp [rawSlotAt, hFirst]
    · by_cases hSecond : m = loc 1 <;> simp [rawSlotAt, hFirst, hSecond]
  · by_cases hFirst : m = loc 0
    · simp [rawSlotAt, hFirst, hDifferent]
    · by_cases hSecond : m = loc 1 <;> simp [rawSlotAt, hFirst, hSecond, hDifferent.symm]

/-- Project successful raw-ready polls and raw-free arrivals from an actual trace. -/
def rawSignal (L : Launch) (g : Nat) (e : Event) : Option RawSignal :=
  let atOffset off := (⟨.shared, ctaOf L g, L.sharedBase + off⟩ : Loc)
  match e.kind with
  | .wait m p true _ _ =>
    (rawSlotAt (atOffset ∘ Wg2.rawReadyOff) m).map fun s => .acquire s p
  | .arrive m _ _ _ _ =>
    (rawSlotAt (atOffset ∘ Wg2.rawFreeOff) m).map RawSignal.release
  | _ => none

private theorem wait_candidates {pc : Nat} (hTag : pc ∈ Flow.mbarWait.toList)
    (hLower : 2680 ≤ pc) : pc = 2684 := by
  have h : Flow.mbarWait.toList.all (fun p => decide (2680 ≤ p → p = 2684)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h pc hTag) hLower

private theorem arrive_candidates {pc : Nat} (hTag : pc ∈ Flow.mbarArrive.toList)
    (hLower : 2680 ≤ pc) : pc = 3597 ∨ pc = 3599 := by
  have h : Flow.mbarArrive.toList.all
      (fun p => decide (2680 ≤ p → p = 3597 ∨ p = 3599)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h pc hTag) hLower

/-- Between the successful raw poll and the release, no internal event advances the raw ring.
The same classification excludes all events in the role's epilogue. -/
theorem raw_signal_silent {i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, i) = some e) (hLower : 2680 ≤ e.pc) (hNotFree : e.pc ≠ 3599) :
    rawSignal L g e = none := by
  unfold rawSignal
  split
  · rename_i m p acq scope hk
    have hPc := wait_candidates (RingSourceSites.actual_wait_pc hX he hk) hLower
    obtain ⟨b, rfl⟩ := actual_dequant_sv_poll hpre hX he hPc hk
    have bound := b.isLt
    have hDifferent (s : Nat) (hs : s < 2) :
        (⟨.shared, ctaOf L g, L.sharedBase + Wg2.svDoneOff b.val⟩ : Loc) ≠
          ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff s⟩ := by
      intro he
      have ha := congrArg Loc.addr he
      change L.sharedBase + (222936 + 8 * b.val) =
        L.sharedBase + (222808 + 8 * s) at ha
      omega
    simp only [rawSlotAt, Function.comp_apply, ite_eq_right (hDifferent 0 (by decide)),
      ite_eq_right (hDifferent 1 (by decide)), Option.map_none]
  · rename_i m tx count rel scope hk
    have hPc := arrive_candidates (RingSourceSites.actual_arrive_pc hX he hk) hLower
    rcases actual_dequant_barrier_address hpre hX he hPc hk with
      ⟨_, b, hKind⟩ | ⟨hFree, _, _⟩
    · obtain ⟨rfl, _, _, _, _⟩ := Kind.arrive.inj (hk.symm.trans hKind)
      have hDifferent (s : Nat) :
          (⟨.shared, ctaOf L g, L.sharedBase + (222792 + 8 * b.val)⟩ : Loc) ≠
            ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff s⟩ := by
        intro he
        have ha := congrArg Loc.addr he
        have hb := b.isLt
        change L.sharedBase + (222792 + 8 * b.val) =
          L.sharedBase + (222824 + 8 * s) at ha
        omega
      simp only [rawSlotAt, Function.comp_apply, ite_eq_right (hDifferent 0),
        ite_eq_right (hDifferent 1), Option.map_none]
    · exact (hNotFree hFree).elim
  · rfl

/-- The actual slot address projects to the corresponding raw-acquire marker. -/
theorem raw_signal_wait {block : Nat} {ok : Bool} :
    rawSignal L g ⟨2677, .wait
      ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff (block % 2)⟩
      (block / 2 % 2) ok true .cta⟩ =
      if ok then some (.acquire (block % 2) (block / 2 % 2)) else none := by
  cases ok
  · rfl
  · have hs : block % 2 = 0 ∨ block % 2 = 1 := by omega
    rcases hs with h | h
    · simp [rawSignal, rawSlotAt, h]
    · simp [rawSignal, rawSlotAt, h, Wg2.rawReadyOff]

/-- The actual unit arrival projects to the corresponding raw-release marker. -/
theorem raw_signal_release {block : Nat} {e : Event}
    (hk : e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff (block % 2)⟩
      0 1 true .cta) :
    rawSignal L g e = some (.release (block % 2)) := by
  have hs : block % 2 = 0 ∨ block % 2 = 1 := by omega
  rcases hs with h | h
  · simp [rawSignal, rawSlotAt, hk, h]
  · simp [rawSignal, rawSlotAt, hk, h, Wg2.rawFreeOff]

private theorem raw_slot_addresses_ne (off : Nat) :
    (⟨.shared, ctaOf L g, L.sharedBase + off⟩ : Loc) ≠
      ⟨.shared, ctaOf L g, L.sharedBase + (off + 8)⟩ := by
  intro h
  have ha := congrArg Loc.addr h
  simp only at ha
  omega

/-- A projected acquire records exactly a successful poll on the specified ready slot. -/
theorem raw_signal_acquire_iff {e : Event} {slot : Fin 2} {p : Nat} :
    rawSignal L g e = some (.acquire slot.val p) ↔
      ∃ acq scope, e.kind = .wait
        ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff slot.val⟩ p true acq scope := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try (solve | simp [rawSignal])
  case wait m parity ok acq scope =>
    cases ok
    · simp [rawSignal]
    · let loc := fun s => (⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff s⟩ : Loc)
      have hAddr := raw_slot_at_iff (loc := loc) (m := m)
        (raw_slot_addresses_ne (L := L) (g := g) 222808) slot
      change ((rawSlotAt loc m).map fun s => RawSignal.acquire s parity) =
        some (.acquire slot.val p) ↔ _
      rw [Option.map_eq_some_iff]
      constructor
      · rintro ⟨s, hs, hSignal⟩
        obtain ⟨rfl, rfl⟩ := RawSignal.acquire.inj hSignal
        exact ⟨acq, scope, by rw [hAddr.mp hs]⟩
      · rintro ⟨acq', scope', hk⟩
        obtain ⟨hm, hp, _, _, _⟩ := Kind.wait.inj hk
        exact ⟨slot.val, hAddr.mpr hm, congrArg (RawSignal.acquire slot.val) hp⟩

/-- A projected release records exactly an arrival on the specified raw-free slot. -/
theorem raw_signal_release_iff {e : Event} {slot : Fin 2} :
    rawSignal L g e = some (.release slot.val) ↔
      ∃ tx count rel scope, e.kind = .arrive
        ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff slot.val⟩ tx count rel scope := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> try (solve | simp [rawSignal])
  case wait m p ok acq scope =>
    cases ok <;> simp [rawSignal, reduceCtorEq]
  case arrive m tx count rel scope =>
    let loc := fun s => (⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff s⟩ : Loc)
    have hAddr := raw_slot_at_iff (loc := loc) (m := m)
      (raw_slot_addresses_ne (L := L) (g := g) 222824) slot
    change (rawSlotAt loc m).map RawSignal.release = some (.release slot.val) ↔ _
    rw [Option.map_eq_some_iff]
    constructor
    · rintro ⟨s, hs, hSignal⟩
      obtain rfl := RawSignal.release.inj hSignal
      exact ⟨tx, count, rel, scope, by rw [hAddr.mp hs]⟩
    · rintro ⟨tx', count', rel', scope', hk⟩
      exact ⟨slot.val, hAddr.mpr (Kind.arrive.inj hk).1, rfl⟩


private theorem raw_slot_at_lt {loc : Nat → Loc} {m : Loc} {s : Nat}
    (h : rawSlotAt loc m = some s) : s < 2 := by
  unfold rawSlotAt at h
  split at h
  · cases h
    decide
  · split at h
    · cases h
      decide
    · cases h

/-- Each projected raw event belongs to one of the two physical slots. -/
theorem raw_signal_has_slot {e : Event} (he : rawSignal L g e ≠ none) :
    (∃ (slot : Fin 2) (p : Nat), rawSignal L g e = some (.acquire slot.val p)) ∨
      (∃ slot : Fin 2, rawSignal L g e = some (.release slot.val)) := by
  unfold rawSignal at he ⊢
  split at he
  · rename_i m p acq scope hKind
    let loc := fun s => (⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawReadyOff s⟩ : Loc)
    change ((rawSlotAt loc m).map fun s => RawSignal.acquire s p) ≠ none at he
    have hSlot : rawSlotAt loc m ≠ none := fun h => he (Option.map_eq_none_iff.mpr h)
    obtain ⟨s, h⟩ := Option.ne_none_iff_exists'.mp hSlot
    exact .inl ⟨⟨s, raw_slot_at_lt h⟩, p, congrArg (Option.map fun s => RawSignal.acquire s p) h⟩
  · rename_i m tx count rel scope hKind
    let loc := fun s => (⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff s⟩ : Loc)
    change (rawSlotAt loc m).map RawSignal.release ≠ none at he
    have hSlot : rawSlotAt loc m ≠ none := fun h => he (Option.map_eq_none_iff.mpr h)
    obtain ⟨s, h⟩ := Option.ne_none_iff_exists'.mp hSlot
    exact .inr ⟨⟨s, raw_slot_at_lt h⟩, congrArg (Option.map RawSignal.release) h⟩
  · exact (he rfl).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
