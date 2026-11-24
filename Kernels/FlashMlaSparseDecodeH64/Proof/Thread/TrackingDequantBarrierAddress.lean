-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterRegion
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturn
import Lemmas.Flow.NotObject
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents

@[expose] public section

/-! # Concrete dequantizer barrier addresses through numerical dismissals -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private def bufferRegion (pc : Nat) : Bool := decide (2667 ≤ pc ∧ pc ≤ 3607)
private def scaledRegion (pc : Nat) : Bool := decide (pc = 2672 ∨ pc = 2673)
private def symbolRegion (pc : Nat) : Bool := pc == 2673
private def addressRegion (pc : Nat) : Bool := decide (2674 ≤ pc ∧ pc ≤ 3599)
private def complementRegion (pc : Nat) : Bool := decide (2675 ≤ pc ∧ pc ≤ 3604)

set_option maxRecDepth 100000 in
private theorem buffer_audit : registerRegionChecked 2988 bufferRegion [2666, 3604] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem scaled_audit : registerRegionChecked 2786 scaledRegion [2671] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem symbol_audit : registerRegionChecked 2787 symbolRegion [2672] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem address_audit : registerRegionChecked 2788 addressRegion [2673] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem complement_audit : registerRegionChecked 2789 complementRegion [2674] = true := by
  decide +kernel

private def BufferAddressState (L : Launch) (t : TState) : Prop :=
  (bufferRegion t.pc = true → ∃ b : Fin 2, t.regs 2988 = some (b32 b.val)) ∧
  (scaledRegion t.pc = true → ∃ b : Fin 2, t.regs 2786 = some (b32 (8 * b.val))) ∧
  (symbolRegion t.pc = true → t.regs 2787 = some (b32 L.sharedBase)) ∧
  (addressRegion t.pc = true → ∃ b : Fin 2, t.regs 2788 = some (b32 (L.sharedBase + 8 * b.val))) ∧
  (complementRegion t.pc = true → ∃ b : Fin 2, t.regs 2789 = some (b32 (4294967295 - b.val)))

private theorem buffer_address_tau {t u : TState}
    (hpre : Pre P L mem0) (hOld : BufferAddressState L t)
    (hTau : Tau kernel Assumptions.all L g t u) :
    BufferAddressState L u := by
  have hFault := tau_fault_free hTau
  have hShared := sharedBase_lt hpre
  refine ⟨register_region_tau
    (property := fun value => ∃ b : Fin 2, value = some (b32 b.val)) buffer_audit
    hOld.1 ?_ hTau,
    register_region_tau
    (property := fun value => ∃ b : Fin 2, value = some (b32 (8 * b.val))) scaled_audit
    hOld.2.1 ?_ hTau,
    register_region_tau
    (property := fun value => value = some (b32 L.sharedBase)) symbol_audit
    hOld.2.2.1 ?_ hTau,
    register_region_tau
    (property := fun value => ∃ b : Fin 2, value = some (b32 (L.sharedBase + 8 * b.val)))
    address_audit
    hOld.2.2.2.1 ?_ hTau,
    register_region_tau
    (property := fun value => ∃ b : Fin 2, value = some (b32 (4294967295 - b.val))) complement_audit
    hOld.2.2.2.2 ?_ hTau⟩
  · intro hp _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hPc | hPc
    · have ha : AtVector t 2666 [] t.sub t.acc := ⟨hPc, rfl, rfl, hFault, trivial⟩
      obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
          AtVector v 2667 [(2988, b32 0)] t.sub t.acc := by
        seg_fp ha using (try rfl)
      exact ⟨0, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩
    · obtain ⟨b, hb⟩ := hOld.2.2.2.2 (hPc ▸ by decide)
      have ha : AtVector t 3604 [(2789, b32 (4294967295 - b.val))] t.sub t.acc :=
        ⟨hPc, rfl, rfl, hFault, hb, trivial⟩
      fin_cases b
      · obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
            AtVector v 3605 [(2988, b32 1)] t.sub t.acc := by
          seg_fp ha using (try rfl)
        exact ⟨1, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩
      · obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
            AtVector v 3605 [(2988, b32 0)] t.sub t.acc := by
          seg_fp ha using (try rfl)
        exact ⟨0, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩
  · intro hp _
    have hPc : t.pc = 2671 := List.mem_singleton.mp hp
    obtain ⟨b, hb⟩ := hOld.1 (hPc ▸ by decide)
    have ha : AtVector t 2671 [(2988, b32 b.val)] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hFault, hb, trivial⟩
    obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 2672 [(2786, b32 (8 * b.val))] t.sub t.acc := by
      seg_fp ha using
        (try unfold b32)
        (try norm_bits [Nat.mul_comm])
    exact ⟨b, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩
  · intro hp _
    have hPc : t.pc = 2672 := List.mem_singleton.mp hp
    have ha : AtVector t 2672 [] t.sub t.acc := ⟨hPc, rfl, rfl, hFault, trivial⟩
    obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 2673 [(2787, b32 L.sharedBase)] t.sub t.acc := by
      seg_fp ha using
        (try unfold b32)
        (try norm_bits [Nat.add_zero])
    exact (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1
  · intro hp _
    have hPc : t.pc = 2673 := List.mem_singleton.mp hp
    obtain ⟨b, hb⟩ := hOld.2.1 (hPc ▸ by decide)
    have hSym := hOld.2.2.1 (hPc ▸ by decide)
    have ha : AtVector t 2673 [(2786, b32 (8 * b.val)), (2787, b32 L.sharedBase)] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hFault, hb, hSym, trivial⟩
    have hbRange := b.isLt
    obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 2674 [(2788, b32 (L.sharedBase + 8 * b.val))] t.sub t.acc := by
      seg_fp ha using
        (try unfold b32)
        (try norm_bits [Nat.add_zero])
    exact ⟨b, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩
  · intro hp _
    have hPc : t.pc = 2674 := List.mem_singleton.mp hp
    obtain ⟨b, hb⟩ := hOld.1 (hPc ▸ by decide)
    have ha : AtVector t 2674 [(2988, b32 b.val)] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hFault, hb, trivial⟩
    fin_cases b
    · obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
          AtVector v 2675 [(2789, b32 4294967295)] t.sub t.acc := by
        seg_fp ha using (try rfl)
      exact ⟨0, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩
    · obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
          AtVector v 2675 [(2789, b32 4294967294)] t.sub t.acc := by
        seg_fp ha using (try rfl)
      exact ⟨1, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩

private theorem buffer_address_event {t u : TState} {e : Event}
    (hOld : BufferAddressState L t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    BufferAddressState L u := by
  refine ⟨register_region_event
    (property := fun value => ∃ b : Fin 2, value = some (b32 b.val)) buffer_audit ?_ hOld.1 he,
    register_region_event
    (property := fun value => ∃ b : Fin 2, value = some (b32 (8 * b.val))) scaled_audit
    ?_ hOld.2.1 he,
    register_region_event
    (property := fun value => value = some (b32 L.sharedBase)) symbol_audit ?_ hOld.2.2.1 he,
    register_region_event
    (property := fun value => ∃ b : Fin 2, value = some (b32 (L.sharedBase + 8 * b.val)))
    address_audit
    ?_ hOld.2.2.2.1 he,
    register_region_event
    (property := fun value => ∃ b : Fin 2, value = some (b32 (4294967295 - b.val))) complement_audit
    ?_ hOld.2.2.2.2 he⟩
  · intro pc hp ins hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rw [Flow.code_2666] at hc
      obtain rfl := Option.some.inj hc
      rfl
    · rw [Flow.code_3604] at hc
      obtain rfl := Option.some.inj hc
      rfl
  · intro pc hp ins hc
    obtain rfl := List.mem_singleton.mp hp
    rw [Flow.code_2671] at hc
    obtain rfl := Option.some.inj hc
    rfl
  · intro pc hp ins hc
    obtain rfl := List.mem_singleton.mp hp
    rw [Flow.code_2672] at hc
    obtain rfl := Option.some.inj hc
    rfl
  · intro pc hp ins hc
    obtain rfl := List.mem_singleton.mp hp
    rw [Flow.code_2673] at hc
    obtain rfl := Option.some.inj hc
    rfl
  · intro pc hp ins hc
    obtain rfl := List.mem_singleton.mp hp
    rw [Flow.code_2674] at hc
    obtain rfl := Option.some.inj hc
    rfl

private theorem buffer_address_start : BufferAddressState L {} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals intro h; cases h

private def readyRegion (pc : Nat) : Bool := pc == 3597
private def freeRegion (pc : Nat) : Bool := pc == 3599

set_option maxRecDepth 100000 in
private theorem ready_audit : registerRegionChecked 2783 readyRegion [3596] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem free_audit : registerRegionChecked 2784 freeRegion [3598] = true := by
  decide +kernel

private def DequantBarrierState (L : Launch) (t : TState) : Prop :=
  BufferAddressState L t ∧
  (readyRegion t.pc = true → ∃ b : Fin 2,
    t.regs 2783 = some (b32 (L.sharedBase + (222792 + 8 * b.val)))) ∧
  (freeRegion t.pc = true → ∃ b : Fin 2,
    t.regs 2784 = some (b32 (L.sharedBase + (222824 + 8 * b.val))))

private theorem dequant_barrier_tau {t u : TState}
    (hpre : Pre P L mem0) (hOld : DequantBarrierState L t)
    (hTau : Tau kernel Assumptions.all L g t u) :
    DequantBarrierState L u := by
  have hFault := tau_fault_free hTau
  have hShared := sharedBase_lt hpre
  refine ⟨buffer_address_tau hpre hOld.1 hTau, register_region_tau
    (property := fun v => ∃ b : Fin 2, v = some (b32 (L.sharedBase + (222792 + 8 * b.val))))
    ready_audit hOld.2.1 ?_ hTau, register_region_tau
    (property := fun v => ∃ b : Fin 2, v = some (b32 (L.sharedBase + (222824 + 8 * b.val))))
    free_audit hOld.2.2 ?_ hTau⟩
  · intro hp _
    have hPc : t.pc = 3596 := List.mem_singleton.mp hp
    obtain ⟨b, hb⟩ := hOld.1.2.2.2.1 (hPc ▸ by decide)
    have ha : AtVector t 3596 [(2788, b32 (L.sharedBase + 8 * b.val))] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hFault, hb, trivial⟩
    have hbRange := b.isLt
    obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 3597 [(2783, b32 (L.sharedBase + (222792 + 8 * b.val)))] t.sub t.acc := by
      seg_fp ha using
        (try unfold b32)
        (try norm_bits [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm])
    exact ⟨b, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩
  · intro hp _
    have hPc : t.pc = 3598 := List.mem_singleton.mp hp
    obtain ⟨b, hb⟩ := hOld.1.2.2.2.1 (hPc ▸ by decide)
    have ha : AtVector t 3598 [(2788, b32 (L.sharedBase + 8 * b.val))] t.sub t.acc :=
      ⟨hPc, rfl, rfl, hFault, hb, trivial⟩
    have hbRange := b.isLt
    obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
        AtVector v 3599 [(2784, b32 (L.sharedBase + (222824 + 8 * b.val)))] t.sub t.acc := by
      seg_fp ha using
        (try unfold b32)
        (try norm_bits [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm])
    exact ⟨b, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩

private theorem dequant_barrier_event {t u : TState} {e : Event}
    (hOld : DequantBarrierState L t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    DequantBarrierState L u := by
  refine ⟨buffer_address_event hOld.1 he, register_region_event
    (property := fun v => ∃ b : Fin 2, v = some (b32 (L.sharedBase + (222792 + 8 * b.val))))
    ready_audit ?_ hOld.2.1 he, register_region_event
    (property := fun v => ∃ b : Fin 2, v = some (b32 (L.sharedBase + (222824 + 8 * b.val))))
    free_audit ?_ hOld.2.2 he⟩
  · intro pc hp ins hc
    obtain rfl := List.mem_singleton.mp hp
    rw [Flow.code_3596] at hc
    obtain rfl := Option.some.inj hc
    rfl
  · intro pc hp ins hc
    obtain rfl := List.mem_singleton.mp hp
    rw [Flow.code_3598] at hc
    obtain rfl := Option.some.inj hc
    rfl

/-- Dequantizer arrivals keep their two-slot barrier addresses for every actual trace. -/
theorem actual_dequant_barrier_address {X : Execution} {i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {m : Loc} {tx count : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get (g, i) = some e) (hTag : e.pc = Wg2.Site.ready.pc ∨ e.pc = Wg2.Site.free.pc)
    (hKind : e.kind = .arrive m tx count rel scope) :
    (e.pc = Wg2.Site.ready.pc ∧ ∃ b : Fin 2, e.kind = .arrive
      ⟨.shared, ctaOf L g, L.sharedBase + (222792 + 8 * b.val)⟩ 0 1 true .cta) ∨
    (e.pc = Wg2.Site.free.pc ∧ ∃ b : Fin 2, e.kind = .arrive
      ⟨.shared, ctaOf L g, L.sharedBase + (222824 + 8 * b.val)⟩ 0 1 true .cta) := by
  obtain ⟨o, hRun⟩ := hX.thr g (Frame.lt_of_get hX he)
  have hStart : DequantBarrierState L {} := ⟨buffer_address_start, nofun, nofun⟩
  obtain ⟨t, q, hAt, hStep⟩ := actual_event_invariant
    (dequant_barrier_tau hpre) dequant_barrier_event hStart hRun (List.mem_of_getElem? he)
  have hPc := estep_source_pc hStep
  have hShared := sharedBase_lt hpre
  cases q with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have h := fires_none_ends hf
    simp [Ends, hKind] at h
  | some u =>
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
    rcases hTag with hReady | hFree
    · have hp : t.pc = 3597 := hPc.symm.trans hReady
      obtain ⟨b, hb⟩ := hAt.2.1 (hp ▸ by decide)
      have hbRange := b.isLt
      have hm := mbarLoc_b32 (L := L) (g := g) hb (by omega)
        (Wg0.ringAddr_mod8 hpre (off := 222792) (by decide))
      rw [hp, Flow.code_3597] at hc
      obtain rfl := Option.some.inj hc
      exact .inl ⟨hReady, b, RingEvents.fired_unit_arrive hm hf⟩
    · have hp : t.pc = 3599 := hPc.symm.trans hFree
      obtain ⟨b, hb⟩ := hAt.2.2 (hp ▸ by decide)
      have hbRange := b.isLt
      have hm := mbarLoc_b32 (L := L) (g := g) hb (by omega)
        (Wg0.ringAddr_mod8 hpre (off := 222824) (by decide))
      rw [hp, Flow.code_3599] at hc
      obtain rfl := Option.some.inj hc
      exact .inr ⟨hFree, b, RingEvents.fired_unit_arrive hm hf⟩

private def svPollRegion (pc : Nat) : Bool := decide (2684 ≤ pc ∧ pc ≤ 2686)

set_option maxRecDepth 100000 in
private theorem sv_poll_audit : registerRegionChecked 2461 svPollRegion [2683] = true := by
  decide +kernel

private def SvPollAddress (L : Launch) (t : TState) : Prop :=
  BufferAddressState L t ∧ (svPollRegion t.pc = true → ∃ b : Fin 2,
    t.regs 2461 = some (b32 (L.sharedBase + Wg2.svDoneOff b.val)))

private theorem sv_poll_address_tau {t u : TState}
    (hpre : Pre P L mem0) (hOld : SvPollAddress L t)
    (hTau : Tau kernel Assumptions.all L g t u) : SvPollAddress L u := by
  refine ⟨buffer_address_tau hpre hOld.1 hTau, register_region_tau
    (property := fun v => ∃ b : Fin 2, v = some (b32 (L.sharedBase + Wg2.svDoneOff b.val)))
    sv_poll_audit hOld.2 ?_ hTau⟩
  intro hp _
  have hPc := List.mem_singleton.mp hp
  obtain ⟨b, hb⟩ := hOld.1.2.2.2.1 (hPc ▸ by decide)
  have hBound := b.isLt
  have hShared := sharedBase_lt hpre
  have ha : AtVector t 2683 [(2788, b32 (L.sharedBase + 8 * b.val))] t.sub t.acc :=
    ⟨hPc, rfl, rfl, tau_fault_free hTau, hb, trivial⟩
  obtain ⟨v, hRun, hAt⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
      AtVector v 2684 [(2461, b32 (L.sharedBase + Wg2.svDoneOff b.val))] t.sub t.acc := by
    seg_fp ha using
      (try unfold b32 Wg2.svDoneOff)
      (try norm_bits [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm])
  exact ⟨b, (one_step_matches hTau hRun) ▸ hAt.2.2.2.2.1⟩

private theorem sv_poll_address_event {t u : TState} {e : Event}
    (hOld : SvPollAddress L t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    SvPollAddress L u := by
  refine ⟨buffer_address_event hOld.1 he, register_region_event
    (property := fun v => ∃ b : Fin 2, v = some (b32 (L.sharedBase + Wg2.svDoneOff b.val)))
    sv_poll_audit ?_ hOld.2 he⟩
  intro pc hp ins hc
  obtain rfl := List.mem_singleton.mp hp
  rw [Flow.code_2683] at hc
  obtain rfl := Option.some.inj hc
  rfl

/-- The actual accumulator-reuse wait uses the two SV barriers, including in a dismissed trace. -/
theorem actual_dequant_sv_poll {X : Execution} {i parity : Nat} {e : Event}
    {m : Loc} {ok acq : Bool} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, i) = some e) (hTag : e.pc = Wg2.Site.svDone.pc)
    (hKind : e.kind = .wait m parity ok acq scope) :
    ∃ b : Fin 2, m = ⟨.shared, ctaOf L g, L.sharedBase + Wg2.svDoneOff b.val⟩ := by
  obtain ⟨o, hRun⟩ := hX.thr g (Frame.lt_of_get hX he)
  have hStart : SvPollAddress L {} := ⟨buffer_address_start, nofun⟩
  obtain ⟨t, q, hAt, hStep⟩ := actual_event_invariant
    (sv_poll_address_tau hpre) sv_poll_address_event hStart hRun (List.mem_of_getElem? he)
  cases q with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have h := fires_none_ends hf
    simp [Ends, hKind] at h
  | some u =>
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
    have hp : t.pc = 2684 := (estep_source_pc hStep).symm.trans hTag
    obtain ⟨b, hb⟩ := hAt.2 (hp ▸ by decide)
    have hBound : L.sharedBase + Wg2.svDoneOff b.val < 2 ^ 32 := by
      have hShared := sharedBase_lt hpre
      have hSlot := b.isLt
      unfold Wg2.svDoneOff
      omega
    have hm := mbarLoc_b32 (L := L) (g := g) hb hBound
      (Wg2.sharedAddr_align hpre (by unfold Wg2.svDoneOff; omega))
    rw [hp, Flow.code_2684] at hc
    obtain rfl := Option.some.inj hc
    exact ⟨b, fires_wait_loc hm hf m parity ok acq scope hKind⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
