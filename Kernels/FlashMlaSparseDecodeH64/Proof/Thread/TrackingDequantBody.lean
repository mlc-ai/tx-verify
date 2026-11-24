-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantContinuation
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxMaskControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterRegion
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents

@[expose] public section

/-! # The state carried through an actual dequantizer body -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private def carriedRegisters : List Nat := [2788, 351, 2789, 513, 457, 2988]

set_option maxRecDepth 100000 in
private theorem body_windows :
    carriedRegisters.all (fun r => stableRegisterWindow r 2680 3599) = true := by decide +kernel

private theorem body_window (r : Nat) (hr : r ∈ carriedRegisters) :
    stableRegisterWindow r 2680 3599 = true :=
  List.all_eq_true.mp body_windows r hr

/-- Every event before the first release stays inside the current body. -/
theorem dequant_body_event_bound {t : TState} {e : Event} {before tail : List Event}
    {o : Option TState} (hPc : t.pc = 2680) (hBefore : ∀ f ∈ before, f.pc ≠ 3599)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    2680 ≤ e.pc := by
  have hLow : 2680 ≤ t.pc := hPc.symm ▸ le_rfl
  have hHigh : t.pc < 3599 := by rw [hPc]; decide
  have hChecked := body_window 2788 (by decide)
  obtain ⟨v, u, q, hFirst, hLast, _, hLocal, hStep⟩ :=
    register_at_event_in_window hChecked Flow.code_3598 rfl hLow hHigh hBefore hRun
  rw [estep_source_pc hStep]
  exact (local_path_in_register_window hChecked ⟨hFirst, hLast.le⟩ hLocal).1

private theorem raw_free_address {t : TState} {block : Nat}
    (hpre : Pre P L mem0) (hPc : t.pc = 3598)
    (hBase : t.regs 2788 = some (sb L (8 * (block % 2)))) (hf : t.fault = none) :
    ∃ u, run kernel Assumptions.all L g 1 t = some u ∧
      AtVector u 3599 [(2784, sb L (Wg2.rawFreeOff (block % 2)))] t.sub t.acc := by
  have ht : AtVector t 3598 [(2788, sb L (8 * (block % 2)))] t.sub t.acc :=
    ⟨hPc, rfl, rfl, hf, hBase, trivial⟩
  have hShared := sharedBase_lt hpre
  have hSlot := Nat.mod_lt block (by decide : 0 < 2)
  seg_fp ht using
    simp only [sb, Wg2.rawFreeOff, b32]
    norm_bits [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The first free arrival of a concrete body releases exactly the slot its raw wait acquired. -/
theorem dequant_body_release {t : TState} {block : Nat} {e : Event}
    {before tail : List Event} {o : Option TState}
    (hpre : Pre P L mem0) (hAt : AtVector t 2680 (dequantPollFacts L g block) t.sub t.acc)
    (hTag : e.pc = 3599) (hBefore : ∀ f ∈ before, f.pc ≠ 3599)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + Wg2.rawFreeOff (block % 2)⟩
      0 1 true .cta := by
  have hLow : 2680 ≤ t.pc := hAt.1.symm ▸ le_rfl
  have hHigh : t.pc < 3599 := by rw [hAt.1]; decide
  obtain ⟨v, u, q, hPc, hRegs, htau, hFire⟩ :=
    register_before_window_end (body_window 2788 (by decide)) Flow.code_3598 rfl
      (by decide +kernel) hLow hHigh hTag hBefore hRun
  obtain ⟨z, hz, hAtZ⟩ := raw_free_address (L := L) (g := g) (block := block) hpre hPc
    (hRegs.trans hAt.2.2.2.2.2.2.2.2.1) (tau_fault_free htau)
  obtain rfl := one_step_matches htau hz
  have hSlot := Nat.mod_lt block (by decide : 0 < 2)
  have hShared := sharedBase_lt hpre
  have hBound : L.sharedBase + Wg2.rawFreeOff (block % 2) < 2 ^ 32 := by
    unfold Wg2.rawFreeOff
    omega
  have hm := mbarLoc_b32 (L := L) (g := g) hAtZ.2.2.2.2.1 hBound
    (Wg2.sharedAddr_align hpre (by unfold Wg2.rawFreeOff; omega))
  obtain ⟨m, ho, hf⟩ := hFire
  rw [out_event hAtZ.2.2.2.1 (hAtZ.1 ▸ Flow.code_3599) rfl rfl] at ho
  obtain rfl := Out.ev.inj ho.symm
  exact RingEvents.fired_unit_arrive hm hf

/-- A concrete raw slot return with a nonempty continuation advances the slot and parity
before either the next loop entry or epilogue. -/
theorem dequant_body_advance {t : TState} {block : Nat} {e : Event}
    {before : List Event} {head : Event} {tail : List Event} {o : Option TState}
    (hAt : AtVector t 2680 (dequantPollFacts L g block) t.sub t.acc)
    (hTag : e.pc = 3599) (hBefore : ∀ f ∈ before, f.pc ≠ 3599)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: head :: tail) o) :
    ∃ u, AtVector u 3605 (dequantHeadFacts L g (block + 1)) u.sub u.acc ∧
      Run kernel Assumptions.all L g u (head :: tail) o := by
  have hLow : 2680 ≤ t.pc := hAt.1.symm ▸ le_rfl
  have hHigh : t.pc ≤ 3599 := by rw [hAt.1]; decide
  obtain ⟨v, hPc, hKeep, hNext⟩ :=
    resume_register_window_end body_window (by decide) hLow hHigh hTag hBefore hRun
  have hCode := hPc ▸ Flow.code_3599
  have hStop : Stops kernel Assumptions.all L g v := by
    cases hF : v.fault with
    | none => exact ⟨_, out_event hF hCode rfl rfl⟩
    | some f => exact ⟨.ub f, by simp [out, hF]⟩
  cases hNext with
  | step hTau hStep hTail =>
    rw [stop_unique hTau .refl (stops_of_estep hStep) hStop] at hStep
    obtain ⟨rfl, hFault⟩ := softmax_unit_arrival_return hCode hStep
    have hf := hAt.2.2.2.2
    have hStart : AtVector (PTX.next v) 3600
        ([(351, dequantParityWord block), (2789, b32 (4294967295 - block % 2))] ++
          dequantHeadFacts L g block) v.sub v.acc := by
      exact ⟨by change v.pc + 1 = 3600; rw [hPc], rfl, rfl, hFault,
        (hKeep 351 (by decide)).trans hf.2.2.1, (hKeep 2789 (by decide)).trans hf.2.2.2.1,
        (hKeep 513 (by decide)).trans hf.2.2.2.2.2.1,
        (hKeep 457 (by decide)).trans hf.2.2.2.2.2.2.1,
        (hKeep 2988 (by decide)).trans hf.2.2.2.2.2.2.2.1, trivial⟩
    obtain ⟨u, hu, hResult⟩ := dequant_loop_advance hStart
    exact ⟨u, ⟨hResult.1, rfl, rfl, hResult.2.2.2.1, hResult.2.2.2.2⟩,
      after_softmax_local_prefix (run_rtg hu) hTail⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
