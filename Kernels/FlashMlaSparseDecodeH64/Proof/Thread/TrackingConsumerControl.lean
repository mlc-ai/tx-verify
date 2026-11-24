-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCausalInduction
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadGuards
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingControlRegions
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotTensor
import Lemmas.Flow.NotClc

@[expose] public section

/-! # Instruction classes in a consumer's concrete continuation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Only the softmax and dequantization roles can dismiss an actual event. -/
inductive ConsumerState : Machine.ThreadD → Prop
  | wg0 (d : Wg0.D) : ConsumerState (.wg0 d)
  | wg2 (d : Wg2.D) : ConsumerState (.wg2 d)

theorem dismissal_is_consumer {g i : Nat} {e : Event} {d : Machine.ThreadD}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hn : Machine.next P L g d e = some none) : ConsumerState d := by
  have hg := Frame.lt_of_get hX he
  have hSound (a : Nat) (ha : a < L.threads) := (hs a ha).machine
  cases d with
  | wg0 d => exact .wg0 d
  | wg2 d => exact .wg2 d
  | tma d => exact (TmaTracking.next_tracked hpre hX (hSound g hg) he hd hn).elim
  | idle s => exact (idle_next_tracked s e hn).elim
  | head => exact (PrologueRoleTrace.dispatch_next_tracked hpre hX hSound he hd hn).elim
  | prologue s => exact (PrologueRoleTrace.prologue_next_tracked hpre hX hSound he hd hn).elim
  | mma d => exact (MmaTracking.next_tracked hpre hX (hSound g hg) he hd hn).elim
  | index d => exact (Wg1Index.next_tracked hpre hX hSound he hd hn).elim
  | done => cases hn

private def nonIssuerRegion (pc : Nat) : Prop := (103 ≤ pc ∧ pc < 1842) ∨ 2606 ≤ pc

private instance (pc : Nat) : Decidable (nonIssuerRegion pc) := by
  unfold nonIssuerRegion
  infer_instance

set_option maxRecDepth 100000 in
private theorem nonIssuerRegion_closed : controlRegionClosed nonIssuerRegion = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem nonIssuerRegion_no_tensor : kernel.code.zipIdx.all
    (fun p => !decide (nonIssuerRegion p.2) || !tensorOp p.1.op) = true := by
  decide +kernel

private theorem softmax_region (d : Wg0.D) : nonIssuerRegion d.site.pc := by
  cases d.site <;> unfold nonIssuerRegion <;>
    first
    | decide
    | (rename_i a; revert a; decide)
    | (rename_i a b; revert a b; decide)

private theorem dequant_region (d : Wg2.D) : nonIssuerRegion d.site.pc := by
  cases d.site <;> unfold nonIssuerRegion <;> decide +revert

/-- A softmax or dequantization suffix cannot execute an instruction that issues a TMA load. -/
theorem no_tensor_after_softmax_or_dequant {g i j : Nat} {d : Machine.ThreadD}
    {early late : Event} {addr : Nat} {sp : TensorCopy.Spec}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some early) (hl : X.get (g, j) = some late) (hij : i < j)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some d))
    (hRole : (∃ z, d = .wg0 z) ∨ ∃ z, d = .wg2 z)
    (hKind : late.kind = .tensorIssue addr sp) : False := by
  have hRegion : nonIssuerRegion early.pc := by
    rw [Frame.event_pc hs hX he hd]
    rcases hRole with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact softmax_region z
    · exact dequant_region z
  have hLater := later_event_in_control_region nonIssuerRegion_closed hX
    (Frame.lt_of_get hX he) he hl hij hRegion
  rcases get_source hX hl with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · rw [hf] at hKind
    cases hKind
  · have hNot := List.all_eq_true.mp nonIssuerRegion_no_tensor (ins, late.pc)
      (List.mem_zipIdx_iff_getElem?.mpr hc)
    have hop : tensorOp ins.op = false := by simpa [hLater] using hNot
    exact fires_notTensor (eventTmpl_notTensor hop) hf addr sp hKind

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
