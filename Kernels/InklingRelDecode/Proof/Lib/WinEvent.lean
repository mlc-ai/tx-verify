-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.WinFacts

@[expose] public section

/-! # A state entered by an event is the state after it

A state of the lane at a position that no local step reaches and only the event just before it
continues at is the state after that event, which is an event of the trace. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat}

/-- No event is at `P`. -/
def evPre (P : Nat) : Bool := scanCode (fun pc ins => ins.op.isLocal || pc != P) kernel.code 0

/-- **The state at `P` is the state after the event before it.** -/
theorem ev_before {P} (hpr : predOk P [] = true) (hev : evPre P = true) (hP : P ≠ 0)
    {X : Execution} {c : TState} (hl : Iface.LaneState L X g c) (hpc : c.pc = P) :
    ∃ k e, (X.tr g)[k]? = some e ∧ e.pc + 1 = P ∧
      Run kernel Assumptions.all L g {} ((X.tr g).take (k + 1)) (some c) := by
  obtain ⟨k, t0, hr, hrt⟩ := hl
  obtain ⟨k0, hk0, hr0⟩ := run_norm hr
  rcases Relation.ReflTransGen.cases_tail hrt with rfl | ⟨x, hx, ht⟩
  · cases k0 with
    | zero =>
      exfalso
      rw [List.take_zero] at hr0
      cases hr0
      simp at hpc
      omega
    | succ k =>
      obtain ⟨e, he'⟩ : ∃ e, (X.tr g)[k]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      refine ⟨k, e, he', ?_, hr0⟩
      obtain ⟨u, s, hu, hus, hes⟩ := pre_idx he' hr0
      obtain ⟨ins, hci, hnl, -⟩ := EventFrame.estep_event_source hes
      have hp := post_pc hes
      have hsp := EventFrame.estep_source_pc hes
      have hsc := scanCode_get hev hci
      rw [Nat.zero_add] at hsc
      simp only [hnl, Bool.false_or, bne_iff_ne, ne_eq] at hsc
      omega
  · have := pred_of_tau hpr ht hpc
    simp at this

end PTX.Kernels.InklingRelDecode.Proof.Lib
