-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingControlRegions
import Lemmas.Flow.NotCommit

@[expose] public section

/-! # The actual control regions outside the MMA role -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow PTX.EventFrame

/-- The softmax region and the region containing TMA, index, idle and dequantization. -/
def outsideMma (n : Nat) : Prop := (125 ≤ n ∧ n < 1842) ∨ 2162 ≤ n

instance outsideMma_decidable : DecidablePred outsideMma := fun n => by
  unfold outsideMma
  infer_instance

set_option maxRecDepth 100000 in
theorem outsideMma_closed : controlRegionClosed outsideMma = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem outsideMma_no_commit : kernel.code.zipIdx.all
    (fun p => !decide (outsideMma p.2) || !commitOp p.1.op) = true := by
  decide +kernel

/-- A fired commit instruction cannot belong to the non-MMA regions. -/
theorem no_commit_outsideMma {L : Launch} {g : Nat} {pc : Nat} {ins : Instr}
    {t : TState} {e : Event} {o : Option TState} {sp : TcCommit.Spec}
    (hpc : outsideMma pc) (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hk : e.kind = .tc (.commit sp)) :
    False := by
  have hn : commitOp ins.op = false := by
    have h := List.all_eq_true.mp outsideMma_no_commit (ins, pc)
      (List.mem_zipIdx_iff_getElem?.mpr hc)
    simpa [hpc] using h
  exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne hn)) hf sp hk).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
