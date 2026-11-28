-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Lib.MmaCollector
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns

@[expose] public section

/-! # ERR-TC-MMA: MMA and copy instances are valid

`TcMma.InstructionUnsafe` has three parts. Every MMA issue passes its checks
(`Mma.Export.issue_shape`: the descriptors, the masks, the D and A columns and the operand
addresses of the QK and PV sites), the kernel issues no `tcgen05.cp` (`Lib.no_cp`) and no MMA
reuses a collector buffer (`Lib.collectorSafe_mma`). What is open is `CompletedValues`: every
unmasked result cell of a completed MMA has a derived value, which needs the operand bytes to be
defined numbers (a value fact about the query tile, the K and V ring and the probabilities); that
is proved (`Safe.completed`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- Every completed MMA's unmasked result cells have a derived value. -/
def Safe.Completed (L : Launch) (X : Execution) : Prop :=
  ∀ i d s acc mask, X.MmaIssue i d s acc mask → TcMma.CompletedValues L Assumptions.all X i

/-- **ERR-TC-MMA**: MMA and copy instances are valid, given the values of the completed MMAs. -/
theorem Safe.noTmemInstruction (hp : Pre Q L m) {X : Execution} (base : Iface.BaseRead L X)
    (hCV : Safe.Completed L X)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    ¬ TcMma.InstructionUnsafe L Assumptions.all X :=
  fun hU => hU ⟨fun i d s acc mask hi => by
    obtain ⟨g, k⟩ := i
    obtain ⟨pc, he⟩ := hi
    exact ⟨Mma.Export.issue_shape hp hX hf base he, hCV _ _ _ _ _ ⟨pc, he⟩⟩,
    fun i c hi => (Lib.no_cp hX i c hi).elim, Lib.collectorSafe_mma hX⟩

end PTX.Kernels.InklingRelDecode.Proof.Top
