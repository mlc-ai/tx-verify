-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Lemmas.Flow.StepsQFT
public import Lemmas.Kernel.NoUbStrictQPLane
import Kernels.InklingRelDecode.Proof.Softmax.LateHalf
import Kernels.InklingRelDecode.Proof.Softmax.Strict.Pieces

@[expose] public section

/-! # The fact of the late lanes, for the windows of the epilogue

The data lanes' strict windows read one fact of every state the lane reaches (`LateR'`): no
declined `add`, `sub`, `mul`, packs and bias pieces on halves, the reciprocal's operand and the
software `exp2` input. It holds by the value facts `Iface.LateValues`. The epilogue's window
takes a fact `R` of that kind abstractly: the single pieces of its pcs hold under it, and under
it the reciprocal's operand is not a zero. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption

private theorem epi_late : ∀ pc ∈ List.range' 2642 32, lateOk pc = true := by decide +kernel

/-- **A fact of every state a data lane reaches**, under which the epilogue's single pieces hold
and the reciprocal's operand is not a zero. -/
public theorem late_package {L : Launch} {X : Execution} {g : Nat} (hv : Iface.LateValues L X)
    (lane : g % L.block < 128) :
    ∃ R : TState → Prop, (∀ t, Frame.LaneAt kernel Assumptions.all L X g t → R t) ∧
      (∀ pc, 2642 ≤ pc → pc ≤ 2673 → SingleStep kernel Assumptions.all L g R pc) ∧
      (∀ t, R t → t.pc = 2602 →
        ∀ x : EReal, readERealOpnd t .f32 (.reg 1762) = some (.ok x) → x ≠ 0) :=
  ⟨LateR' L g,
    fun t h => ⟨⟨hv.noDecline g t lane h, hv.pack g t lane h⟩, hv.half g t lane h,
      hv.rcp g t lane h, hv.exp2 g t lane h⟩,
    fun pc lo hi => Strict.single_late
      (epi_late pc (List.mem_range'_1.mpr ⟨lo, by omega⟩)),
    fun t h hpc => h.2.2.1 hpc⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
