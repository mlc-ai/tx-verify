-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions

@[expose] public section

/-! # The A elements of the PV MMAs

`PvAElements X`: the contraction elements of the A operand of every completed PV MMA (D below
column 256), the probability tile warpgroup 0 stored (`pExchange`), decode to numbers. It is the
part of `MmaElements` that is not proved from the query tile and the dequantized tiles: the
stored words are the rescaled exponentials of warpgroup 0's loop, finite when its words are
(`W0Trace`). It is proved from that guard in `Protocol/Values/PvAProof.lean` (`pv_a_elements`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- **The A elements of the completed PV MMAs are numbers.** -/
def PvAElements (X : Execution) : Prop :=
  ∀ i d s acc mask ops row col cell, X.MmaIssue i d s acc mask → X.async.mmaDone i = true →
    X.async.mmaOperands i = some ops → TcMma.writeCell s d mask row col = some cell → d < 256 →
    ∀ k < 16, ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
      (TcMma.operandRow s.descriptor row col) k = .ok x

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
