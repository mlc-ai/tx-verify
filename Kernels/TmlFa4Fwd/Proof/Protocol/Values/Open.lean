-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.LseStore
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.OutSource
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.KvRows

@[expose] public section

/-! # What the value layer still takes from the roles

`LaneLinks`: the numeric steps of the softmax and correction lanes. The tiles, the blocks and the
operand bytes are proved, so these give the links of the value recursion (`LaneLinks.links`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {D : Nat → RowData}

/-- **The softmax and correction lanes' part of the links.** -/
structure LaneLinks (p : Params) (L : Launch) (X : Execution) (D : Nat → RowData) : Prop where
  soft : SoftLink p L X (tileOf p L) D
  corr : CorrLink p L X (tileOf p L) D

/-- **The links of the value recursion.** -/
theorem LaneLinks.links (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hIn : InputsUnwritten p X) (h : LaneLinks p L X D) :
    ValueLinks p L X (tileOf p L) (tileInputs p L X) D where
  tile _ _ hT := tileOk hp hT
  bytes := operandBytes hp hX hFw hIn
  inputs _ _ hT := inputsAre hp hX hFw hIn (kvRows hp hX hFw) hT
  soft := h.soft
  corr := h.corr

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
