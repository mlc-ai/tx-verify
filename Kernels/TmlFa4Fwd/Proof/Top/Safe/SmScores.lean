-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.NoUb
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global

@[expose] public section

/-! # The softmax warps' undefined behaviour, from their score loads

A softmax lane's bias loads return the launch's bias elements (`biasReadHandoff`), so it makes no
undefined behaviour once its score loads return numbers (`softNoUb`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A softmax lane makes no undefined behaviour** when its score loads return numbers. -/
theorem softNoUb (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hScore : SmWarp.ScorePayloads p L X) {g k : Nat} {e : Event}
    (hw : Prologue.warpIndex L g < 8) (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f :=
  SmWarp.noUb_of_scores hp hX (biasReadHandoff hp hX hFw
    (inputsUnwritten hp (noInputWrite hp hX hFw)) (biasWrites hp hX hFw)) hScore hw he f

end PTX.Kernels.TmlFa4Fwd.Proof.Top
