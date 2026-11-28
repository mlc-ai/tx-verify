-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Typed
import Kernels.InklingRelDecode.Proof.Softmax.Soft.SentState
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Inp
import Kernels.InklingRelDecode.Proof.Common.ValueThread
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Proof.Softmax.Export.Value
import Kernels.InklingRelDecode.Proof.Softmax.Operand
import Kernels.InklingRelDecode.Proof.Softmax.LateStep
import Kernels.InklingRelDecode.Flow.Code.Part035

/-! # The word a lane sends at pc 1838 is a number or `-inf`

The first window's result (register 1520) is a number or `-inf` when the value state is typed
(`w1_ni`); the state is typed along the trace given that the score loads return numbers
(`soft_vtyp`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

/-- **The word of the shuffle at pc 1838 is a number or `-inf`**, when the score loads of the lane
return numbers. -/
public theorem sent_ni {m : Mem0} {X : Execution} {k : Nat} {mode : ShflMode} {b c : Nat}
    {recv : Value} {ok : Bool} {sent : Value} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (get : X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩) : SK.ni.Has sent := by
  obtain ⟨w, ent, d, y, n, -, -, hs, -, -, rfl⟩ := sent_state hp hX hf get
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nub := Frame.noUbBefore_of_get hX get
  have typ := soft_vtyp hp hX hf hS k len _ hs nub w ent y n rfl
  exact w1_ni _ (w1_in hp typ)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
