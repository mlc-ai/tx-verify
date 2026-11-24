-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaRead
public import Lemmas.Tcgen05.TcMmaValue
public import Mathlib.Tactic.ByContra

@[expose] public section

namespace PTX
noncomputable section

/-- The selected arithmetic profiles flow into the safety source obligation: every required
Tensor Memory read of a safe execution has a read source with a value. -/
theorem sourceSafe_of_safe {L : Launch} {A : List Assumption} {X : Execution}
    {mem0 : Mem0} (hs : ¬ Unsafe L K A mem0 X) : TcMma.SourceSafe L A X := by
  by_contra h
  apply hs
  unfold Unsafe
  tauto

theorem writesSafe_of_safe {L : Launch} {A : List Assumption} {X : Execution}
    {mem0 : Mem0} (hs : ¬ Unsafe L K A mem0 X) : TcMma.WritesSafe L X := by
  by_contra h
  apply hs
  unfold Unsafe TcMma.WritesUnsafe
  tauto

end
end PTX
