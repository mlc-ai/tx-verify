-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.LoaderRoleCounts
public import Kernels.TmlFa4Fwd.Proof.RoleCounts
public import Lemmas.Kernel.Correct
import Lemmas.Kernel.Existence
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX Prologue

noncomputable section

/-- A uniform bound covers every finite consistent execution, including one stuck
at any canonical polling loop. -/
theorem terminates {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    ∃ n, ∀ X, Consistent l kernel Assumptions.all m X → X.size l ≤ n := by
  refine terminates_of_count (computeBudget p + Loader.loaderLaneBudget p) ?_ ?_
  · intro X hX g hg
    by_cases hCompute : warpIndex l g < 14
    · exact (computeLaneTraceBound hp hX hg hCompute).trans (Nat.le_add_right ..)
    · exact (Loader.loaderLaneTraceBound hp hX hg (by omega)).trans (Nat.le_add_left ..)
  · intro X hX i s hi
    rw [(actualCopyShape hX hi).widthEq]
    decide

/-- Every consistent prefix has an extension of maximal counted size. -/
theorem maximalExtension {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    ∃ Y, X.le Y ∧ Maximal l kernel Assumptions.all m Y := by
  obtain ⟨Y, hY, hXY, hLargest⟩ := bounded_largest_extension (terminates hp) hX
  exact ⟨Y, hXY, hY, fun Z hZ hYZ => hLargest Z hZ (Execution.le_trans hXY hYZ)⟩

end
end PTX.Kernels.TmlFa4Fwd
