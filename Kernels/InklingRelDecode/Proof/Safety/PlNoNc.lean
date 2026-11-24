-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Regions
public import Lemmas.Flow.NotNc

@[expose] public section

/-!
# The kernel has no non-coherent load

No assumption of `Assumptions.all` allows a `ld.global.nc` at any position (`Assumption.ncLoads`),
so no instruction fires a non-coherent read (`fires_not_nc`): an event of a consistent execution
is undefined behaviour or the event of its instruction (`get_source`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- No assumption of the kernel allows a non-coherent load at any position. -/
theorem asms_no_nc (pc : Nat) : asms.any (·.ncLoads pc) = false := by
  rfl

/-- **The kernel has no non-coherent load.** -/
theorem no_nc (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {a : Acc} {bs : List (Option Byte)},
      X.get i ≠ some ⟨pc, .nc a bs⟩ := by
  intro i pc a bs he
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, htpc, -, hfire⟩
  · cases hf
  · exact fires_not_nc (by rw [htpc]; exact asms_no_nc _) hfire rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
