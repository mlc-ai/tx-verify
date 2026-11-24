-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Kernels.TmlFa4Fwd.Spec
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputBytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global

@[expose] public section

/-! # The launch words of the cumulative query array are not written -/

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX

/-- The cumulative query array is immutable throughout the accepted execution. -/
def DrainCuQProtected (p : Params) (X : Execution) : Prop :=
  ∀ idx ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
    ¬ a.Covers ((globalLoc (p.cuQBase + 4 * idx)).at k)

end PTX.Kernels.TmlFa4Fwd.Epilogue

namespace PTX.Kernels.TmlFa4Fwd.Audit
open PTX Epilogue

set_option linter.unusedVariables false in
/-- The high-address audit layouts protect every CuQ byte even in a partial execution. -/
theorem cuQProtectedOfHighOutputBases {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : p.cuQBase + 4*p.batch + 3 < 137438953472)
    (hBase : p.lseBase = 274877906944) (hStride : p.lseStride = 274877906944)
    (hOutput : 137438953472 ≤ p.oMap.base) : DrainCuQProtected p X := by
  intro i hi k hk w a bytes hw
  have hU := Proof.inputsUnwritten hp (Proof.Top.noInputWrite hp hX (Proof.follow hp hX))
  exact hU ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions]) _ (by
    refine ⟨rfl, ?_, ?_⟩
    all_goals simp only [globalLoc, Loc.at]
    omega) w a bytes hw

end PTX.Kernels.TmlFa4Fwd.Audit
