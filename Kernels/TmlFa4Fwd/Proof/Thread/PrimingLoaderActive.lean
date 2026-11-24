-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingKeyPrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingValuePrefix
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Kernels.TmlFa4Fwd.Loader Epilogue Prologue

/-- An issued priming key vector identifies an active scheduled tile. -/
theorem PrimingKeyVector.active {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingKeyVector X (g, j) pair upper spec) (hWarp : 14 ≤ warpIndex l g) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  refine loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) h ?_ ?_
  · change 297 < kCopyPc pair + (if upper then 1 else 0)
    fin_cases pair <;> cases upper <;> decide
  · change kCopyPc pair + (if upper then 1 else 0) < 1862
    fin_cases pair <;> cases upper <;> decide

/-- An issued priming value vector identifies an active scheduled tile. -/
theorem PrimingValueVector.active {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingValueVector X (g, j) pair upper spec) (hWarp : 14 ≤ warpIndex l g) :
    g / l.block < tilePrefix p p.batch * p.heads := by
  refine loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
    (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) h ?_ ?_
  · change 297 < vCopyPc pair + (if upper then 1 else 0)
    fin_cases pair <;> cases upper <;> decide
  · change vCopyPc pair + (if upper then 1 else 0) < 1862
    fin_cases pair <;> cases upper <;> decide

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
