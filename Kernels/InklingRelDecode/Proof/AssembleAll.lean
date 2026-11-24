-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.AssembleBase
public import Kernels.InklingRelDecode.Proof.AssembleDispatch
public import Kernels.InklingRelDecode.Proof.AssembleLock
public import Kernels.InklingRelDecode.Proof.AssembleLk4
public import Kernels.InklingRelDecode.Proof.AssembleProtocol
public import Kernels.InklingRelDecode.Proof.AssembleProgress
public import Kernels.InklingRelDecode.Proof.AssembleResult

/-!
# The assembly of the open premises from the proved theorems: umbrella

* `AssembleBase`: `Base` (thread facts, `GoodP`), `RoleReads`, `NumWordRead`, `BaseWordRead`;
* `AssembleDispatch`: `Bound.DispatchBound` (`R = 3`) from `RoleReads` and the phase counts;
* `AssembleProtocol`: `Safety.Protocol` from `ProtocolRest`;
* `AssembleProgress`: `Progress.Remaining` (every field proved);
* `AssembleResult`: `Result.Out.Inputs` from `InputsRest`.

`Correct.lean` collects the premises that nothing proves in `Open`.
-/
