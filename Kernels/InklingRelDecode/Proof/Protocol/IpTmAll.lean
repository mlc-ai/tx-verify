-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Tmem
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmAlloc
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmSmBase
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmIssue

@[expose] public section

/-!
# The Tensor Memory resource facts and the MMA instruction branch (umbrella)

* `Proof2.tmem1Facts` (`Proof2/Safety/Tmem.lean`): `Tmem1Facts L X 0`, on the second tree's role
  table;
* `Tmem1.allocWordZero` (`IpTmAlloc`): `Interface.AllocWordZero`;
* `Rs.smBaseZero` (`IpTmSmBase`): `Rs.SmBaseZero`;
* `Tmem1.tcInstr_of` (`IpTmIssue`): `Safety.Protocol.tcInstr`, from the issue shape, no copy, no
  collector reuse and `CompletedValues`.
-/
