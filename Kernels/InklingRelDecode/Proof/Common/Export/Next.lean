-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.Export.DataNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Sched

def FailsAt (L : Launch) (m : Mem0) (X : Execution) (g pc : Nat) : Prop :=
  ∃ l q sc, NextEv L kernel Assumptions.all m X g ⟨pc,.wait l q false true sc⟩

end PTX.Kernels.InklingRelDecode.Proof
