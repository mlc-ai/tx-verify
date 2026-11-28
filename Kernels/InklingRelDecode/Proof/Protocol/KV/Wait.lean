-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Next

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Sched

def Waiting (L : Launch) (m : Mem0) (X : Execution) (r : Ring) (c : Nat) (s : Fin 3) (g : Nat) :=
  g / L.block = c ∧ ∃ q sc, NextEv L kernel Assumptions.all m X g
    ⟨r.site,.wait (r.obj L c s) q false true sc⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
