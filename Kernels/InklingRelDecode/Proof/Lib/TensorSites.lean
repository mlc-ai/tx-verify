-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.NotTensor
import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

def preloadPcs : List Nat := [211,217,226,231,253,259,268,273,295,301,310,315]

private def workerPcs : List Nat := [2389,2391,2394,2396,2404,2406,2410,2412]

private theorem all_sites : OpPcsFast kernel.code tensorOp (preloadPcs++workerPcs)=true := by
  decide +kernel

theorem tensor_issue_site {L m X g k pc addr sp}
    (hX : Consistent L kernel Assumptions.all m X)
    (event : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩) :
    pc ∈ preloadPcs ∨ pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412] := by
  obtain ⟨_,bad⟩|⟨_,ins,_,_,code,fire⟩ := get_source hX event
  · cases bad
  have op : tensorOp ins.op=true := by
    cases test : tensorOp ins.op with
    | true => rfl
    | false => exact (fires_notTensor (eventTmpl_notTensor test) fire addr sp rfl).elim
  exact List.mem_append.mp (OpPcsFast.mem all_sites code op)

end PTX.Kernels.InklingRelDecode.Proof.Lib
