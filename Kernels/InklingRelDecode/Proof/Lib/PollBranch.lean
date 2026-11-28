-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.CtlSteps
import Lemmas.Flow.SegPieces

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

/-- The retry branches are a single negated, uniform branch back to the poll. -/
theorem poll_branch {L g pc r target F} (pick : Bool)
    (hc : kernel.code[pc]? = some ⟨some (r,true),.bra target true⟩)
    (hs : Assumptions.emuSites.contains pc = false) :
    SegU kernel Assumptions.all L g pc ((r,.pred pick)::F) (if pick then pc+1 else target) F := by
  intro t ht
  obtain ⟨pc0,sub,acc,fault,hp,tail⟩ := ht
  obtain ⟨u,h,hu⟩ := run_braNot hc pick ⟨pc0,sub,acc,fault,tail⟩ hp (Lib.bra_rule t) (segFree hs)
  exact .inl ⟨u,run_rtg h,hu⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
