-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryAllFragmentsReuse
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputBank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Correction (outputElementAccess)
open Thread.Correction (StageZeroStagingWrites)

/-- An overlap with any staging element forces stage zero and discharges the
write-to-write conflict through that stage's observed output completion. -/
theorem tensorIntentBeforeStagingElement {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input writer : EvId} {loc : Loc} {data : List Byte} {a : Acc}
    {stage : Fin 2} {subbox : Fin 4} {qx qy qbyte x row : Nat}
    (hIntent : X.Intent (.async input (.write (.load qx qy qbyte))) a true)
    (hInput : a.Covers loc) (hx : x < 32) (hy : row < 128)
    (hStore : stage = 0 → StageZeroStagingWrites X writer
      (outputElementAccess l writer.1 stage subbox x row) data)
    (hOutput : (outputElementAccess l writer.1 stage subbox x row).Covers loc) :
    stage = 0 ∧ X.AsyncPresent input (.write (.load qx qy qbyte)) ∧
      ByteCausality l X loc (.async input (.write (.load qx qy qbyte))) (.thread writer) := by
  obtain ⟨_, _, _, hBox, hByte⟩ :=
    Thread.queryOfOverlappingTensorIntent hp hX hIntent hInput hx hy hOutput
  have hStage := (Thread.querySubboxOfCorrectionOverlap hBox hByte hx hy hOutput).1
  have hStaging := hStore hStage
  subst stage
  obtain ⟨wait, hWait, hLater⟩ := hStaging.firstAcquire hp hX
  exact ⟨rfl, queryIntentBeforeCorrection hp hX hBox hByte hWait hLater
    hStaging.writes hx hy hOutput⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
