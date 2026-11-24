-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryStageReuse
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputBank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread
open PTX.Kernels.TmlFa4Fwd.Correction (outputElementAccess)
open Thread.Correction (FirstOutputAcquire)

/-- The initial output acquire orders every overlapping Q0 or Q1 transfer intent before the
actual correction store. The issue already wrote the byte even when the execution is suspended. -/
theorem queryIntentBeforeCorrection {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input wait writer : EvId} {s : TensorCopy.Spec} {loc : Loc} {bytes : List Byte}
    {qStage plane correctionStage : Fin 2} {subbox : Fin 4} {qx qy qbyte x row : Nat}
    (hBox : Loader.QuerySubbox p l X input qStage plane s)
    (hQuery : TensorCopy.writeLoc s qx qy qbyte = some loc)
    (hWait : FirstOutputAcquire l X wait) (hLater : po X wait writer)
    (hWrite : X.Writes writer (outputElementAccess l writer.1 correctionStage subbox x row) bytes)
    (hx : x < 32) (hy : row < 128)
    (hCover : (outputElementAccess l writer.1 correctionStage subbox x row).Covers loc) :
    X.AsyncPresent input (.write (.load qx qy qbyte)) ∧
      ByteCausality l X loc (.async input (.write (.load qx qy qbyte))) (.thread writer) :=
  queryIntentBeforeCorrectionOfBank hp hX hBox hQuery hWait hLater hWrite hx hy hCover
    (fun _ _ he => firstOutputCommitQueryBank hp hX he qStage)

end PTX.Kernels.TmlFa4Fwd.Protocol
