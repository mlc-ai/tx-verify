-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVFromK
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVMaskArithmetic
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVAdmission
import Kernels.TmlFa4Fwd.Flow.Code.Part010

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

def primingMaskCountPc (n : Nat) : Nat :=
  if n = 0 then 543 else 550 + 8 * (n - 1) + if n - 1 < 8 then 0 else 1

def primingMaskPrefix (len tile tid count : Nat) : List (Nat × Value) :=
  ((List.finRange 16).take count).map (primingMaskFact len tile tid)

def primingMaskBaseFrame (p : Params) (l : Launch)
    (batch queryHead queryTile tile warp lane : Nat) : List (Nat × Value) :=
  let tid := 32 * warp + lane
  (1852, b32 (primingMaskWord (p.kLength batch) tile tid)) ::
    primingMaskPred (p.kLength batch) tile tid 0 ::
    primingKMaskInputs p l batch tile warp lane ++
      primingVAdmissionCarry p l batch queryHead queryTile

def primingMaskFrame (p : Params) (l : Launch)
    (batch queryHead queryTile tile warp lane count : Nat) : List (Nat × Value) :=
  primingMaskPrefix (p.kLength batch) tile (32 * warp + lane) count ++
    primingMaskBaseFrame p l batch queryHead queryTile tile warp lane

variable {p : Params} {l : Launch} {g batch queryHead queryTile tile warp lane : Nat}
    (hLen : p.kLength batch < 2 ^ 31) (hRow : kvCopyRow tile (32 * warp + lane) 0 < 2 ^ 31)
include hLen hRow

end
end PTX.Kernels.TmlFa4Fwd.Loader
