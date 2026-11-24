-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondReload
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPairSites
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

def warmKInputPc (pair : Fin 16) : Nat :=
  if pair.val = 0 then 1004 else if pair.val < 8 then 1008 else 1073

def warmKInputRank (pair : Fin 16) : Nat :=
  if pair.val = 0 then 64 else if pair.val < 8 then 66 else 80

def warmKInputRow (tile tid : Nat) (pair : Fin 16) : Nat :=
  primingLaneRow tile tid + if pair.val < 8 then 0 else 64

def warmKInputColumn (tid : Nat) (pair : Fin 16) : Nat × Value :=
  if pair.val = 0 then (1119, b32 (8 * (tid % 8))) else (7666, b64 (16 * (tid % 8)))

def warmKSlotWords (pair : Fin 16) (ptr tid : Nat) : List (Nat × Value) :=
  [(warmKShuffleInput pair, b32 (ptr % 2 ^ 32)),
    (warmKShuffleInput pair + 1, b32 (ptr / 2 ^ 32)),
    warmKInputColumn tid pair]

end
end PTX.Kernels.TmlFa4Fwd.Loader
