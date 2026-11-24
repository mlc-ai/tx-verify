-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasSequence
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMax
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMaskWord

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow

/-- The three registers connecting one affine bias result to two masked logits. -/
structure MaskPairRegs where
  packed : Nat
  low : Nat
  high : Nat

def firstMaskGroupStart (group : Nat) : Nat := 3876 + 114 * group

def firstMaskGroupCode (group : Nat) : List Instr :=
  ((Decoded.code121 ++ Decoded.code122 ++ Decoded.code123 ++ Decoded.code124 ++
    Decoded.code125 ++ Decoded.code126 ++ Decoded.code127 ++ Decoded.code128 ++
    Decoded.code129 ++ Decoded.code130 ++ Decoded.code131 ++ Decoded.code132 ++
    Decoded.code133 ++ Decoded.code134 ++ Decoded.code135).drop
    (firstMaskGroupStart group - 3872)).take 111

end PTX.Kernels.TmlFa4Fwd.Softmax
