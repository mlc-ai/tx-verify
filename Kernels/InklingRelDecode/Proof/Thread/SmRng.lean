-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmScZ
public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-!
# The score stage's range premise follows from `Pre`

The integer arithmetic of the score stage (the key `128 n`, the positions of the query token and
the columns, `past / 128`) stays below `2 ^ 31` (`Rng`, `SmScZ`). For an iteration `i` of the
loop (`i < num_iters`) of request `r` and split `s` this follows from `Pre.seqRange`
(`seqlen_k + 511 < 2 ^ 31`): the block number is below `cdiv(seqlen_k, 128)`, so
`128 n + 256 ≤ seqlen_k + 255`, and `past + 128 ≤ seqlen_k + 128`, `past / 128 ≤ past`.

`EntSeq` is the part of the meaning of the entry numbers the range needs (the fields of
`SmEntry.entOf`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The entry numbers the range needs: request `r`'s `past`, `past / 128`, `num_iters`, the split
and `num_splits`. -/
structure EntSeq (P : Params) (r s : Nat) (e : Ent) : Prop where
  past : e.past = P.past r
  r23 : e.r23 = P.past r / 128
  r26 : e.r26 = P.numIters r s
  split : e.split = s
  splits : e.splits = P.splits

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
