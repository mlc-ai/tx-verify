-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.SoftKernel
public import Kernels.InklingRelDecode.Proof.Lib.SoftWords
import Kernels.InklingRelDecode.Proof.Softmax.Data.LExact
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Fin
import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskFin
import Kernels.InklingRelDecode.Proof.Softmax.Data.MaskConst
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Score
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpInXw
import Kernels.InklingRelDecode.Proof.Softmax.Data.PredIn
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleOrder
import Kernels.InklingRelDecode.Proof.Softmax.Soft.Ledger
import Kernels.InklingRelDecode.Proof.Softmax.Soft.CurStep
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasEv
import Kernels.InklingRelDecode.Proof.Lib.SoftLane
import Kernels.InklingRelDecode.Proof.Lib.ScoreEv
import Kernels.InklingRelDecode.Proof.Softmax.Soft.ScoreAt
import Kernels.InklingRelDecode.Proof.Softmax.Export.RecvHalf
import Kernels.InklingRelDecode.Proof.Softmax.Export.PwordEv
import Kernels.InklingRelDecode.Proof.Softmax.Data.ScaleEv
import Kernels.InklingRelDecode.Proof.Lib.FoldPw
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleEv

@[expose] public section

/-! # The carried maximum and sum of a row are the fold's

The words a lane carries (the running maximum and the running sum) after the rounds of a row, when
the words of every round are exact (`Ev`): the halves' maxima, and the lane's and its partner's
sums, which add up to the block's sum relative to the maximum the round used. The words are
`SoftFold.run`'s state, so the row's `kState` is read off the registers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Proof Lib.SoftFold

/-- **The registers after the rounds read as the fold's state.** The initial maximum is `-inf` and
the initial sum zero; `rs` are the rounds' words and `bs` the row's blocks. -/
public theorem lm_state {c : Value} {sc : ℝ} (hc : Lib.Ev c sc) (hpos : 0 < sc) (rs : List Lib.Rw)
    (bs : List (List (ℝ × ℝ))) (len : rs.length = bs.length)
    (ok : ∀ j st', j < rs.length → st' = (bs.take j).foldl (fun s b => step sc b s) ⟨⊥, 0, 0⟩ →
      ∀ w blk, rs[j]? = some w → bs[j]? = some blk → Lib.RoundOk sc st' w blk) :
    Lib.Ev (Lib.lmAfter c rs).1 (Lib.SoftFold.run sc bs).m ∧
      Lib.Rd (Lib.lmAfter c rs).2 ((Lib.SoftFold.run sc bs).l : EReal) :=
  Data.lmAfter_ev hc hpos rs bs (b32 4286578688, b32 0) ⟨⊥, 0, 0⟩ Data.ev_bot Data.rd_zero ok len

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
