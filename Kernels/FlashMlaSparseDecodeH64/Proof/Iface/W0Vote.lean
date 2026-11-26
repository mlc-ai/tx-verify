-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value

@[expose] public section

/-! # The input of warpgroup 0's rescale vote

The vote at pc 578 takes, per lane, the predicate `r21 - m > 6.0` where `r21` is the larger of the
lane's scaled row maximum and the peer's (`w0Loc`, `w0FE pm` of the block in progress) and `m` the
carried maximum (`ftz` comparison, extended reals). `w0VoteArg` is that bit from the block's words
and the carried maximum; `w0VoteIn` from a trace. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Assumption

noncomputable section

/-- The vote's predicate of a block with words `w`, scale `sc` and carried maximum `m`. -/
def w0VoteArg (sc : ℝ) (w : W0Words) (m : ℝ) : Bool :=
  erealCompare .gt (max (w0Loc sc w) (w0FE w.pm) + -(m : EReal)) ((6 : ℝ) : EReal)

/-- The vote's predicate depends on the words only through the larger of the two maxima. -/
theorem w0VoteArg_of_max {sc : ℝ} {w w' : W0Words} {m : ℝ}
    (h : max (w0Loc sc w) (w0FE w.pm) = max (w0Loc sc w') (w0FE w'.pm)) :
    w0VoteArg sc w m = w0VoteArg sc w' m := by
  unfold w0VoteArg
  rw [h]

/-- The vote's predicate at the end of the trace `l`: the block in progress against the maximum
the finished blocks carried. -/
def w0VoteIn (sc : ℝ) (l : List Event) : Bool :=
  w0VoteArg sc (w0Words (w0Fin l).2) (w0Carry sc (w0Fin l).1).1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
