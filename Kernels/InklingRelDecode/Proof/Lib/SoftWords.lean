-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.Alpha
public import Kernels.InklingRelDecode.Proof.Lib.SoftFold
public import Kernels.InklingRelDecode.Proof.Lib.EvWord
public import Lemmas.Flow.OutKinds

@[expose] public section

/-! # The words of a row's rounds

The carried maximum (register 1914) and sum (register 1915) after a round, as functions of the
words the round brought: the halves' maxima (pc 1838), the lane's and its partner's sums (pc 2234)
and the words before (`lmAfter`). A round's words are exact (`RoundOk`) when they are the exact
words of the fold's block relative to the state before. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof PTX.Assumption Lib.SoftFold Classical

noncomputable section

/-- The words of a round: the maxima of the two halves and the two halves' sums. -/
structure Rw where
  a : Value
  b : Value
  s : Value
  r : Value

/-- The running sum after a round (pcs 2235 and 950). -/
def lNext (l f s r : Value) : Value := lStep l f (psWord s r)

/-- The carried maximum and sum after a round. -/
def lmNext (c : Value) (p : Value × Value) (w : Rw) : Value × Value :=
  (Lib.mNext c p.1 (Lib.mxWord p.1 w.a w.b),
    lNext p.2 (Lib.alphaVal c p.1 (Lib.mxWord p.1 w.a w.b) 507) w.s w.r)

/-- The carried maximum and sum after the rounds. -/
def lmAfter (c : Value) (rs : List Rw) : Value × Value :=
  rs.foldl (lmNext c) (b32 4286578688, b32 0)

/-- The exponent of a key relative to the maximum used. -/
def pExp (sl mUse : ℝ) (q : ℝ × ℝ) : ℝ := (2 : ℝ) ^ (sl * q.1 - mUse * sl)

/-- The maximum a block's exponents are taken relative to (`SoftFold.step`'s `mUse`). -/
def mUseOf (sl : ℝ) (blk : List (ℝ × ℝ)) (st : St) : ℝ :=
  if Keep (alphaLog2 sl st.m (max st.m (blockMax blk))) then st.m.toReal
  else mSafe (max st.m (blockMax blk))

theorem step_l (sl : ℝ) (blk : List (ℝ × ℝ)) (st : St) :
    (step sl blk st).l = st.l * (if Keep (alphaLog2 sl st.m (max st.m (blockMax blk))) then 1
      else pow2 (alphaLog2 sl st.m (max st.m (blockMax blk)))) +
      (blk.map (pExp sl (mUseOf sl blk st))).sum := rfl

/-- **A round's words are exact**: the halves' maxima, and sums that add up to the block's. -/
def RoundOk (sl : ℝ) (st : St) (w : Rw) (blk : List (ℝ × ℝ)) : Prop :=
  ∃ (aE bE : EReal) (u v : ℝ), Ev w.a aE ∧ Ev w.b bE ∧ max aE bE = blockMax blk ∧
    Ev w.s (u : EReal) ∧ Ev w.r (v : EReal) ∧
    u + v = (blk.map (pExp sl (mUseOf sl blk st))).sum


end
end PTX.Kernels.InklingRelDecode.Proof.Lib
