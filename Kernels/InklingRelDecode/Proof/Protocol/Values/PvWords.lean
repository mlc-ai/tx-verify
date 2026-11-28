-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvVals
public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsScore
public import Kernels.InklingRelDecode.Proof.Lib.PvFold
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord

@[expose] public section

/-! # What the softmax role owes the accumulator

The probability words `pw` and the rescale factors `al` of a row are the fold's (`FoldWords`); the
words of a rescale store are its factor times the word of the accumulator load before it
(`RescaleAl`); a round without a rescale store covering a cell has factor one (`NoRescaleAl`).
`closedAcc` is the accumulator these give after `n` blocks. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma Tmem Lib.SoftRow Finset

/-- The coordinates of a CTA. -/
abbrev ctaZ (L : Launch) (c : Nat) : Nat := (L.ctaidOf c).get .z
abbrev ctaY (L : Launch) (c : Nat) : Nat := (L.ctaidOf c).get .y
abbrev ctaXc (L : Launch) (c : Nat) : Nat := (L.ctaidOf c).get .x

/-- **The probability words and the factors of a row are the fold's.** -/
structure FoldWords (Q : Params) (L : Launch) (pw : Nat → Nat → Nat → Nat → ℝ)
    (al : Nat → Nat → Nat → ℝ) : Prop where
  p : ∀ c row d b κ, Lib.QRowValid Q L c row → κ < 128 → pw c b row κ =
    if 128 * (Q.splits * b + ctaXc L c) + κ ∈
        blockKeys Q (ctaZ L c) (ctaXc L c) (row / 6) b then
      Lib.pExp (Q.scale * log2eF32) (Lib.mUseOf (Q.scale * log2eF32)
        (kBlk Q (ctaZ L c) (ctaXc L c) (row / 6) (ctaY L c * 6 + row % 6) d b)
        (kSt Q (ctaZ L c) (ctaXc L c) (row / 6) (ctaY L c * 6 + row % 6) d b))
        (keyPair Q (ctaZ L c) (row / 6) (ctaY L c * 6 + row % 6) d
          (128 * (Q.splits * b + ctaXc L c) + κ))
    else 0
  a : ∀ c row d b, Lib.QRowValid Q L c row → al c b row =
    stepAlpha (Q.scale * log2eF32)
      (kBlk Q (ctaZ L c) (ctaXc L c) (row / 6) (ctaY L c * 6 + row % 6) d b)
      (kSt Q (ctaZ L c) (ctaXc L c) (row / 6) (ctaY L c * 6 + row % 6) d b)

/-- **A rescale store of a row that loads writes its factor times the load's word.** -/
def RescaleAl (Q : Params) (L : Launch) (X : Execution) (al : Nat → Nat → Nat → ℝ) : Prop :=
  ∀ t k a vals sh kl a' ov sh' jj,
    Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a jj).lane) →
    X.get (t, k) = some ⟨2328, .tc (.st a vals sh)⟩ →
    X.get (t, kl) = some ⟨2260, .tc (.ld a' ov sh')⟩ →
    pollRound 1257 ((X.tr t).take kl) = pollRound 1257 ((X.tr t).take k) → jj < vals.length →
    ∃ x : ℝ, ov[jj]? = some (.float .f32 x) ∧ vals[jj]? = some (.float .f32
      (al (t / L.block) (pollRound 1257 ((X.tr t).take k) - 1)
        (laneRow (tcDataCell L t sh a jj).lane) * x))

/-- **A cell no rescale store covers in a round that runs has the factor one in it.** -/
def NoRescaleAl (Q : Params) (L : Launch) (X : Execution) (al : Nat → Nat → Nat → ℝ) : Prop :=
  ∀ c b row col, c < L.grid → row < 64 → col < 128 → Lib.QRowValid Q L c row →
    0 < b → b < Q.numIters (ctaZ L c) (ctaXc L c) →
    (∀ st, ¬ RescaleAt L X st b ⟨c, 32 * (row / 16) + row % 16, 256 + col⟩) → al c b row = 1

/-- The accumulator of a row and column after `n` blocks. -/
noncomputable def closedAcc (Q : Params) (L : Launch) (pw : Nat → Nat → Nat → Nat → ℝ)
    (al : Nat → Nat → Nat → ℝ) (c row col n : Nat) : ℝ :=
  clAcc (fun k => (keyPair Q (ctaZ L c) (row / 6) (ctaY L c * 6 + row % 6) col k).2)
    (fun b κ => pw c b row κ) (fun b => al c b row) Q.splits (ctaXc L c) n

/-- **The closed form is the fold's numerator** when the words are the fold's. -/
theorem closedAcc_eq {Q : Params} {L : Launch} {pw : Nat → Nat → Nat → Nat → ℝ}
    {al : Nat → Nat → Nat → ℝ} (F : FoldWords Q L pw al) {c row : Nat}
    (v : Lib.QRowValid Q L c row) (col n : Nat) :
    closedAcc Q L pw al c row col n = (kSt Q (ctaZ L c) (ctaXc L c) (row / 6)
      (ctaY L c * 6 + row % 6) col n).o :=
  clAcc_eq Q _ _ _ _ _ n (fun b _ κ hκ => F.p c row col b κ v hκ)
    (fun b _ => F.a c row col b v)

/-- The cache element of a PV step is the value of its key. -/
theorem pv_v_elem (Q : Params) (L : Launch) (c b i kk row col : Nat) (_hi : i < 8) (hk : kk < 16)
    (_hc : col < 128) :
    kvElem Q L c b 1 (i / 4) (col / 64) (col % 64) (16 * (i % 4) + kk) =
      (keyPair Q (ctaZ L c) (row / 6) (ctaY L c * 6 + row % 6) col
        (128 * (Q.splits * b + ctaXc L c) + (16 * i + kk))).2 := by
  have hy : (ctaY L c * 6 + row % 6) / group = ctaY L c := by
    unfold group
    omega
  unfold kvElem keyPair pair Params.vVal Params.kvRow
  rw [hy]
  have e1 : (128 * (Q.splits * b + ctaXc L c) + (16 * i + kk)) / 64 =
      2 * (Q.splits * b + ctaXc L c) + i / 4 := by omega
  have e2 : (128 * (Q.splits * b + ctaXc L c) + (16 * i + kk)) % 64 = 16 * (i % 4) + kk := by
    omega
  have e3 : headDim + col = 128 * 1 + 64 * (col / 64) + col % 64 := by
    show 128 + col = _
    omega
  simp only [e1, e2, add_assoc, e3]

/-- **The sum of the products of a PV block's steps** is the sum over its 128 keys. -/
theorem pv_block_sum (Q : Params) (L : Launch) (pw : Nat → Nat → Nat → Nat → ℝ) (c b row col : Nat)
    (hc : col < 128) :
    ∑ i ∈ range 8, ∑ kk ∈ range 16, pw c b row (16 * i + kk) *
        kvElem Q L c b 1 (i / 4) (col / 64) (col % 64) (16 * (i % 4) + kk) =
      ∑ κ ∈ range 128, pw c b row κ * (keyPair Q (ctaZ L c) (row / 6) (ctaY L c * 6 + row % 6)
        col (128 * (Q.splits * b + ctaXc L c) + κ)).2 := by
  rw [show (128 : Nat) = 16 * 8 from rfl, sum_blocks16 (fun κ => pw c b row κ * (keyPair Q
    (ctaZ L c) (row / 6) (ctaY L c * 6 + row % 6) col (128 * (Q.splits * b + ctaXc L c) + κ)).2) 8]
  refine sum_congr rfl fun i hi => sum_congr rfl fun kk hk => ?_
  rw [pv_v_elem Q L c b i kk row col (mem_range.1 hi) (mem_range.1 hk) hc]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
