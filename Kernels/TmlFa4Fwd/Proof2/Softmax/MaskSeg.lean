-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SegSym
public import Lemmas.Flow.MaskMax
public import Kernels.TmlFa4Fwd.Flow.Code
public import Kernels.TmlFa4Fwd.Flow.Sites
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Base

@[expose] public section

/-! # The first round's masked maximum: the code's terms

The first round applies the causal mask to its 128 bias products (pcs 3872 to 4329) and folds the
maximum (pcs 4329 to 4397). The mask is four 32-bit words `mword k m = 0xffffffff >>> max(32 (k + 1)
- m, 0)` of the mask count `m` (`%r2175`); element `i` of word `k` keeps its score when bit `i` of
the word is set, tested as the code tests it (`setp.ne` of `and … 1` for bit 0, `setp.eq` of `and …
2^i` for bits 1 to 30, `setp.gt.s32 … -1` for bit 31), and is `-∞` otherwise (`mkeep0`, `mdrop`,
`mdrop31`). A bias product is the `f32` number of the scaled bias plus the score, or `-∞` when the
bias element is the masked pattern (`bv32`, read as `bpe`), so the maximum may be `-∞`. The terms
mirror the code (rule M2), so the walk's values close by `rfl`; the closed form over the set bits is
`Lemmas/Flow/MaskMax.lean`'s `maskMax`. The role opts in to conditional `selp` values
(`sym_selp_value`), so each select is one step. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The role's floating `selp`s write conditional values (lane L's opt-in). -/
scoped macro_rules | `(tactic| sym_selp_value) => `(tactic| skip)

/-- The shift of mask word `k`: `max.s32 (32 (k + 1) - m) 0`. -/
def mshift (k : Nat) (m : BitVec 64) : BitVec 64 :=
  let s := sub32 (i32 (32 * (k + 1))) m
  if compare (if true = true then Cmp.gt else Cmp.lt) .s 32 (r32 s) (i32 0) = true then r32 s
  else i32 0

/-- Mask word `k`: `shr.u32 -1, mshift k m`. -/
def mword (k : Nat) (m : BitVec 64) : BitVec 64 :=
  if (r32 (mshift k m)).toNat ≥ 32 then 0 else r32 (i32 (-1)) >>> (r32 (mshift k m)).toNat

/-- Bit 0 of mask word `k` keeps its element (`setp.ne.b32 (and … 1), 0`). -/
def mkeep0 (k : Nat) (m : BitVec 64) : Bool :=
  compare .ne .b 32 (r32 (andi (mword k m) 1)) (i32 0)

/-- Bit `i` (1 to 30) of mask word `k` drops its element (`setp.eq.b32 (and … 2^i), 0`). -/
def mdrop (k : Nat) (m : BitVec 64) (i : Nat) : Bool :=
  compare .eq .b 32 (r32 (andi (mword k m) (2 ^ i))) (i32 0)

/-- Bit 31 of mask word `k` drops its element (`setp.gt.s32 …, -1`). -/
def mdrop31 (k : Nat) (m : BitVec 64) : Bool := compare .gt .s 32 (r32 (mword k m)) (i32 (-1))

/-- The reading of element `i` of mask word `k` with the extended real `x` (a bias product, `⊥`
when its bias is masked): `x` when kept, `⊥` (the reading of `-∞`) otherwise. -/
def mre (k : Nat) (m : BitVec 64) (i : Nat) (x : EReal) : EReal :=
  if i = 0 then (if mkeep0 k m = true then x else ⊥)
  else if i < 31 then (if mdrop k m i = true then ⊥ else x)
  else if mdrop31 k m = true then ⊥ else x

/-- A bias product as the code holds it: the `f32` number `sc n` when its bias is a payload
(`bf n`), the pattern of `-∞` when its bias is the masked pattern. -/
abbrev bv32 (bf : Nat → Bool) (sc : Nat → ℝ) (n : Nat) : Value :=
  if bf n = true then .float .f32 (sc n) else .bits 32 (BitVec.ofNat 64 4286578688)

/-- The reading of a bias product: its real when finite (`bf n`), `⊥` when its bias is masked. -/
def bpe (bf : Nat → Bool) (sc : Nat → ℝ) (n : Nat) : EReal :=
  if bf n = true then (sc n : EReal) else ⊥

/-- The fold of the 128 readings as the code's `max.f32` tree computes it (four accumulators,
pcs 4329 to 4394; a three-operand `max` is the maximum of the first two, then the third). -/
def foldM (m : BitVec 64) (sc : Nat → EReal) : EReal :=
  let a3620 := max (mre 0 m 0 (sc 0)) (mre 0 m 1 (sc 1))
  let a3621 := max (mre 0 m 2 (sc 2)) (mre 0 m 3 (sc 3))
  let a3622 := max (mre 0 m 4 (sc 4)) (mre 0 m 5 (sc 5))
  let a3623 := max (mre 0 m 6 (sc 6)) (mre 0 m 7 (sc 7))
  let a3624 := max (max a3620 (mre 0 m 8 (sc 8))) (mre 0 m 9 (sc 9))
  let a3625 := max (max a3621 (mre 0 m 10 (sc 10))) (mre 0 m 11 (sc 11))
  let a3626 := max (max a3622 (mre 0 m 12 (sc 12))) (mre 0 m 13 (sc 13))
  let a3627 := max (max a3623 (mre 0 m 14 (sc 14))) (mre 0 m 15 (sc 15))
  let a3628 := max (max a3624 (mre 0 m 16 (sc 16))) (mre 0 m 17 (sc 17))
  let a3629 := max (max a3625 (mre 0 m 18 (sc 18))) (mre 0 m 19 (sc 19))
  let a3630 := max (max a3626 (mre 0 m 20 (sc 20))) (mre 0 m 21 (sc 21))
  let a3631 := max (max a3627 (mre 0 m 22 (sc 22))) (mre 0 m 23 (sc 23))
  let a3632 := max (max a3628 (mre 0 m 24 (sc 24))) (mre 0 m 25 (sc 25))
  let a3633 := max (max a3629 (mre 0 m 26 (sc 26))) (mre 0 m 27 (sc 27))
  let a3634 := max (max a3630 (mre 0 m 28 (sc 28))) (mre 0 m 29 (sc 29))
  let a3635 := max (max a3631 (mre 0 m 30 (sc 30))) (mre 0 m 31 (sc 31))
  let a3636 := max (max a3632 (mre 1 m 0 (sc 32))) (mre 1 m 1 (sc 33))
  let a3637 := max (max a3633 (mre 1 m 2 (sc 34))) (mre 1 m 3 (sc 35))
  let a3638 := max (max a3634 (mre 1 m 4 (sc 36))) (mre 1 m 5 (sc 37))
  let a3639 := max (max a3635 (mre 1 m 6 (sc 38))) (mre 1 m 7 (sc 39))
  let a3640 := max (max a3636 (mre 1 m 8 (sc 40))) (mre 1 m 9 (sc 41))
  let a3641 := max (max a3637 (mre 1 m 10 (sc 42))) (mre 1 m 11 (sc 43))
  let a3642 := max (max a3638 (mre 1 m 12 (sc 44))) (mre 1 m 13 (sc 45))
  let a3643 := max (max a3639 (mre 1 m 14 (sc 46))) (mre 1 m 15 (sc 47))
  let a3644 := max (max a3640 (mre 1 m 16 (sc 48))) (mre 1 m 17 (sc 49))
  let a3645 := max (max a3641 (mre 1 m 18 (sc 50))) (mre 1 m 19 (sc 51))
  let a3646 := max (max a3642 (mre 1 m 20 (sc 52))) (mre 1 m 21 (sc 53))
  let a3647 := max (max a3643 (mre 1 m 22 (sc 54))) (mre 1 m 23 (sc 55))
  let a3648 := max (max a3644 (mre 1 m 24 (sc 56))) (mre 1 m 25 (sc 57))
  let a3649 := max (max a3645 (mre 1 m 26 (sc 58))) (mre 1 m 27 (sc 59))
  let a3650 := max (max a3646 (mre 1 m 28 (sc 60))) (mre 1 m 29 (sc 61))
  let a3651 := max (max a3647 (mre 1 m 30 (sc 62))) (mre 1 m 31 (sc 63))
  let a3652 := max (max a3648 (mre 2 m 0 (sc 64))) (mre 2 m 1 (sc 65))
  let a3653 := max (max a3649 (mre 2 m 2 (sc 66))) (mre 2 m 3 (sc 67))
  let a3654 := max (max a3650 (mre 2 m 4 (sc 68))) (mre 2 m 5 (sc 69))
  let a3655 := max (max a3651 (mre 2 m 6 (sc 70))) (mre 2 m 7 (sc 71))
  let a3656 := max (max a3652 (mre 2 m 8 (sc 72))) (mre 2 m 9 (sc 73))
  let a3657 := max (max a3653 (mre 2 m 10 (sc 74))) (mre 2 m 11 (sc 75))
  let a3658 := max (max a3654 (mre 2 m 12 (sc 76))) (mre 2 m 13 (sc 77))
  let a3659 := max (max a3655 (mre 2 m 14 (sc 78))) (mre 2 m 15 (sc 79))
  let a3660 := max (max a3656 (mre 2 m 16 (sc 80))) (mre 2 m 17 (sc 81))
  let a3661 := max (max a3657 (mre 2 m 18 (sc 82))) (mre 2 m 19 (sc 83))
  let a3662 := max (max a3658 (mre 2 m 20 (sc 84))) (mre 2 m 21 (sc 85))
  let a3663 := max (max a3659 (mre 2 m 22 (sc 86))) (mre 2 m 23 (sc 87))
  let a3664 := max (max a3660 (mre 2 m 24 (sc 88))) (mre 2 m 25 (sc 89))
  let a3665 := max (max a3661 (mre 2 m 26 (sc 90))) (mre 2 m 27 (sc 91))
  let a3666 := max (max a3662 (mre 2 m 28 (sc 92))) (mre 2 m 29 (sc 93))
  let a3667 := max (max a3663 (mre 2 m 30 (sc 94))) (mre 2 m 31 (sc 95))
  let a3668 := max (max a3664 (mre 3 m 0 (sc 96))) (mre 3 m 1 (sc 97))
  let a3669 := max (max a3665 (mre 3 m 2 (sc 98))) (mre 3 m 3 (sc 99))
  let a3670 := max (max a3666 (mre 3 m 4 (sc 100))) (mre 3 m 5 (sc 101))
  let a3671 := max (max a3667 (mre 3 m 6 (sc 102))) (mre 3 m 7 (sc 103))
  let a3672 := max (max a3668 (mre 3 m 8 (sc 104))) (mre 3 m 9 (sc 105))
  let a3673 := max (max a3669 (mre 3 m 10 (sc 106))) (mre 3 m 11 (sc 107))
  let a3674 := max (max a3670 (mre 3 m 12 (sc 108))) (mre 3 m 13 (sc 109))
  let a3675 := max (max a3671 (mre 3 m 14 (sc 110))) (mre 3 m 15 (sc 111))
  let a3676 := max (max a3672 (mre 3 m 16 (sc 112))) (mre 3 m 17 (sc 113))
  let a3677 := max (max a3673 (mre 3 m 18 (sc 114))) (mre 3 m 19 (sc 115))
  let a3678 := max (max a3674 (mre 3 m 20 (sc 116))) (mre 3 m 21 (sc 117))
  let a3679 := max (max a3675 (mre 3 m 22 (sc 118))) (mre 3 m 23 (sc 119))
  let a3680 := max (max a3676 (mre 3 m 24 (sc 120))) (mre 3 m 25 (sc 121))
  let a3681 := max (max a3677 (mre 3 m 26 (sc 122))) (mre 3 m 27 (sc 123))
  let a3682 := max (max a3678 (mre 3 m 28 (sc 124))) (mre 3 m 29 (sc 125))
  let a3683 := max (max a3679 (mre 3 m 30 (sc 126))) (mre 3 m 31 (sc 127))
  let a3684 := max a3680 a3681
  let a7256 := max (max a3684 a3682) a3683
  a7256

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
