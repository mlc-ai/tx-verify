-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Machine
public import Kernels.TmlFa4Fwd.Proof2.Softmax.PlainFold
public import Kernels.TmlFa4Fwd.Proof2.Softmax.BiasFold
public import Lemmas.Flow.Step.SiteShape
public import Kernels.TmlFa4Fwd.Proof2.Softmax.MaskSeg
public import Kernels.TmlFa4Fwd.Proof2.Softmax.Gen.Expo1

@[expose] public section

/-! # The softmax machine with its data plane

`codeD` is the softmax machine `code` whose facts also name data registers: the registers live at
the state's instruction that are control registers (`ctl`) or named data registers (`dnamed`),
each with the value of the data table `valuesData` when it has one and the control table's
otherwise (`valueOfD`). The machines have the same states, invariant and successors; only the
facts differ, and `codeD`'s facts contain `code`'s (`factsD_mono`), so every shape obligation of
`code` is one of `codeD` (`shapeAtD`).

The data table states the score pairs of the current round from their packing to the bias
products (first and biased rounds) or the exponents (plain rounds), and the 32 registers of a
plain round's score load at its implicit wait, as the code computes them from the reals the score
loads returned (`V.sv`, rule M2): pair `j` of a round holds the elements `2j` and `2j + 1`
(`pairReg`), element `n` is element `n mod 32` of load `n / 32` (`V.score`). It also states the
row maximum and row sum before the round (`V.mf`, `V.mr`, `V.rs`; the maximum may be `-∞`) from
a bias round's and a plain round's start to the final stores, and a plain round's maximum,
subtracted maximum and rescaling factor after its fourth load (`maxP`, `facP`). The first round's
and a bias round's maximum (after the bias products, the register `%r6196` is stated from pc 6661
on only, `liveF`), the probabilities and their packs are not named yet (`DECISIONS.md`); the bias
halves are named from their unpacks to the bias products (`valuesHalves`), the negated exponent
scale `%r170` from the first round's P part on (`negS`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (r32 i32 add32 addi sub32 min32 shl andi)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The row maximum before the round (`%r6191` in a bias round, `%r6195` in a plain round), the
row sum (`%r6197`) and the negated scale. -/
def valuesRun (p : Params) (v : V) : List (Nat × Value) :=
  [(7251, mxVal v), (7255, mxVal v), (7257, .float .f32 v.rs), (1230, negS p)]

/-- A plain round after its maximum (`maxP`, `facP` and `mxVal` written out per kind of the
maximum before the round, so that the segment tactics see one form): the maximum, the maximum
its exponents subtract, the rescaling factor, the row sum, and the fold and the maximum before
the round (no longer live at the round's states; listed so that the walk cut after the fold
states them from this table). -/
def valuesPlainP (p : Params) (v : V) : List (Nat × Value) :=
  match v.mf with
  | true =>
    [(7256, if keepP p v = true then .float .f32 v.mr else .float .f32 (foldPT v.mr v.score)),
     (5514, if keepP p v = true then .float .f32 v.mr else .float .f32 (foldPT v.mr v.score)),
     (1492, if keepP p v = true then .bits 32 (BitVec.ofNat 64 1065353216)
       else .float .f32 (Real.rpow 2 ((scl p : ℝ) * (v.mr + -foldPT v.mr v.score)))),
     (7257, .float .f32 v.rs), (7255, .float .f32 v.mr),
     (5509, .float .f32 (foldPT v.mr v.score)), (1230, negS p)]
  | false =>
    [(7256, .float .f32 (foldPF v.score)), (5514, .float .f32 (foldPF v.score)),
     (1492, .float .f32 0), (7257, .float .f32 v.rs),
     (7255, .bits 32 (BitVec.ofNat 64 4286578688)), (5509, .float .f32 (foldPF v.score)),
     (1230, negS p)]

/-- A recorded bias half as the code holds it: the `bf16` payload `r` when `b`, else the masked
pattern `0xFF80`. -/
abbrev hv16 (b : Bool) (r : ℝ) : Value :=
  if b = true then .float .bf16 r else .bits 16 (BitVec.ofNat 64 0xFF80)

/-- The halves of the round's bias loads (`b = false` the first round): half `i` of load `c` (the
low half of word `i / 2` when `i` is even) is register `base + 8 c + 7 - i` (`base` 786 or 914),
as the code's unpacks write them, with the value `hv16` written out and literal registers and
indices (the segment tactics split on a conditional they see, and a case split rewrites the facts
with `simp`, which would reduce arithmetic in them). -/
def halvesList (b : Bool) (v : V) : List (Nat × Value) :=
  match b with
  | false =>
    [(793, if v.bk 0 0 = true then .float .bf16 (v.br 0 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (792, if v.bk 0 1 = true then .float .bf16 (v.br 0 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (791, if v.bk 0 2 = true then .float .bf16 (v.br 0 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (790, if v.bk 0 3 = true then .float .bf16 (v.br 0 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (789, if v.bk 0 4 = true then .float .bf16 (v.br 0 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (788, if v.bk 0 5 = true then .float .bf16 (v.br 0 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (787, if v.bk 0 6 = true then .float .bf16 (v.br 0 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (786, if v.bk 0 7 = true then .float .bf16 (v.br 0 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (801, if v.bk 1 0 = true then .float .bf16 (v.br 1 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (800, if v.bk 1 1 = true then .float .bf16 (v.br 1 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (799, if v.bk 1 2 = true then .float .bf16 (v.br 1 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (798, if v.bk 1 3 = true then .float .bf16 (v.br 1 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (797, if v.bk 1 4 = true then .float .bf16 (v.br 1 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (796, if v.bk 1 5 = true then .float .bf16 (v.br 1 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (795, if v.bk 1 6 = true then .float .bf16 (v.br 1 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (794, if v.bk 1 7 = true then .float .bf16 (v.br 1 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (809, if v.bk 2 0 = true then .float .bf16 (v.br 2 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (808, if v.bk 2 1 = true then .float .bf16 (v.br 2 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (807, if v.bk 2 2 = true then .float .bf16 (v.br 2 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (806, if v.bk 2 3 = true then .float .bf16 (v.br 2 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (805, if v.bk 2 4 = true then .float .bf16 (v.br 2 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (804, if v.bk 2 5 = true then .float .bf16 (v.br 2 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (803, if v.bk 2 6 = true then .float .bf16 (v.br 2 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (802, if v.bk 2 7 = true then .float .bf16 (v.br 2 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (817, if v.bk 3 0 = true then .float .bf16 (v.br 3 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (816, if v.bk 3 1 = true then .float .bf16 (v.br 3 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (815, if v.bk 3 2 = true then .float .bf16 (v.br 3 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (814, if v.bk 3 3 = true then .float .bf16 (v.br 3 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (813, if v.bk 3 4 = true then .float .bf16 (v.br 3 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (812, if v.bk 3 5 = true then .float .bf16 (v.br 3 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (811, if v.bk 3 6 = true then .float .bf16 (v.br 3 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (810, if v.bk 3 7 = true then .float .bf16 (v.br 3 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (825, if v.bk 4 0 = true then .float .bf16 (v.br 4 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (824, if v.bk 4 1 = true then .float .bf16 (v.br 4 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (823, if v.bk 4 2 = true then .float .bf16 (v.br 4 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (822, if v.bk 4 3 = true then .float .bf16 (v.br 4 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (821, if v.bk 4 4 = true then .float .bf16 (v.br 4 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (820, if v.bk 4 5 = true then .float .bf16 (v.br 4 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (819, if v.bk 4 6 = true then .float .bf16 (v.br 4 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (818, if v.bk 4 7 = true then .float .bf16 (v.br 4 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (833, if v.bk 5 0 = true then .float .bf16 (v.br 5 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (832, if v.bk 5 1 = true then .float .bf16 (v.br 5 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (831, if v.bk 5 2 = true then .float .bf16 (v.br 5 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (830, if v.bk 5 3 = true then .float .bf16 (v.br 5 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (829, if v.bk 5 4 = true then .float .bf16 (v.br 5 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (828, if v.bk 5 5 = true then .float .bf16 (v.br 5 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (827, if v.bk 5 6 = true then .float .bf16 (v.br 5 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (826, if v.bk 5 7 = true then .float .bf16 (v.br 5 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (841, if v.bk 6 0 = true then .float .bf16 (v.br 6 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (840, if v.bk 6 1 = true then .float .bf16 (v.br 6 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (839, if v.bk 6 2 = true then .float .bf16 (v.br 6 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (838, if v.bk 6 3 = true then .float .bf16 (v.br 6 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (837, if v.bk 6 4 = true then .float .bf16 (v.br 6 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (836, if v.bk 6 5 = true then .float .bf16 (v.br 6 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (835, if v.bk 6 6 = true then .float .bf16 (v.br 6 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (834, if v.bk 6 7 = true then .float .bf16 (v.br 6 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (849, if v.bk 7 0 = true then .float .bf16 (v.br 7 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (848, if v.bk 7 1 = true then .float .bf16 (v.br 7 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (847, if v.bk 7 2 = true then .float .bf16 (v.br 7 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (846, if v.bk 7 3 = true then .float .bf16 (v.br 7 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (845, if v.bk 7 4 = true then .float .bf16 (v.br 7 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (844, if v.bk 7 5 = true then .float .bf16 (v.br 7 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (843, if v.bk 7 6 = true then .float .bf16 (v.br 7 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (842, if v.bk 7 7 = true then .float .bf16 (v.br 7 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (857, if v.bk 8 0 = true then .float .bf16 (v.br 8 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (856, if v.bk 8 1 = true then .float .bf16 (v.br 8 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (855, if v.bk 8 2 = true then .float .bf16 (v.br 8 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (854, if v.bk 8 3 = true then .float .bf16 (v.br 8 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (853, if v.bk 8 4 = true then .float .bf16 (v.br 8 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (852, if v.bk 8 5 = true then .float .bf16 (v.br 8 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (851, if v.bk 8 6 = true then .float .bf16 (v.br 8 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (850, if v.bk 8 7 = true then .float .bf16 (v.br 8 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (865, if v.bk 9 0 = true then .float .bf16 (v.br 9 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (864, if v.bk 9 1 = true then .float .bf16 (v.br 9 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (863, if v.bk 9 2 = true then .float .bf16 (v.br 9 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (862, if v.bk 9 3 = true then .float .bf16 (v.br 9 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (861, if v.bk 9 4 = true then .float .bf16 (v.br 9 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (860, if v.bk 9 5 = true then .float .bf16 (v.br 9 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (859, if v.bk 9 6 = true then .float .bf16 (v.br 9 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (858, if v.bk 9 7 = true then .float .bf16 (v.br 9 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (873, if v.bk 10 0 = true then .float .bf16 (v.br 10 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (872, if v.bk 10 1 = true then .float .bf16 (v.br 10 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (871, if v.bk 10 2 = true then .float .bf16 (v.br 10 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (870, if v.bk 10 3 = true then .float .bf16 (v.br 10 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (869, if v.bk 10 4 = true then .float .bf16 (v.br 10 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (868, if v.bk 10 5 = true then .float .bf16 (v.br 10 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (867, if v.bk 10 6 = true then .float .bf16 (v.br 10 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (866, if v.bk 10 7 = true then .float .bf16 (v.br 10 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (881, if v.bk 11 0 = true then .float .bf16 (v.br 11 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (880, if v.bk 11 1 = true then .float .bf16 (v.br 11 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (879, if v.bk 11 2 = true then .float .bf16 (v.br 11 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (878, if v.bk 11 3 = true then .float .bf16 (v.br 11 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (877, if v.bk 11 4 = true then .float .bf16 (v.br 11 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (876, if v.bk 11 5 = true then .float .bf16 (v.br 11 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (875, if v.bk 11 6 = true then .float .bf16 (v.br 11 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (874, if v.bk 11 7 = true then .float .bf16 (v.br 11 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (889, if v.bk 12 0 = true then .float .bf16 (v.br 12 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (888, if v.bk 12 1 = true then .float .bf16 (v.br 12 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (887, if v.bk 12 2 = true then .float .bf16 (v.br 12 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (886, if v.bk 12 3 = true then .float .bf16 (v.br 12 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (885, if v.bk 12 4 = true then .float .bf16 (v.br 12 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (884, if v.bk 12 5 = true then .float .bf16 (v.br 12 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (883, if v.bk 12 6 = true then .float .bf16 (v.br 12 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (882, if v.bk 12 7 = true then .float .bf16 (v.br 12 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (897, if v.bk 13 0 = true then .float .bf16 (v.br 13 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (896, if v.bk 13 1 = true then .float .bf16 (v.br 13 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (895, if v.bk 13 2 = true then .float .bf16 (v.br 13 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (894, if v.bk 13 3 = true then .float .bf16 (v.br 13 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (893, if v.bk 13 4 = true then .float .bf16 (v.br 13 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (892, if v.bk 13 5 = true then .float .bf16 (v.br 13 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (891, if v.bk 13 6 = true then .float .bf16 (v.br 13 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (890, if v.bk 13 7 = true then .float .bf16 (v.br 13 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (905, if v.bk 14 0 = true then .float .bf16 (v.br 14 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (904, if v.bk 14 1 = true then .float .bf16 (v.br 14 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (903, if v.bk 14 2 = true then .float .bf16 (v.br 14 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (902, if v.bk 14 3 = true then .float .bf16 (v.br 14 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (901, if v.bk 14 4 = true then .float .bf16 (v.br 14 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (900, if v.bk 14 5 = true then .float .bf16 (v.br 14 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (899, if v.bk 14 6 = true then .float .bf16 (v.br 14 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (898, if v.bk 14 7 = true then .float .bf16 (v.br 14 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (913, if v.bk 15 0 = true then .float .bf16 (v.br 15 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (912, if v.bk 15 1 = true then .float .bf16 (v.br 15 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (911, if v.bk 15 2 = true then .float .bf16 (v.br 15 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (910, if v.bk 15 3 = true then .float .bf16 (v.br 15 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (909, if v.bk 15 4 = true then .float .bf16 (v.br 15 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (908, if v.bk 15 5 = true then .float .bf16 (v.br 15 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (907, if v.bk 15 6 = true then .float .bf16 (v.br 15 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (906, if v.bk 15 7 = true then .float .bf16 (v.br 15 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80))]
  | true =>
    [(921, if v.bk 0 0 = true then .float .bf16 (v.br 0 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (920, if v.bk 0 1 = true then .float .bf16 (v.br 0 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (919, if v.bk 0 2 = true then .float .bf16 (v.br 0 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (918, if v.bk 0 3 = true then .float .bf16 (v.br 0 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (917, if v.bk 0 4 = true then .float .bf16 (v.br 0 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (916, if v.bk 0 5 = true then .float .bf16 (v.br 0 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (915, if v.bk 0 6 = true then .float .bf16 (v.br 0 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (914, if v.bk 0 7 = true then .float .bf16 (v.br 0 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (929, if v.bk 1 0 = true then .float .bf16 (v.br 1 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (928, if v.bk 1 1 = true then .float .bf16 (v.br 1 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (927, if v.bk 1 2 = true then .float .bf16 (v.br 1 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (926, if v.bk 1 3 = true then .float .bf16 (v.br 1 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (925, if v.bk 1 4 = true then .float .bf16 (v.br 1 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (924, if v.bk 1 5 = true then .float .bf16 (v.br 1 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (923, if v.bk 1 6 = true then .float .bf16 (v.br 1 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (922, if v.bk 1 7 = true then .float .bf16 (v.br 1 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (937, if v.bk 2 0 = true then .float .bf16 (v.br 2 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (936, if v.bk 2 1 = true then .float .bf16 (v.br 2 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (935, if v.bk 2 2 = true then .float .bf16 (v.br 2 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (934, if v.bk 2 3 = true then .float .bf16 (v.br 2 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (933, if v.bk 2 4 = true then .float .bf16 (v.br 2 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (932, if v.bk 2 5 = true then .float .bf16 (v.br 2 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (931, if v.bk 2 6 = true then .float .bf16 (v.br 2 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (930, if v.bk 2 7 = true then .float .bf16 (v.br 2 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (945, if v.bk 3 0 = true then .float .bf16 (v.br 3 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (944, if v.bk 3 1 = true then .float .bf16 (v.br 3 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (943, if v.bk 3 2 = true then .float .bf16 (v.br 3 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (942, if v.bk 3 3 = true then .float .bf16 (v.br 3 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (941, if v.bk 3 4 = true then .float .bf16 (v.br 3 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (940, if v.bk 3 5 = true then .float .bf16 (v.br 3 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (939, if v.bk 3 6 = true then .float .bf16 (v.br 3 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (938, if v.bk 3 7 = true then .float .bf16 (v.br 3 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (953, if v.bk 4 0 = true then .float .bf16 (v.br 4 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (952, if v.bk 4 1 = true then .float .bf16 (v.br 4 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (951, if v.bk 4 2 = true then .float .bf16 (v.br 4 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (950, if v.bk 4 3 = true then .float .bf16 (v.br 4 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (949, if v.bk 4 4 = true then .float .bf16 (v.br 4 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (948, if v.bk 4 5 = true then .float .bf16 (v.br 4 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (947, if v.bk 4 6 = true then .float .bf16 (v.br 4 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (946, if v.bk 4 7 = true then .float .bf16 (v.br 4 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (961, if v.bk 5 0 = true then .float .bf16 (v.br 5 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (960, if v.bk 5 1 = true then .float .bf16 (v.br 5 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (959, if v.bk 5 2 = true then .float .bf16 (v.br 5 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (958, if v.bk 5 3 = true then .float .bf16 (v.br 5 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (957, if v.bk 5 4 = true then .float .bf16 (v.br 5 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (956, if v.bk 5 5 = true then .float .bf16 (v.br 5 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (955, if v.bk 5 6 = true then .float .bf16 (v.br 5 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (954, if v.bk 5 7 = true then .float .bf16 (v.br 5 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (969, if v.bk 6 0 = true then .float .bf16 (v.br 6 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (968, if v.bk 6 1 = true then .float .bf16 (v.br 6 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (967, if v.bk 6 2 = true then .float .bf16 (v.br 6 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (966, if v.bk 6 3 = true then .float .bf16 (v.br 6 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (965, if v.bk 6 4 = true then .float .bf16 (v.br 6 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (964, if v.bk 6 5 = true then .float .bf16 (v.br 6 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (963, if v.bk 6 6 = true then .float .bf16 (v.br 6 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (962, if v.bk 6 7 = true then .float .bf16 (v.br 6 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (977, if v.bk 7 0 = true then .float .bf16 (v.br 7 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (976, if v.bk 7 1 = true then .float .bf16 (v.br 7 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (975, if v.bk 7 2 = true then .float .bf16 (v.br 7 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (974, if v.bk 7 3 = true then .float .bf16 (v.br 7 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (973, if v.bk 7 4 = true then .float .bf16 (v.br 7 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (972, if v.bk 7 5 = true then .float .bf16 (v.br 7 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (971, if v.bk 7 6 = true then .float .bf16 (v.br 7 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (970, if v.bk 7 7 = true then .float .bf16 (v.br 7 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (985, if v.bk 8 0 = true then .float .bf16 (v.br 8 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (984, if v.bk 8 1 = true then .float .bf16 (v.br 8 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (983, if v.bk 8 2 = true then .float .bf16 (v.br 8 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (982, if v.bk 8 3 = true then .float .bf16 (v.br 8 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (981, if v.bk 8 4 = true then .float .bf16 (v.br 8 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (980, if v.bk 8 5 = true then .float .bf16 (v.br 8 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (979, if v.bk 8 6 = true then .float .bf16 (v.br 8 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (978, if v.bk 8 7 = true then .float .bf16 (v.br 8 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (993, if v.bk 9 0 = true then .float .bf16 (v.br 9 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (992, if v.bk 9 1 = true then .float .bf16 (v.br 9 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (991, if v.bk 9 2 = true then .float .bf16 (v.br 9 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (990, if v.bk 9 3 = true then .float .bf16 (v.br 9 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (989, if v.bk 9 4 = true then .float .bf16 (v.br 9 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (988, if v.bk 9 5 = true then .float .bf16 (v.br 9 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (987, if v.bk 9 6 = true then .float .bf16 (v.br 9 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (986, if v.bk 9 7 = true then .float .bf16 (v.br 9 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1001, if v.bk 10 0 = true then .float .bf16 (v.br 10 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1000, if v.bk 10 1 = true then .float .bf16 (v.br 10 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (999, if v.bk 10 2 = true then .float .bf16 (v.br 10 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (998, if v.bk 10 3 = true then .float .bf16 (v.br 10 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (997, if v.bk 10 4 = true then .float .bf16 (v.br 10 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (996, if v.bk 10 5 = true then .float .bf16 (v.br 10 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (995, if v.bk 10 6 = true then .float .bf16 (v.br 10 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (994, if v.bk 10 7 = true then .float .bf16 (v.br 10 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1009, if v.bk 11 0 = true then .float .bf16 (v.br 11 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1008, if v.bk 11 1 = true then .float .bf16 (v.br 11 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1007, if v.bk 11 2 = true then .float .bf16 (v.br 11 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1006, if v.bk 11 3 = true then .float .bf16 (v.br 11 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1005, if v.bk 11 4 = true then .float .bf16 (v.br 11 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1004, if v.bk 11 5 = true then .float .bf16 (v.br 11 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1003, if v.bk 11 6 = true then .float .bf16 (v.br 11 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1002, if v.bk 11 7 = true then .float .bf16 (v.br 11 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1017, if v.bk 12 0 = true then .float .bf16 (v.br 12 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1016, if v.bk 12 1 = true then .float .bf16 (v.br 12 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1015, if v.bk 12 2 = true then .float .bf16 (v.br 12 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1014, if v.bk 12 3 = true then .float .bf16 (v.br 12 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1013, if v.bk 12 4 = true then .float .bf16 (v.br 12 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1012, if v.bk 12 5 = true then .float .bf16 (v.br 12 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1011, if v.bk 12 6 = true then .float .bf16 (v.br 12 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1010, if v.bk 12 7 = true then .float .bf16 (v.br 12 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1025, if v.bk 13 0 = true then .float .bf16 (v.br 13 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1024, if v.bk 13 1 = true then .float .bf16 (v.br 13 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1023, if v.bk 13 2 = true then .float .bf16 (v.br 13 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1022, if v.bk 13 3 = true then .float .bf16 (v.br 13 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1021, if v.bk 13 4 = true then .float .bf16 (v.br 13 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1020, if v.bk 13 5 = true then .float .bf16 (v.br 13 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1019, if v.bk 13 6 = true then .float .bf16 (v.br 13 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1018, if v.bk 13 7 = true then .float .bf16 (v.br 13 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1033, if v.bk 14 0 = true then .float .bf16 (v.br 14 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1032, if v.bk 14 1 = true then .float .bf16 (v.br 14 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1031, if v.bk 14 2 = true then .float .bf16 (v.br 14 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1030, if v.bk 14 3 = true then .float .bf16 (v.br 14 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1029, if v.bk 14 4 = true then .float .bf16 (v.br 14 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1028, if v.bk 14 5 = true then .float .bf16 (v.br 14 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1027, if v.bk 14 6 = true then .float .bf16 (v.br 14 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1026, if v.bk 14 7 = true then .float .bf16 (v.br 14 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1041, if v.bk 15 0 = true then .float .bf16 (v.br 15 0)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1040, if v.bk 15 1 = true then .float .bf16 (v.br 15 1)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1039, if v.bk 15 2 = true then .float .bf16 (v.br 15 2)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1038, if v.bk 15 3 = true then .float .bf16 (v.br 15 3)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1037, if v.bk 15 4 = true then .float .bf16 (v.br 15 4)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1036, if v.bk 15 5 = true then .float .bf16 (v.br 15 5)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1035, if v.bk 15 6 = true then .float .bf16 (v.br 15 6)
      else .bits 16 (BitVec.ofNat 64 0xFF80)),
    (1034, if v.bk 15 7 = true then .float .bf16 (v.br 15 7)
      else .bits 16 (BitVec.ofNat 64 0xFF80))]

/-- The halves of the round's first `n` bias loads. -/
def valuesHalves (b : Bool) (v : V) (n : Nat) : List (Nat × Value) :=
  (halvesList b v).take (8 * n)

/-- A plain round's 128 weights at its P part's states, in the order of the code's row sum
(column `i` is the `i`-th of these registers; the software `exp2` results are registers
5128 + 3 k). -/
def valuesProbP (p : Params) (v : V) : List (Nat × Value) :=
  [(1493, .float .f32 (probR p v 0)),
   (1494, .float .f32 (probR p v 1)),
   (1495, .float .f32 (probR p v 2)),
   (1496, .float .f32 (probR p v 3)),
   (1497, .float .f32 (probR p v 4)),
   (1498, .float .f32 (probR p v 5)),
   (1499, .float .f32 (probR p v 6)),
   (1500, .float .f32 (probR p v 7)),
   (1501, .float .f32 (probR p v 8)),
   (1502, .float .f32 (probR p v 9)),
   (1503, .float .f32 (probR p v 10)),
   (1504, .float .f32 (probR p v 11)),
   (1505, .float .f32 (probR p v 12)),
   (1506, .float .f32 (probR p v 13)),
   (1507, .float .f32 (probR p v 14)),
   (1508, .float .f32 (probR p v 15)),
   (1509, .float .f32 (probR p v 16)),
   (1510, .float .f32 (probR p v 17)),
   (1511, .float .f32 (probR p v 18)),
   (1512, .float .f32 (probR p v 19)),
   (1513, .float .f32 (probR p v 20)),
   (1514, .float .f32 (probR p v 21)),
   (1515, .float .f32 (probR p v 22)),
   (1516, .float .f32 (probR p v 23)),
   (1517, .float .f32 (probR p v 24)),
   (1518, .float .f32 (probR p v 25)),
   (1519, .float .f32 (probR p v 26)),
   (1520, .float .f32 (probR p v 27)),
   (1521, .float .f32 (probR p v 28)),
   (1522, .float .f32 (probR p v 29)),
   (1523, .float .f32 (probR p v 30)),
   (1524, .float .f32 (probR p v 31)),
   (1525, .float .f32 (probR p v 32)),
   (1526, .float .f32 (probR p v 33)),
   (1527, .float .f32 (probR p v 34)),
   (1528, .float .f32 (probR p v 35)),
   (1529, .float .f32 (probR p v 36)),
   (1530, .float .f32 (probR p v 37)),
   (1531, .float .f32 (probR p v 38)),
   (1532, .float .f32 (probR p v 39)),
   (1533, .float .f32 (probR p v 40)),
   (1534, .float .f32 (probR p v 41)),
   (1535, .float .f32 (probR p v 42)),
   (1536, .float .f32 (probR p v 43)),
   (5128, .float .f32 (probR p v 44)),
   (5131, .float .f32 (probR p v 45)),
   (5134, .float .f32 (probR p v 46)),
   (5137, .float .f32 (probR p v 47)),
   (1537, .float .f32 (probR p v 48)),
   (1538, .float .f32 (probR p v 49)),
   (1539, .float .f32 (probR p v 50)),
   (1540, .float .f32 (probR p v 51)),
   (1541, .float .f32 (probR p v 52)),
   (1542, .float .f32 (probR p v 53)),
   (1543, .float .f32 (probR p v 54)),
   (1544, .float .f32 (probR p v 55)),
   (1545, .float .f32 (probR p v 56)),
   (1546, .float .f32 (probR p v 57)),
   (1547, .float .f32 (probR p v 58)),
   (1548, .float .f32 (probR p v 59)),
   (5140, .float .f32 (probR p v 60)),
   (5143, .float .f32 (probR p v 61)),
   (5146, .float .f32 (probR p v 62)),
   (5149, .float .f32 (probR p v 63)),
   (1549, .float .f32 (probR p v 64)),
   (1550, .float .f32 (probR p v 65)),
   (1551, .float .f32 (probR p v 66)),
   (1552, .float .f32 (probR p v 67)),
   (1553, .float .f32 (probR p v 68)),
   (1554, .float .f32 (probR p v 69)),
   (1555, .float .f32 (probR p v 70)),
   (1556, .float .f32 (probR p v 71)),
   (1557, .float .f32 (probR p v 72)),
   (1558, .float .f32 (probR p v 73)),
   (1559, .float .f32 (probR p v 74)),
   (1560, .float .f32 (probR p v 75)),
   (5152, .float .f32 (probR p v 76)),
   (5155, .float .f32 (probR p v 77)),
   (5158, .float .f32 (probR p v 78)),
   (5161, .float .f32 (probR p v 79)),
   (1561, .float .f32 (probR p v 80)),
   (1562, .float .f32 (probR p v 81)),
   (1563, .float .f32 (probR p v 82)),
   (1564, .float .f32 (probR p v 83)),
   (1565, .float .f32 (probR p v 84)),
   (1566, .float .f32 (probR p v 85)),
   (1567, .float .f32 (probR p v 86)),
   (1568, .float .f32 (probR p v 87)),
   (1569, .float .f32 (probR p v 88)),
   (1570, .float .f32 (probR p v 89)),
   (1571, .float .f32 (probR p v 90)),
   (1572, .float .f32 (probR p v 91)),
   (5164, .float .f32 (probR p v 92)),
   (5167, .float .f32 (probR p v 93)),
   (5170, .float .f32 (probR p v 94)),
   (5173, .float .f32 (probR p v 95)),
   (1573, .float .f32 (probR p v 96)),
   (1574, .float .f32 (probR p v 97)),
   (1575, .float .f32 (probR p v 98)),
   (1576, .float .f32 (probR p v 99)),
   (1577, .float .f32 (probR p v 100)),
   (1578, .float .f32 (probR p v 101)),
   (1579, .float .f32 (probR p v 102)),
   (1580, .float .f32 (probR p v 103)),
   (1581, .float .f32 (probR p v 104)),
   (1582, .float .f32 (probR p v 105)),
   (1583, .float .f32 (probR p v 106)),
   (1584, .float .f32 (probR p v 107)),
   (1585, .float .f32 (probR p v 108)),
   (1586, .float .f32 (probR p v 109)),
   (1587, .float .f32 (probR p v 110)),
   (1588, .float .f32 (probR p v 111)),
   (1589, .float .f32 (probR p v 112)),
   (1590, .float .f32 (probR p v 113)),
   (1591, .float .f32 (probR p v 114)),
   (1592, .float .f32 (probR p v 115)),
   (1593, .float .f32 (probR p v 116)),
   (1594, .float .f32 (probR p v 117)),
   (1595, .float .f32 (probR p v 118)),
   (1596, .float .f32 (probR p v 119)),
   (1597, .float .f32 (probR p v 120)),
   (1598, .float .f32 (probR p v 121)),
   (1599, .float .f32 (probR p v 122)),
   (1600, .float .f32 (probR p v 123)),
   (1601, .float .f32 (probR p v 124)),
   (1602, .float .f32 (probR p v 125)),
   (1603, .float .f32 (probR p v 126)),
   (1604, .float .f32 (probR p v 127))]

/-! ### A bias round after its maximum -/

/-- The readings of a bias round's 128 products (a real, or `-∞` for a masked bias half). -/
abbrev bpeB (p : Params) (v : V) : Nat → EReal := bpe (bpf v) (bps p v)

/-- The row maximum before the round as an extended real. -/
abbrev mxE (v : V) : EReal := if v.mf = true then (v.mr : EReal) else ⊥

/-- A bias round's maximum before its keep test (`%r3500`, `foldB`). -/
abbrev foldBE (p : Params) (v : V) : EReal := foldB (mxE v) (bpeB p v)

/-- The fold as a number (it is one when the maximum before the round is finite). -/
abbrev foldBR (p : Params) (v : V) : ℝ := (foldBE p v).toReal

/-- Whether a bias round keeps the row maximum before it (`setp.ge.f32` at pc 5671), when that
maximum is finite; stated in the walk's form, as `keepP`. -/
def keepB (p : Params) (v : V) : Bool :=
  Assumption.erealCompare .ge
    (((scl p : ℝ) * (v.mr + -foldBR p v) : ℝ) : EReal) ((-(8 : ℝ) : ℝ) : EReal)

/-- A bias round's products (pcs 5279 to 5534): the scaled bias plus the score, `-∞` for a
masked half. -/
def valuesProdB (p : Params) (v : V) : List (Nat × Value) :=
  (List.range 64).map fun j =>
    (8317 + 2 * j, .pair (bv32 (bpf v) (bps p v) (2 * j)) (bv32 (bpf v) (bps p v) (2 * j + 1)))

/-- A bias round after its maximum (pcs 5666 to 5674): the row maximum (`%r6196`), the maximum
the exponents subtract (`%r3505`) and the row sum's rescaling factor (`%r302`), each per kind of
the maximum before the round (`bif v.mf`, so that the list's spine is literal and a walk that
carries the entries reads them for any `v`). -/
def valuesBiasM (p : Params) (v : V) : List (Nat × Value) :=
  [(7256, bif v.mf then (if keepB p v = true then .float .f32 v.mr else .float .f32 (foldBR p v))
     else Assumption.erealValue .f32 (foldBE p v)),
   (4565, bif v.mf then (if keepB p v = true then .float .f32 v.mr else .float .f32 (foldBR p v))
     else (if foldBE p v = ⊥ then .bits 32 (BitVec.ofNat 64 0)
       else Assumption.erealValue .f32 (foldBE p v))),
   (1362, bif v.mf then (if keepB p v = true then .bits 32 (BitVec.ofNat 64 1065353216)
       else .float .f32 (Real.rpow 2 ((scl p : ℝ) * (v.mr + -foldBR p v))))
     else .float .f32 0)]

/-! ### The first round's P part -/

/-- The data table outside the P parts whose values are the generated runs' terms (matched on the
state, so that a table entry names the state's values, not a projection of it). -/
def valuesData0 (p : Params) (L : Launch) (g : Nat) : D → List (Nat × Value)
  | ⟨s, v, _, _⟩ =>
  match s with
  | .narr .first => valuesNarr1 p L g v
  | .sld r c => valuesPairs r v (16 * c.val) ++ valuesRun p v
  | .wb b => valuesPairs (rdOf b) v 64 ++ valuesRun p v
  | .bld b c => valuesPairs (rdOf b) v 64 ++ valuesRun p v ++ valuesHalves b v c.val
  | .fence b | .bsync b | .barr b =>
    valuesPairs (rdOf b) v 64 ++ valuesRun p v ++ valuesHalves b v 16
  | .sldw c => valuesLoaded v c ++ valuesPairs .plain v (16 * c.val) ++ valuesRun p v
  | .stat true | .narr .plain => valuesPairs .plain v 64 ++ valuesPlainP p v
  | .pst .plain _ | .pwst .plain _ | .parr .plain | .pws .plain | .pel .plain | .parr2 .plain
  | .pwend .plain => valuesPlainP p v ++ valuesProbP p v
  | .ws _ => valuesRun p v
  | .stat false | .narr .bias => valuesRun p v ++ valuesBiasM p v ++ valuesProdB p v
  | .pst .bias _ | .pwst .bias _ | .parr .bias | .pws .bias | .pel .bias | .parr2 .bias
  | .pwend .bias => valuesRun p v ++ valuesBiasM p v
  | .fin _ | .finarr => [(7256, mxVal v), (7257, .float .f32 v.rs)]
  | _ => []


/-- The value of register `r` at state `d` outside the generated P parts. -/
def valueOfD0 (p : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((valuesData0 p L g d).lookup r).getD (valueOf p L g d r)

/-- The unpacks before the second to fourth P stores of the first round (pcs 4827 to 4834, 4836
to 4843, 4848 to 4855): low half, high half, the packed word. -/
def unpackSpec1 : List (Nat × Nat × Nat) :=
  [(3895, 3896, 8169), (3897, 3898, 8168), (3899, 3900, 8167), (3901, 3902, 8166),
   (3903, 3904, 8165), (3905, 3906, 8164), (3907, 3908, 8163), (3909, 3910, 8162),
   (3911, 3912, 8177), (3913, 3914, 8176), (3915, 3916, 8175), (3917, 3918, 8174),
   (3919, 3920, 8173), (3921, 3922, 8172), (3923, 3924, 8171), (3925, 3926, 8170),
   (3928, 3929, 8185), (3930, 3931, 8184), (3932, 3933, 8183), (3934, 3935, 8182),
   (3936, 3937, 8181), (3938, 3939, 8180), (3940, 3941, 8179), (3942, 3943, 8178)]

/-- The halves those unpacks write, as the splits of the packed words' terms. -/
def halvesP1 (E : List (Nat × Value)) : List (Nat × Value) :=
  unpackSpec1.flatMap fun (lo, hi, w) =>
    [(lo, (splitValue 64 (lookupD E w)).1), (hi, (splitValue 64 (lookupD E w)).2)]

/-- The first round's P part's data: the exponent stretch's terms and the store halves. -/
def p1Data (p : Params) (L : Launch) (g : Nat) (v : V) : List (Nat × Value) :=
  expoE p L g v ++ halvesP1 (expoE p L g v)

/-- **The data table**: the named data registers at state `d` (matched on the state). -/
def valuesData (p : Params) (L : Launch) (g : Nat) : D → List (Nat × Value)
  | ⟨s, v, k, acc⟩ =>
  match s with
  | .pst .first _ | .pwst .first _ | .parr .first | .pws .first | .pel .first | .parr2 .first
  | .pwend .first => p1Data p L g v
  | .pst .plain _ | .pwst .plain _ | .parr .plain | .pws .plain | .pel .plain | .parr2 .plain
  | .pwend .plain => pPData p v
  | _ => valuesData0 p L g ⟨s, v, k, acc⟩

/-- The registers a bias round names from its statistics store to its last P store
(`liveF`). -/
def biasNamed (r : Nat) : Bool :=
  (Nat.ble 8317 r && Nat.ble r 8443) || r == 1362 || r == 4565 || r == 7256

/-- The data registers the table names: the score pairs of the three round kinds and the
destinations of the score loads (live only from a load to its packs). -/
def dnamed0 (r : Nat) : Bool :=
  (Nat.ble 7303 r && Nat.ble r 7490) || (Nat.ble 8687 r && Nat.ble r 8690) ||
    (Nat.ble 5188 r && Nat.ble r 5315) || (Nat.ble 2881 r && Nat.ble r 2912) ||
    (Nat.ble 2914 r && Nat.ble r 2977) || (Nat.ble 2979 r && Nat.ble r 3010) ||
    (Nat.ble 4038 r && Nat.ble r 4165) || r == 7251 || (Nat.ble 7255 r && Nat.ble r 7257) ||
    r == 1230 || r == 1492 || r == 5509 || r == 5514 || (Nat.ble 786 r && Nat.ble r 1041) ||
    (Nat.ble 1493 r && Nat.ble r 1604) ||
    (Nat.ble 5128 r && Nat.ble r 5173 && (r - 5128) % 3 == 0) ||
    (Nat.ble 1231 r && Nat.ble r 1358) || (Nat.ble 3879 r && Nat.ble r 3926) ||
    (Nat.ble 3928 r && Nat.ble r 3943) || (Nat.ble 8162 r && Nat.ble r 8185) ||
    (Nat.ble 3240 r && Nat.ble r 3685 && (r == 3685 || elemRegs.contains r))

/-- The registers a plain round's P part names (`pPData`): the exponent stretch's terms and the
store halves. -/
def plainNamed (r : Nat) : Bool :=
  ((Gen.expoP4_facts3 fun _ => .pred false).map Prod.fst).contains r ||
    (Nat.ble 5749 r && Nat.ble r 5797 && r != 5781)

/-- The data registers the table names, with a bias round's from its statistics store on. -/
def dnamed (r : Nat) : Bool := dnamed0 r || biasNamed r || plainNamed r

/-- The program counters of the role's states: its event instructions and the instruction after
a plain round's score load (the implicit wait's facts, `livePc`). -/
def statePcs : List Nat :=
  [3102, 3103, 3110, 3111, 3130, 3134, 3138, 3142, 3146, 3150, 3169, 3171, 3192, 3195, 3198,
   3201, 3204, 3207, 3220, 3227, 3231, 3369, 3370, 3373, 3420, 3425, 3428, 3446, 3463, 3481,
   3498, 3501, 3506, 3511, 3516, 3521, 3526, 3531, 3536, 3541, 3546, 3551, 3556, 3561, 3566,
   3571, 3576, 3581, 3583, 3590, 4397, 4826, 4835, 4844, 4845, 4847, 4856, 4857, 4858, 4859,
   4867, 4874, 5109, 5112, 5129, 5146, 5163, 5181, 5189, 5194, 5199, 5204, 5209, 5214, 5219,
   5224, 5229, 5234, 5239, 5244, 5249, 5254, 5259, 5264, 5269, 5271, 5278, 5682, 5683, 6508,
   6517, 6526, 6527, 6532, 6541, 6542, 6543, 6544, 6552, 6558, 6676, 6679, 6680, 6696, 6697,
   6713, 6714, 6730, 6731, 6890, 6891, 7416, 7425, 7434, 7435, 7437, 7446, 7447, 7448, 7449,
   7457, 7463, 7614, 7615, 7616, 7621, 7622, 7642, 7645, 7648, 7651, 7654, 7657, 7677, 7679,
   7700, 7703, 7706, 7709, 7712, 7715, 7726, 7731, 7732, 7738, 7741, 7746, 9205]

/-- The program counters where a numeric walk is cut (the end of a plain round's fold). -/
def cutPcs : List Nat := [6877]

/-- The registers a walk's checkpoint states: at a cut, the live control registers and the live
named data registers (the facts of a table at the cut); elsewhere every live register. -/
noncomputable def liveCut (pc : Nat) : List Nat :=
  if cutPcs.contains pc then
    (PTX.Kernels.TmlFa4Fwd.Flow.live pc).filter fun r => ctl r || dnamed r
  else PTX.Kernels.TmlFa4Fwd.Flow.live pc

/-- The registers a state's table states at `pc`: the live control registers and the live named
data registers. -/
noncomputable def liveF (pc : Nat) : List Nat :=
  (PTX.Kernels.TmlFa4Fwd.Flow.live pc).filter fun r =>
    ctl r || (dnamed r && (r != 7256 || Nat.ble 6661 pc || (Nat.ble 4397 pc && Nat.ble pc 4874))) ||
      (biasNamed r && Nat.ble 5682 pc && Nat.ble pc 6558)

/-- The registers whose facts a state of `codeD` states: at a state's program counter those of
its table (`liveF`); elsewhere (inside a walk between states, whose live function is this one)
every live register, so that a walk keeps the data registers it computes. -/
noncomputable def liveD (pc : Nat) : List Nat :=
  if statePcs.contains pc then liveF pc else PTX.Kernels.TmlFa4Fwd.Flow.live pc

/-- The value of register `r` at state `d`: the data table's, else the control table's. -/
def valueOfD (p : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((valuesData p L g d).lookup r).getD (valueOf p L g d r)

abbrev factsD (p : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (liveD (livePc d)) (valueOfD p L g d)

/-- **The softmax machine with its data plane.** -/
@[reducible] def codeD (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := D.mk' .setmax {}
  pc := (·.site.pc)
  facts := factsD p L g
  sub := (·.k.val)
  acc := (·.acc)
  inv := fun d => (d.k = 0 ∧ d.acc = [] ∧ d.site.first = true) ∨ d.site.midOk d.k d.acc
  next := succ p L g

variable {p : Params} {L : Launch} {g : Nat}

/-- A named data register is a data register. -/
theorem ctl_of_dnamed0 {r : Nat} (h : dnamed0 r = true) : ctl r = false := by
  simp only [dnamed0, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq,
    List.contains_iff_mem] at h
  unfold ctl
  rw [Bool.not_eq_false', List.any_eq_true]
  have k : ∀ a b : Nat, (a, b) ∈ dataRanges → a ≤ r → r ≤ b →
      ∃ x ∈ dataRanges, (Nat.ble x.1 r && Nat.ble r x.2) = true :=
    fun a b hm h1 h2 => ⟨(a, b), hm, by simp only [Bool.and_eq_true, Nat.ble_eq]; omega⟩
  rcases h with ((((((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) |
    h) | h) | h) | h) | h) | h) | h) | h)
  · exact k 7303 7490 (by decide) (by omega) (by omega)
  · exact k 8605 8691 (by decide) (by omega) (by omega)
  · exact k 5188 5514 (by decide) (by omega) (by omega)
  · exact k 2881 2912 (by decide) (by omega) (by omega)
  · exact k 2914 2977 (by decide) (by omega) (by omega)
  · exact k 2979 3074 (by decide) (by omega) (by omega)
  · exact k 4038 4165 (by decide) (by omega) (by omega)
  · exact k 7251 7252 (by decide) (by omega) (by omega)
  · exact k 7255 7257 (by decide) (by omega) (by omega)
  · exact k 1230 1358 (by decide) (by omega) (by omega)
  · exact k 1492 1604 (by decide) (by omega) (by omega)
  · exact k 5188 5514 (by decide) (by omega) (by omega)
  · exact k 5188 5514 (by decide) (by omega) (by omega)
  · exact k 786 1041 (by decide) (by omega) (by omega)
  · exact k 1492 1604 (by decide) (by omega) (by omega)
  · exact k 5128 5175 (by decide) (by omega) (by omega)
  · exact k 1230 1358 (by decide) (by omega) (by omega)
  · exact k 3616 3926 (by decide) (by omega) (by omega)
  · exact k 3928 3943 (by decide) (by omega) (by omega)
  · exact k 8027 8185 (by decide) (by omega) (by omega)
  · obtain ⟨⟨-, -⟩, h | h⟩ := h
    · subst h; exact k 3616 3926 (by decide) (by omega) (by omega)
    · have hc : ∀ x ∈ elemRegs, ctl x = false := by
        intro x hx; revert x; decide
      have := hc r (by simpa using h)
      simp only [ctl, Bool.not_eq_false', List.any_eq_true] at this
      exact this

theorem ctl_of_dnamed {r : Nat} (h : dnamed r = true) : ctl r = false := by
  simp only [dnamed, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact ctl_of_dnamed0 h
  rotate_left
  · have hk : ((Gen.expoP4_facts3 fun _ => .pred false).map Prod.fst ++
        (List.range' 5749 32 ++ List.range' 5782 16)).all (fun x => !ctl x) = true := by kernel_rfl
    have hm : r ∈ (Gen.expoP4_facts3 fun _ => .pred false).map Prod.fst ++
        (List.range' 5749 32 ++ List.range' 5782 16) := by
      simp only [plainNamed, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq,
        List.contains_iff_mem, bne_iff_ne, ne_eq] at h
      rcases h with h | ⟨⟨h1, h2⟩, h3⟩
      · exact List.mem_append_left _ h
      · refine List.mem_append_right _ ?_
        have : r - 5749 < 32 ∨ 33 ≤ r - 5749 := by omega
        rcases this with h4 | h4
        · exact List.mem_append_left _ (List.mem_range'.mpr ⟨r - 5749, h4, by omega⟩)
        · exact List.mem_append_right _ (List.mem_range'.mpr ⟨r - 5782, by omega, by omega⟩)
    simpa using List.all_eq_true.mp hk r hm
  simp only [biasNamed, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at h
  unfold ctl
  rw [Bool.not_eq_false', List.any_eq_true]
  have k : ∀ a b : Nat, (a, b) ∈ dataRanges → a ≤ r → r ≤ b →
      ∃ x ∈ dataRanges, (Nat.ble x.1 r && Nat.ble r x.2) = true :=
    fun a b hm h1 h2 => ⟨(a, b), hm, by simp only [Bool.and_eq_true, Nat.ble_eq]; omega⟩
  rcases h with ((h | h) | h) | h
  · exact k 8316 8444 (by decide) (by omega) (by omega)
  · exact k 1362 1490 (by decide) (by omega) (by omega)
  · exact k 4239 4565 (by decide) (by omega) (by omega)
  · exact k 7255 7257 (by decide) (by omega) (by omega)

theorem valuesPairs_keys (r : Rd) (v : V) (n : Nat) (hn : n ≤ 64) :
    ∀ q ∈ valuesPairs r v n, dnamed q.1 = true := by
  intro q hq
  simp only [valuesPairs, List.mem_map, List.mem_range] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  have : j < 64 := by omega
  cases r <;>
    simp only [pairReg, dnamed, dnamed0, biasNamed, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq]
  · omega
  · omega
  · split <;> omega

theorem valuesLoaded_keys (v : V) (c : Fin 4) : ∀ q ∈ valuesLoaded v c, dnamed q.1 = true := by
  intro q hq
  simp only [valuesLoaded, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  have := c.isLt
  simp only [dnamed, dnamed0, biasNamed, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq]
  omega

theorem valuesHalves_keys (b : Bool) (v : V) (n : Nat) :
    ∀ q ∈ valuesHalves b v n, dnamed q.1 = true := by
  have h : ∀ q ∈ halvesList b v, dnamed q.1 = true := by
    cases b <;> simp only [halvesList, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true] <;> and_intros <;> rfl
  exact fun q hq => h q (List.mem_of_mem_take hq)

theorem valuesProbP_keys (p : Params) (v : V) : ∀ q ∈ valuesProbP p v, dnamed q.1 = true := by
  simp only [valuesProbP, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> rfl

theorem valuesRun_keys (p : Params) (v : V) : ∀ q ∈ valuesRun p v, dnamed q.1 = true := by
  intro q hq
  simp only [valuesRun, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> rfl

theorem valuesPlainP_keys (p : Params) (v : V) : ∀ q ∈ valuesPlainP p v, dnamed q.1 = true := by
  intro q hq
  unfold valuesPlainP at hq
  split at hq <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem keys_of_all {l : List (Nat × Value)} (h : (l.map Prod.fst).all dnamed = true) :
    ∀ q ∈ l, dnamed q.1 = true :=
  fun q hq => List.all_eq_true.mp h q.1 (List.mem_map_of_mem hq)

theorem valuesBiasM_keys (p : Params) (v : V) : ∀ q ∈ valuesBiasM p v, dnamed q.1 = true := by
  intro q hq
  simp only [valuesBiasM, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> rfl

theorem valuesProdB_keys (p : Params) (v : V) : ∀ q ∈ valuesProdB p v, dnamed q.1 = true := by
  intro q hq
  simp only [valuesProdB, List.mem_map, List.mem_range] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  simp only [dnamed, dnamed0, biasNamed, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq]
  omega

theorem valuesData0_keys (p : Params) (L : Launch) (g : Nat) (d : D) :
    ∀ q ∈ valuesData0 p L g d, dnamed q.1 = true := by
  obtain ⟨s, v, k, acc⟩ := d
  have hfin : ∀ q ∈ [(7256, mxVal v), (7257, Value.float .f32 v.rs)], dnamed q.1 = true := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> rfl
  have app : ∀ {l₁ l₂ : List (Nat × Value)}, (∀ q ∈ l₁, dnamed q.1 = true) →
      (∀ q ∈ l₂, dnamed q.1 = true) → ∀ q ∈ l₁ ++ l₂, dnamed q.1 = true :=
    fun h1 h2 q hq => (List.mem_append.mp hq).elim (h1 q) (h2 q)
  have nil : ∀ q ∈ ([] : List (Nat × Value)), dnamed q.1 = true := by simp
  have hneg : ∀ q ∈ [(1230, negS p)], dnamed q.1 = true := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; rfl
  cases s
  all_goals (try cases ‹Rd›)
  all_goals (try cases ‹Bool›)
  all_goals simp only [valuesData0]
  all_goals first
    | exact keys_of_all (by rfl)
    | exact nil
    | exact hneg
    | exact valuesRun_keys p v
    | exact valuesPlainP_keys p v
    | exact hfin
    | exact app (valuesPairs_keys _ _ _ (by omega)) (valuesRun_keys p v)
    | exact app (app (valuesPairs_keys _ _ _ (by omega)) (valuesRun_keys p v))
        (valuesHalves_keys _ v _)
    | exact app (app (valuesPairs_keys _ _ _ (by omega)) (valuesRun_keys p v))
        (valuesHalves_keys _ v _)
    | exact app (valuesPairs_keys _ _ _ (by omega)) (valuesPlainP_keys p v)
    | exact app (valuesPlainP_keys p v) (valuesProbP_keys p v)
    | exact app (valuesPairs_keys _ _ _ (by have := (‹Fin 4›).isLt; omega)) (valuesRun_keys p v)
    | exact app (app (valuesRun_keys p v) (valuesBiasM_keys p v)) (valuesProdB_keys p v)
    | exact app (valuesRun_keys p v) (valuesBiasM_keys p v)
    | exact app (app (valuesLoaded_keys v _)
        (valuesPairs_keys _ _ _ (by have := (‹Fin 4›).isLt; omega))) (valuesRun_keys p v)

theorem valuesData_keys (p : Params) (L : Launch) (g : Nat) (d : D) :
    ∀ q ∈ valuesData p L g d, dnamed q.1 = true := by
  obtain ⟨s, v, k, acc⟩ := d
  have h1 : ∀ q ∈ p1Data p L g v, dnamed q.1 = true := keys_of_all (by rfl)
  have h2 : ∀ q ∈ pPData p v, dnamed q.1 = true := keys_of_all (by kernel_rfl)
  cases s
  all_goals (try cases ‹Rd›)
  all_goals simp only [valuesData]
  all_goals first
    | exact h1
    | exact h2
    | exact valuesData0_keys p L g _

/-- On a control register the two tables agree. -/
theorem valueOfD_ctl (d : D) {r : Nat} (h : ctl r = true) :
    valueOfD p L g d r = valueOf p L g d r := by
  have hn : (valuesData p L g d).lookup r = none := by
    rw [List.lookup_eq_none_iff]
    intro q hq
    have := ctl_of_dnamed (valuesData_keys p L g d q hq)
    simp only [bne_iff_ne, ne_eq]
    intro e; rw [e] at h; rw [h] at this; cases this
  simp only [valueOfD, hn, Option.getD_none]

/-- **`codeD`'s facts contain `code`'s.** -/
theorem factsD_mono {R : Nat → Option Value} {d : D} (h : Holds R (factsD p L g d)) :
    Holds R ((code p L g).facts d) := by
  refine holds_of_pointwise fun r hr => ?_
  simp only [ctlLive, List.mem_filter] at hr
  rw [← valueOfD_ctl d hr.2]
  exact holds_mem h (mem_factsFrom (by
    unfold liveD liveF; split <;> simp [List.mem_filter, hr.1, hr.2]))

theorem atD_mono {d : D} {t : TState} (h : (codeD p L g).AtD d t) : (code p L g).AtD d t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, factsD_mono h.2.2.2.2⟩

/-- **Every shape obligation of `code` is one of `codeD`.** -/
theorem shapeAtD {P : D → Event → Prop} {d : D} (h : (code p L g).ShapeAt P d) :
    (codeD p L g).ShapeAt P d :=
  fun hat hi hc hf => h (atD_mono hat) hi hc hf

theorem shapeD {P : D → Event → Prop} (h : (code p L g).Shape P) : (codeD p L g).Shape P :=
  fun hat hi hc hf => h (atD_mono hat) hi hc hf

/-- The value of a key in a table of shifted keys. -/
theorem lookup_shift {β : Type} (base : Nat) (f : Nat → β) {l : List Nat} {q : Nat}
    (hq : q ∈ l) : (l.map fun i => (base + i, f i)).lookup (base + q) = some (f q) := by
  induction l with
  | nil => cases hq
  | cons i rest ih =>
    by_cases e : q = i
    · subst e; simp
    · have hr : q ∈ rest := (List.mem_cons.mp hq).resolve_left e
      have hb : (base + q == base + i) = false := by simp [e]
      simp only [List.map_cons, List.lookup, hb]
      exact ih hr

/-- A key outside a table of shifted keys has no value. -/
theorem lookup_shift_none {β : Type} (base : Nat) (f : Nat → β) {l : List Nat} {q : Nat}
    (hq : ∀ i ∈ l, base + i ≠ q) : (l.map fun i => (base + i, f i)).lookup q = none := by
  rw [List.lookup_eq_none_iff]
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp only [bne_iff_ne, ne_eq]
  exact fun e => hq i hi e.symm

/-- A score load into slot `c` keeps the pairs of the earlier loads. -/
theorem valuesPairs_update (r : Rd) (v : V) (c : Fin 4) (xs : Nat → ℝ) {n : Nat}
    (hn : n ≤ 16 * c.val) :
    valuesPairs r { v with sv := Function.update v.sv c xs } n = valuesPairs r v n := by
  unfold valuesPairs
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  have h1 : (⟨2 * j / 32 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) ≠ c := by
    intro e; have := congrArg Fin.val e; simp only at this; omega
  have h2 : (⟨(2 * j + 1) / 32 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) ≠ c := by
    intro e; have := congrArg Fin.val e; simp only at this; omega
  simp only [V.score, Function.update_of_ne h1, Function.update_of_ne h2]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
