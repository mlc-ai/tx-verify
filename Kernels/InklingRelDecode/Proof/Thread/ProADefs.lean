-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Flow.Sites
public import Kernels.InklingRelDecode.Flow.Code
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.SignedBits
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Segment
public import Lemmas.Flow.Hooks
public import Lemmas.Flow.TensorIssue
public import Lemmas.Flow.Events
public import Lemmas.Flow.Vector
public import Lemmas.Flow.ParamObject
public import Lemmas.Flow.EventCont
public import Kernels.InklingRelDecode.Proof.Thread.RawWord

@[expose] public section

/-! # The default partition's prologue as abstract states

The 128 threads of warps 0 to 3 of `_rel_verify_kernel` leave the common code at the
`@!%p4 bra` of pc 19 and run, from the first `setmaxnreg.inc` (pc 27) to the `barrier.sync 1`
of pc 573:

* the parameters the partition reads (pc 20 to 26), the CTA coordinates and the three words
  `cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]` (pc 28 to 41), from which the
  code computes `q_len`, `past`, `n_bias`, `num_iters` (a signed division, pc 59) and the
  row-validity predicates of the query rows (pc 42 to 129);
* twelve `elect.sync` / `mbarrier.init` pairs for the twelve mbarriers (pc 130 to 178), the
  proxy fence and the partition's barrier (pc 179, 180);
* when `num_pre` is not zero, the issue of up to three K/V blocks (pc 181 to 315): per block a
  barrier, the lane-0 `mbarrier.arrive.expect_tx`, two block-table loads, and four tensor copies
  each by an elected lane;
* the parameters of the outputs (pc 316 to 318), the query loads (64 `ld.global.b16`, each
  guarded by the row-validity predicate of its row group; pc 388 to 514), their packing into
  eight `st.shared.v4.b32` (pc 526 to 568), the proxy fence, the role table `0x01000202`
  (pc 570), `(num_pre, num_iters)` (pc 571) and `barrier.sync 1` (pc 573).

A state is the next event with the data the code carries: the inherited registers and
parameter words (`Inh`), the three loaded words and the six block-table words, and the 64
loaded query values, which are recorded as the load events carry them. Every register the code
computes is a function of these (`table`): each register is valued by the term the evaluator
computes for its instruction on the values of its operands, in the operations of the code
(`wAdd32` …), so that a local segment agrees with the table by unfolding. What the values mean
(`q_len`, `num_iters`, …) is `ProAExit`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-! ### The code's integer operations

Each function mirrors the evaluator's rule for one instruction form on the stored bits of its
operands (a register's stored `BitVec 64`, or an immediate as `BitVec.ofInt 64 k`), so that the
value a segment computes and the value the table states agree by unfolding. -/

/-- A CTA coordinate as `mov.u32` reads it. -/
def wCta (L : Launch) (g : Nat) (d : Dim) : BitVec 64 :=
  truncBits 32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get d))
/-- `mov.b32 r, global_smem`. -/
def wSmem (L : Launch) : BitVec 64 := truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0))
/-- `add.s32`. -/
def wAdd32 (a b : BitVec 64) : BitVec 64 := truncBits 32 (truncBits 32 a + truncBits 32 b)
/-- `sub.s32`. -/
def wSub32 (a b : BitVec 64) : BitVec 64 := truncBits 32 (truncBits 32 a - truncBits 32 b)
/-- `mul.lo.s32`. -/
def wMulLo32 (a b : BitVec 64) : BitVec 64 := truncBits 32 (truncBits 32 a * truncBits 32 b)
/-- `mad.lo.s32`. -/
def wMadLo32 (a b c : BitVec 64) : BitVec 64 :=
  truncBits 32 (truncBits 32 a * truncBits 32 b + truncBits 32 c)
/-- `max.s32`. -/
def wMaxS32 (a b : BitVec 64) : BitVec 64 :=
  if compare (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
      (if (some IType.s == some IType.s) = true then IType.s else IType.u) 32
      (truncBits 32 a) (truncBits 32 b) = true then truncBits 32 a else truncBits 32 b
/-- `min.s32`. -/
def wMinS32 (a b : BitVec 64) : BitVec 64 :=
  if compare (if (IntOp.min false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
      (if (some IType.s == some IType.s) = true then IType.s else IType.u) 32
      (truncBits 32 a) (truncBits 32 b) = true then truncBits 32 a else truncBits 32 b
/-- `min.u32`. -/
def wMinU32 (a b : BitVec 64) : BitVec 64 :=
  if compare (if (IntOp.min false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
      (if (some IType.u == some IType.s) = true then IType.s else IType.u) 32
      (truncBits 32 a) (truncBits 32 b) = true then truncBits 32 a else truncBits 32 b
/-- `shr.u32`. -/
def wShrU32 (a s : BitVec 64) : BitVec 64 :=
  if (truncBits 32 s).toNat ≥ 32 then 0 else truncBits 32 a >>> (truncBits 32 s).toNat
/-- `2 ^ n` as an `Int` with the core's power instance. -/
abbrev pw (n : Nat) : Int :=
  @HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow)) 2 n
/-- `shr.s32`. -/
def wShrS32 (a s : BitVec 64) : BitVec 64 :=
  truncBits 32 (BitVec.ofInt 64 (toSigned 32 (truncBits 32 a) / pw (min (truncBits 32 s).toNat 32)))
/-- `shl.b32`. -/
def wShl32 (a s : BitVec 64) : BitVec 64 :=
  if (truncBits 32 s).toNat ≥ 32 then 0
  else truncBits 32 (truncBits 32 a <<< (truncBits 32 s).toNat)
/-- `shl.b64`. -/
def wShl64 (a s : BitVec 64) : BitVec 64 :=
  if (truncBits 32 s).toNat ≥ 64 then 0
  else truncBits 64 (truncBits 64 a <<< (truncBits 32 s).toNat)
/-- `shl.b16`. -/
def wShl16 (a s : BitVec 64) : BitVec 64 :=
  if (truncBits 32 s).toNat ≥ 16 then 0
  else truncBits 16 (truncBits 16 a <<< (truncBits 32 s).toNat)
/-- `and.b32`. -/
def wAnd32 (a b : BitVec 64) : BitVec 64 := truncBits 32 a &&& truncBits 32 b
/-- `or.b32`. -/
def wOr32 (a b : BitVec 64) : BitVec 64 := truncBits 32 a ||| truncBits 32 b
/-- `xor.b32`. -/
def wXor32 (a b : BitVec 64) : BitVec 64 := truncBits 32 a ^^^ truncBits 32 b
/-- `not.b32`. -/
def wNot32 (a : BitVec 64) : BitVec 64 := truncBits 32 (~~~truncBits 32 a)
/-- `or.b16`. -/
def wOr16 (a b : BitVec 64) : BitVec 64 := truncBits 16 a ||| truncBits 16 b
/-- `add.s16`. -/
def wAdd16 (a b : BitVec 64) : BitVec 64 := truncBits 16 (truncBits 16 a + truncBits 16 b)
/-- `cvt.u16.u32`. -/
def wCvt16of32 (a : BitVec 64) : BitVec 64 := truncBits 16 (truncBits 32 a)
/-- `cvt.u32.u16`. -/
def wCvt32of16 (a : BitVec 64) : BitVec 64 := truncBits 32 (truncBits 16 a)
/-- `mul.hi.u16`. -/
def wMulHiU16 (a b : BitVec 64) : BitVec 64 :=
  truncBits 16 (BitVec.ofInt 64
    ((if (some IType.u == some IType.s) = true then
        toSigned 16 (truncBits 16 a) * toSigned 16 (truncBits 16 b)
      else ↑(truncBits 16 a).toNat * ↑(truncBits 16 b).toNat) / 2 ^ 16))
/-- `bfe.u32`. -/
def wBfeU32 (a p l : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (bfeBits IType.u 32 (truncBits 32 a).toNat ((truncBits 32 p).toNat % 256)
    ((truncBits 32 l).toNat % 256))
/-- `add.s64`. -/
def wAdd64 (a b : BitVec 64) : BitVec 64 := truncBits 64 (truncBits 64 a + truncBits 64 b)
/-- `mul.wide.u32`. -/
def wMulWideU32 (a b : BitVec 64) : BitVec 64 :=
  if (some IType.u == some IType.s) = true then
    truncBits (2 * 32)
      (BitVec.ofInt 64 (toSigned 32 (truncBits 32 a) * toSigned 32 (truncBits 32 b)))
  else BitVec.ofNat 64 ((truncBits 32 a).toNat * (truncBits 32 b).toNat)
/-- `mul.wide.s32`. -/
def wMulWideS32 (a b : BitVec 64) : BitVec 64 :=
  if (some IType.s == some IType.s) = true then
    truncBits (2 * 32)
      (BitVec.ofInt 64 (toSigned 32 (truncBits 32 a) * toSigned 32 (truncBits 32 b)))
  else BitVec.ofNat 64 ((truncBits 32 a).toNat * (truncBits 32 b).toNat)
/-- `mad.wide.u32`. -/
def wMadWideU32 (a b c : BitVec 64) : BitVec 64 :=
  intBits (2 * 32) (intOf IType.u 32 (truncBits 32 a) * intOf IType.u 32 (truncBits 32 b) +
    intOf IType.u (2 * 32) (truncBits (2 * 32) c))
/-- `mad.wide.s32`. -/
def wMadWideS32 (a b c : BitVec 64) : BitVec 64 :=
  intBits (2 * 32) (intOf IType.s 32 (truncBits 32 a) * intOf IType.s 32 (truncBits 32 b) +
    intOf IType.s (2 * 32) (truncBits (2 * 32) c))
/-- `div.s32` of two registers, when the evaluator has a rule. -/
def wDivS32 (a b : BitVec 64) : BitVec 64 :=
  intBits 32 ((intOf IType.s 32 (truncBits 32 a)).tdiv (intOf IType.s 32 (truncBits 32 b)))
/-- `setp.lt.u32`. -/
def pLtU32 (a b : BitVec 64) : Bool :=
  compare Cmp.lt ((some IType.u).getD IType.b) 32 (truncBits 32 a) (truncBits 32 b)
/-- `setp.gt.s32`. -/
def pGtS32 (a b : BitVec 64) : Bool :=
  compare Cmp.gt ((some IType.s).getD IType.b) 32 (truncBits 32 a) (truncBits 32 b)
/-- `setp.eq.b32`. -/
def pEqB32 (a b : BitVec 64) : Bool :=
  compare Cmp.eq ((some IType.b).getD IType.b) 32 (truncBits 32 a) (truncBits 32 b)
/-- `setp.ne.b32`. -/
def pNeB32 (a b : BitVec 64) : Bool :=
  compare Cmp.ne ((some IType.b).getD IType.b) 32 (truncBits 32 a) (truncBits 32 b)

/-! ### The inherited registers and parameter words -/

/-- What the partition reads of the registers it inherits and of the kernel parameters.
`%r2` (`tm`, the Tensor Memory base `ld.shared` read in the common code), the strides and counts
`%r67 … %r71` (parameters 18, 21, 22, 23, 24: `stride_bt`, `page_rows`, `head_rows`,
`head_cols`, `num_splits`) and the block-table base `%rd72` (parameter 7) come from the common
code. The other parameters are read by this region itself, and `x` is the 64-bit word the launch
gives the parameter: `%r64` (15: `softmax_scale`), `%r65` (16: `stride_q_t`), `%r66` (17:
`stride_rel_t`), `%rd70` (0: Q), `%rd71` (6: relative logits), `%rd73` (8: `seq_lens`), `%rd74` (9:
`cu_seqlens_q`), `%r72` (25: `num_tokens`), `%rd75` (10: `OPart`) and `%rd76` (11: `LsePart`).
The registers carried unchanged (`%p3`, `%rd1`) are `rest`. -/
structure Inh where
  rest : Nat → Value
  tm : Nat
  w67 : Nat
  w68 : Nat
  w69 : Nat
  w70 : Nat
  w71 : Nat
  btB : Nat
  x15 : BitVec 64
  x16 : BitVec 64
  x17 : BitVec 64
  x0 : BitVec 64
  x6 : BitVec 64
  x8 : BitVec 64
  x9 : BitVec 64
  x25 : BitVec 64
  x10 : BitVec 64
  x11 : BitVec 64

/-- The data of a state: the inherited registers and parameters, the words `cu_seqlens_q[req]`
(`cu0`), `cu_seqlens_q[req + 1]` (`cu1`) and `seq_lens[req]` (`sk`) the loads return, the six
block-table words (`b0 … b5`: `%r220`, `%r226`, `%r240`, `%r246`, `%r262`, `%r268`) and the
values the 64 query loads returned (`q k`: the load `k` in program order; a load that was
masked leaves the zero `qZero`), and the outcome of each `elect.sync` of the region (`el pc`, for
the election at program counter `pc`: whether the thread is the elected lane), and the words the
three broadcasts of the warp index returned (`sh0`, `sh1`, `sh2`: `%r232`, `%r253`, `%r275`, as
the shuffles returned them; bit 0 picks the half of the K/V preload the block's copies fill), and
the Tensor Memory base word `w` (`%r2`) as the common start's load returned it (`pro.tm` is its
32-bit number when the word has one; the machine follows every word). -/
structure Dat where
  pro : Inh
  cu0 : Nat
  cu1 : Nat
  sk : Nat
  b0 : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  b4 : Nat
  b5 : Nat
  q : Nat → Value
  el : Nat → Bool
  sh0 : Value
  sh1 : Value
  sh2 : Value
  w : Value

/-- The 16-bit zero (`mov.b16 %rs18, 0`) a masked query load leaves in its register. -/
def qZero : Value := .bits 16 (truncBits 16 (BitVec.ofInt 64 0))

/-- The thread index `%tid.x` (`%r1`). -/
abbrev tidOf (L : Launch) (g : Nat) : Nat := g % L.block

/-- A CTA coordinate (`%ctaid.x`, `.y`, `.z`) of the thread's CTA. -/
def cta (L : Launch) (g : Nat) (d : Dim) : Nat := (L.ctaidOf (g / L.block)).get d

/-- What the machine needs of the inherited registers: the thread is in the default partition,
`num_splits` is a positive 31-bit number above this CTA's split index (the divisor and the
numerators of the two `div.s32` are then in range), and the parameters this region reads are
the words of `Pro` (`L.params`). -/
structure ArgsOk (L : Launch) (g : Nat) (P : Inh) : Prop where
  tid : tidOf L g < 128
  splitsPos : 0 < P.w71
  splitsRange : P.w71 < 2 ^ 31
  splitIdx : cta L g .x < P.w71
  p0 : L.params (param "0") = some P.x0
  p6 : L.params (param "6") = some P.x6
  p8 : L.params (param "8") = some P.x8
  p9 : L.params (param "9") = some P.x9
  p10 : L.params (param "10") = some P.x10
  p11 : L.params (param "11") = some P.x11
  p15 : L.params (param "15") = some P.x15
  p16 : L.params (param "16") = some P.x16
  p17 : L.params (param "17") = some P.x17
  p25 : L.params (param "25") = some P.x25

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
