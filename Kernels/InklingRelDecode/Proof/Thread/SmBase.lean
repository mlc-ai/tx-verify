-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Sites
public import Kernels.InklingRelDecode.Flow.Code
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Thread.WorkerBase
public import Lemmas.Flow.Code
public import Lemmas.Flow.Facts
public import Lemmas.Flow.Next
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.RegBits
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Kernels.InklingRelDecode.Proof.Thread.SmMin
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The default-partition softmax region: sites, state and entry numbers

The data of the softmax region's machine (`Sm.lean`): the numbers the prologue left in registers
(`Ent`), the sites, the state `D` and the pointer arithmetic of the bias loads. See `Sm.lean` for
the machine, its register table and its successor function. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### Assumptions and shape -/

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-- The thread's index in the block (`%r1`). -/
abbrev tidOf (L : Launch) (g : Nat) : Nat := g % L.block

/-- The numbers the default prologue left in registers at pc 573 that the region reads (`%rK` is
decoder id `461 + K`, `%rdK` is `1948 + K`, `%rsK` is `181 + K`, `%pK` is `K`). Every number is
the value of its register as a natural number: 32 bits for an `%r`, 64 bits for an `%rd`. -/
structure Ent where
  /-- The Tensor Memory base (`%r2`). -/
  tm : Nat
  /-- `ctaid.x`, the first block of the split (`%r17`). -/
  split : Nat
  /-- `q_len` (`%r20`). -/
  qlen : Nat
  /-- `seqlen_k - q_len`, the position of the first query token (`%r21`). -/
  past : Nat
  /-- `n_bias` (`%r22`). -/
  nbias : Nat
  /-- `%r23` and `%r24` (`%r24` is read by the bias pointer, `%r23` is carried). -/
  r23 : Nat
  r24 : Nat
  /-- The block count of the split as `div.s32` leaves it (`%r25`) and as `max.s32` clamps it
  (`%r26`, `num_iters`). -/
  r25 : Nat
  r26 : Nat
  /-- `kv_head * 6` (`%r29`). -/
  kvh : Nat
  /-- `cu_seqlens_q[req]` (`%r149`). -/
  qs : Nat
  /-- The bits of `softmax_scale` (`%r64`), its real value, and `stride_rel_t` (`%r66`). -/
  scb : Nat
  sc : ℝ
  strRel : Nat
  /-- `num_splits` (`%r71`) and `num_tokens` (`%r72`). -/
  splits : Nat
  ntok : Nat
  /-- The pointers `Rel` (`%rd71`) and the two outputs (`%rd75`, `%rd76`). -/
  rel : Nat
  rd75 : Nat
  rd76 : Nat

/-- What the entry numbers must satisfy: they are words of their registers, `q_len` is a
non-negative signed word, `num_iters` is the clamp of the block count, the scale reads as a
positive real, and every block of the loop has a block number below `2 ^ 31`. -/
structure Ent.Ok (e : Ent) : Prop where
  tm : e.tm < 2 ^ 32
  split : e.split < 2 ^ 32
  qlen : e.qlen < 2 ^ 31
  past : e.past < 2 ^ 32
  nbias : e.nbias < 2 ^ 31
  r24 : e.r24 < 2 ^ 32
  r25 : e.r25 < 2 ^ 32
  r26 : e.r26 = if e.r25 < 2 ^ 31 then e.r25 else 0
  kvh : e.kvh < 2 ^ 32
  qs : e.qs < 2 ^ 32
  strRel : e.strRel < 2 ^ 32
  splits : e.splits < 2 ^ 32
  rel : e.rel < 2 ^ 64
  scale : valFloat .f32 (b32 e.scb) = .ok e.sc
  scalePos : 0 < e.sc
  blk : e.split + e.r26 * e.splits + e.splits < 2 ^ 31
  /-- The words of the count and of the two output pointers. -/
  ntok : e.ntok < 2 ^ 32
  rd75 : e.rd75 < 2 ^ 64
  rd76 : e.rd76 < 2 ^ 64
  /-- The split is below `num_splits`, the request's first token is at most the token count and
  the head group is at most the second (`kvh = 6 * ctaid.y`, `ctaid.y ≤ 1`): the numbers of the
  output row index. -/
  splitLt : e.split < e.splits
  qsLe : e.qs ≤ e.ntok
  kvhLe : e.kvh ≤ 6
  /-- The launch leaves room for the output row index of the padding rows of the last request
  (`Pre.outRangeSlack`): their token is up to 10 past the request's first. -/
  slack : (e.splits * e.ntok + 11) * 12 * 128 ≤ 2 ^ 31
  /-- The pointers are aligned to their access sizes: `Rel` to the 2 bytes of a `bf16` word, the
  two outputs to the 4 bytes of an `f32` word (`Pre.relAlign`, `oAlign`, `lseAlign`). -/
  relAl : e.rel % 2 = 0
  rd75Al : e.rd75 % 4 = 0
  rd76Al : e.rd76 % 4 = 0
  /-- The Tensor Memory base's column field has room for the 512 columns (the common start
  follows only such a base word, `DStart.next`). -/
  col : e.tm + 512 ≤ 2 ^ 16
  /-- The integer arithmetic of the score stage stays below `2 ^ 31` (its comparisons are signed):
  the key `128 n` of every block `n = split + i · num_splits` of the loop, `past` plus the 128
  columns of a block, and `past / 128` (`Pre.seqRange`, `seqlen_k + 511 < 2 ^ 31`). -/
  rngBlk : ∀ i < e.r26, (e.split + i * e.splits) * 128 + 256 < 2 ^ 31
  rngPast : e.past + 64 + 64 < 2 ^ 31
  rngR23 : e.r23 < 2 ^ 31

/-! ### Functions of the thread index

The thread index `T` of a softmax thread is below 128. Its row of the score tile is `row T`, its
query token `tokOf T` (the code computes `row * 43 >> 8`, which is `row / 6` for a row below 64)
and its head `remOf T` within the group of 6. -/

abbrev row (T : Nat) : Nat := T % 16 + T / 32 % 4 * 16
abbrev tokOf (T : Nat) : Nat := row T * 43 / 256
abbrev remOf (T : Nat) : Nat := row T - tokOf T * 6
/-- The thread's half of the row: bit 4 of the thread index. -/
abbrev half (T : Nat) : Nat := T / 16 % 2

/-- A 16-bit register value. -/
def b16 (n : Nat) : Value := .bits 16 (BitVec.ofNat 64 n)

/-- The thread's row is a query row: below 60 and with a token below `q_len` (`%p175`). -/
def rowValid (e : Ent) (T : Nat) : Bool := decide (row T < 60 ∧ tokOf T < e.qlen)

/-- The bias loads of the first block are issued: the split has blocks, the row is valid and the
first block is at or after `n_bias` (`%p85`). -/
def act0 (e : Ent) (T : Nat) : Bool :=
  decide (0 < e.r25 ∧ e.r25 < 2 ^ 31) && rowValid e T && decide (e.nbias ≤ e.split)

/-- The loads of the next block are issued (`%p92`) in iteration `i`: a valid row, a next
iteration, and the next block at or after `n_bias` (`block = split + i * num_splits`). -/
def actB (e : Ent) (T i : Nat) : Bool :=
  rowValid e T && decide (i + 1 < e.r25 ∧ e.r25 < 2 ^ 31) &&
    decide (e.nbias ≤ e.split + i * e.splits + e.splits)

/-- The output row index the code computes for the thread of index `T`
(`((split * num_tokens + token) + cu_seqlens_q[req]) * 12 + head`, in 32-bit arithmetic with the
order of the code's operations: `Br.In.Ok.row`). -/
def rowIdx (e : Ent) (T : Nat) : Nat :=
  ((((e.ntok * e.split + tokOf T) % 2 ^ 32 + e.qs) % 2 ^ 32) * 12 +
    (e.kvh + remOf T) % 2 ^ 32) % 2 ^ 32

/-- The remainder of the row by 6 is below 6, and the token of a row of the tile is at most 10. -/
theorem remOf_lt (T : Nat) : remOf T < 6 := by
  unfold remOf tokOf row
  omega

theorem tokOf_le (T : Nat) : tokOf T ≤ 10 := by
  unfold tokOf row
  omega

/-- **The output row index of a softmax thread is below `2 ^ 24`** where the launch leaves room
for the padding rows: `(num_splits * num_tokens + 11) * 12 * 128 ≤ 2 ^ 31`. -/
theorem Ent.Ok.rowIdx_lt {e : Ent} (h : e.Ok) (hs : (e.splits * e.ntok + 11) * 12 * 128 ≤ 2 ^ 31)
    (T : Nat) : rowIdx e T < 2 ^ 24 := by
  have h1 := remOf_lt T
  have h2 := tokOf_le T
  have h3 : e.split * e.ntok + e.ntok ≤ e.splits * e.ntok := by
    have := Nat.mul_le_mul_right e.ntok (Nat.succ_le_of_lt h.splitLt)
    rw [Nat.succ_mul] at this
    exact this
  have h4 := h.qsLe
  have h5 := h.kvhLe
  unfold rowIdx
  rw [Nat.mul_comm e.ntok e.split]
  generalize e.split * e.ntok = A at *
  generalize e.splits * e.ntok = B at *
  generalize tokOf T = c at *
  generalize remOf T = r at *
  have c1 : (A + c) % 2 ^ 32 = A + c := Nat.mod_eq_of_lt (by omega)
  have c2 : (A + c + e.qs) % 2 ^ 32 = A + c + e.qs := Nat.mod_eq_of_lt (by omega)
  have c3 : (e.kvh + r) % 2 ^ 32 = e.kvh + r := Nat.mod_eq_of_lt (by omega)
  have c4 : ((A + c + e.qs) * 12 + (e.kvh + r)) % 2 ^ 32 = (A + c + e.qs) * 12 + (e.kvh + r) :=
    Nat.mod_eq_of_lt (by omega)
  rw [c1, c2, c3, c4]
  omega

/-! ### Pointer arithmetic

The pointer of the bias loads is built by `mul.wide`/`mad.wide` chains of 32-bit values into
64-bit ones. The code treats the 32-bit operand of the `.s32` forms as signed; `sxw x` is the
sign extension of the low 32 bits of `x` as a number below `2 ^ 64`. Each stage is stated as the
number the instruction computes. -/

/-- The sign extension of a 32-bit word to 64 bits. -/
def sxw (x : Nat) : Nat := x % 2 ^ 32 + x % 2 ^ 32 / 2 ^ 31 * (2 ^ 64 - 2 ^ 32)

/-- `%r345 = %r36 * 1280` and `%r346 = 1280 - %r24`. -/
def r345 (e : Ent) (T : Nat) : Nat := (e.kvh + remOf T) % 2 ^ 32 * 1280 % 2 ^ 32
def r346 (e : Ent) : Nat := (1280 + 2 ^ 32 - e.r24 % 2 ^ 32) % 2 ^ 32

/-- The stages of the bias row pointer: `%rd258` (`mul.wide.s32 %r342, %r66`), `%rd259` (`shl`),
`%rd260` (`+ %rd71`), `%rd261` (`mad.wide.u32 %r345, 2`), `%rd262` (`mad.wide.s32 %r346, 2`) and
`%rd9` (`mad.wide.u32 %r337, 2`). -/
def p258 (e : Ent) (T : Nat) : Nat := sxw ((e.qs + tokOf T) % 2 ^ 32) * sxw e.strRel % 2 ^ 64
def p259 (e : Ent) (T : Nat) : Nat := p258 e T * 2 % 2 ^ 64
def p260 (e : Ent) (T : Nat) : Nat := (e.rel + p259 e T) % 2 ^ 64
def p261 (e : Ent) (T : Nat) : Nat := (r345 e T * 2 + p260 e T) % 2 ^ 64
def p262 (e : Ent) (T : Nat) : Nat := (sxw (r346 e) * 2 + p261 e T) % 2 ^ 64
def p9 (e : Ent) (T : Nat) : Nat := (half T * 64 * 2 + p262 e T) % 2 ^ 64

/-- The key offset of a block's bias: `n * 128` as the 32-bit register `%r1451`, and the pointer
of its first word (`mad.wide.s32 %rd193, %r1451, 2, %rd9`); word `k` is `2 k` bytes further. -/
def key (n : Nat) : Nat := n * 128 % 2 ^ 32
def ptrAt (e : Ent) (T k : Nat) : Nat := (sxw k * 2 + p9 e T) % 2 ^ 64

/-- The block number of iteration `i`. -/
def blkOf (e : Ent) (i : Nat) : Nat := e.split + i * e.splits

/-- The position of the thread's query token (`%r349 = past + token`) and the offset of the
first key's column from it (`%r350 = half * 64 - pos`). -/
def posOf (e : Ent) (T : Nat) : Nat := (e.past + tokOf T) % 2 ^ 32
def pos2Of (e : Ent) (T : Nat) : Nat := (half T * 64 + 2 ^ 32 - posOf e T) % 2 ^ 32

/-- The sum `pos - a` as a 32-bit register (`add.s32` by `-a`). -/
def posSum (e : Ent) (T a : Nat) : Value := b32 ((e.past + tokOf T + 2 ^ 32 - a) % 2 ^ 32)

/-- The pair `pos - a`, `pos - b` the code packs (`add.s32` by a negative immediate, then
`mov.b64 {lo, hi}`). -/
def pairPos (e : Ent) (T a b : Nat) : Value :=
  joinValue (posSum e T a) (posSum e T b)

/-! ### Sites -/

/-- The event instructions of the region, in execution order. -/
inductive Site where
  /-- Region A: the register increase, the named barrier, the 64 preloads of the first block's
  bias, then the loop's own bias loads. -/
  | setMaxReg | bar0
  | pre (j : Fin 64)
  | nxt (j : Fin 64)
  /-- Region B: the `s_ready` poll, the broadcast of the warp index, the S tile's `tcgen05.ld`
  and its wait. -/
  | waitS | shfl4 | ldS | waitLd
  /-- Region C: the two row shuffles that bound the score, maximum, exponential and sum code. -/
  | shfl5 | shfl6
  /-- Region D: the remaining shuffle exchanges, the row sum's shared store, its reload, the
  `o_done` poll, the O rescale and the P store with its `p_ready` arrival. -/
  | bar22 | shfl7 | shfl8 | shfl9 | shfl10 | store10 | bar23 | ldL | shfl11 | shfl12
  | waitO | ldO | waitLdO | bar24 | stO | waitStO
  | bar20 | tmemSt | tmemWait | bar21 | arrive
  deriving DecidableEq

def Site.pc : Site → Nat
  | .setMaxReg => Flow.setMaxReg_1 | .bar0 => Flow.bar_19
  | .pre j => 680 + 2 * j.val
  | .nxt j => 1124 + 2 * j.val
  | .waitS => Flow.mbarWait_0 | .shfl4 => Flow.shfl_4 | .ldS => Flow.tmemLoad_0
  | .waitLd => Flow.tmemWait_1
  | .shfl5 => Flow.shfl_5 | .shfl6 => Flow.shfl_6
  | .bar22 => Flow.bar_22 | .shfl7 => Flow.shfl_7 | .shfl8 => Flow.shfl_8
  | .shfl9 => Flow.shfl_9 | .shfl10 => Flow.shfl_10 | .store10 => Flow.store_10
  | .bar23 => Flow.bar_23 | .ldL => Flow.load_202 | .shfl11 => Flow.shfl_11
  | .shfl12 => Flow.shfl_12
  | .waitO => Flow.mbarWait_1 | .ldO => Flow.tmemLoad_1 | .waitLdO => Flow.tmemWait_2
  | .bar24 => Flow.bar_24 | .stO => Flow.tmemStore_1 | .waitStO => Flow.tmemWait_3
  | .bar20 => Flow.bar_20 | .tmemSt => Flow.tmemStore_0 | .tmemWait => Flow.tmemWait_0
  | .bar21 => Flow.bar_21 | .arrive => Flow.mbarArrive_3

/-! ### The state -/

/-- The numbers the score stage hands to the loop's tail (pcs 949-950, 2252-2258), kept as the
registers they are in: the new running maximum (`%r1061`), the lazy-rescale decision (`%p168`),
`alpha` (`%r46`), the row sum of the block (`%r1070`) and the minimum of the alphas of the lanes
and warps combined so far (`%r1083`, read by the rescale test), and the numbers the stage's
code leaves between its shuffles. -/
structure Stg where
  /-- The new running maximum (`%r1061`); before the first shuffle of the row maximum, the pattern
  of `-inf`. -/
  mn : Value := b32 4286578688
  kp : Bool := false
  al : Value := b32 0
  rs : Value := b32 0
  m2 : Value := b32 0
  /-- The real number `alpha` stands for (`1` for the pattern `1.0`, else `2 ^ alpha_log2`); before
  `alpha` is computed, the number of the word `0` the register starts with. -/
  alr : ℝ := 0
  /-- The 64 score words after the bias and the mask (`%r954 …` at pc 1838, in column order). -/
  fsv : Nat → { v : Value // v.bytes = 4 } := fun _ => ⟨b32 0, rfl⟩
  /-- The running minima of the alphas of the rescale test (`%r1075`, `%r1077`, `%r1079`,
  `%r1073`), and the word loaded from shared memory (`%r1081`). -/
  cm1 : Value := b32 0
  cm2 : Value := b32 0
  cm3 : Value := b32 0
  cm4 : Value := b32 0
  ld : Value := b32 0
  /-- The 64 words of `O` the rescale loaded (`%r1086 …`), as the load returned them (any
  values: the products by `alpha` fault where a word is no `f32` datum, `Sm.D.owOk`). -/
  ow : Nat → Value := fun _ => b32 0
  /-- The lane bits the broadcast of the warp index returned (`m % 4` where the received word
  reads as `m`: `shl.b32 %r484, %r483, 21`, `and.b32 %r45, %r484, 0x600000`), the lane field of
  the Tensor Memory addresses `%r45`, `%r1215`, `%r1150` in units of 32 lanes; 0 before the first
  broadcast. -/
  bw : Nat := 0
  /-- The stage's numbers are the real ones: every exchange of the row maximum so far received a
  score word and had score words (`Sm.next shfl5` took the score-word path). -/
  re : Bool := true
  /-- The 64 probability words as the registers hold them (`%r47 …` and the halves of `%rd46 …`),
  in tile order as `D.pf`. -/
  pv : Nat → Value := fun _ => .float .f32 0
  /-- The thread's sum of the probabilities as the register holds it (`%r1068`). -/
  sw : Value := .float .f32 0

/-- The state of a softmax thread: the next event, the entry numbers, the loop counter `i`, the
running maximum and sum, the bias words of the block in the registers (`w`: the words of
`%rs82 …`, packed in `%r1455 …`) and of the block being loaded (`v`: `%rs151 …`), and how many of
each group's words are loaded (`cw`, `cv`). -/
structure D where
  site : Site
  e : Ent
  i : Nat
  m : Value
  l : Value
  cw : Nat
  cv : Nat
  w : Nat → Value
  v : Nat → Value
  /-- The 64 words of the S tile the Tensor Memory load returned (`%r415 …`; the words before the
  load are not used). -/
  sv : Nat → { v : Value // v.bytes = 4 } := fun _ => ⟨b32 0, rfl⟩
  /-- The 64 probabilities `P` of the thread's columns of the tile as real numbers, in tile
  order (`2 k` and `2 k + 1` are the halves of the pair that is stored as word `k`). -/
  pf : Nat → ℝ := fun _ => 0
  /-- The numbers of the score stage that the tail of the loop reads. -/
  stg : Stg := {}

/-- The block number of the state's iteration. -/
abbrev D.n (d : D) : Nat := blkOf d.e d.i

/-- The zero half-word the masked loads leave in their destination. -/
abbrev z16 : Value := .bits 16 0

/-- The word `k` of the block in the registers: the loaded one, the zero half-word before it is
loaded. -/
abbrev D.wd (d : D) (k : Nat) : Value := if k < d.cw then d.w k else z16

/-- The word `k` of the block being loaded. -/
abbrev D.vd (d : D) (k : Nat) : Value := if k < d.cv then d.v k else z16

/-- The destination register of loop bias load `j` (pc `1124 + 2 j`): `%rs151`, then `%rs153 …`
(`%rs152` is the zero constant the destinations are first filled with). -/
abbrev nxtDst (j : Nat) : Nat := if j = 0 then 332 else 333 + j

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
