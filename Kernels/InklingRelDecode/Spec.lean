-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Kernels.InklingRelDecode.Data.Decoded
public import Kernels.InklingRelDecode.Data.TensorMaps

@[expose] public section

/-!
The Inkling 2 Small relative-attention decode kernel, `_rel_verify_kernel` of vLLM PR #67325
(`vllm/models/inkling2/ops/attention.py:852-1100`, commit
`d664cd1e96052857aea2aa844eeba571c24758b4`),
for the full-attention layer (`IS_LOCAL = False`), the gated-combine variant (`FUSE_GATE = False`,
`DRAFT = False`), with the compile-time configuration of `manifest.json`: 12 query heads over 2 KV
heads (group 6), head dimension 128, `BLOCK_M = 64`, `BLOCK_N = FA_BLOCK = 128`, `PAGE = 64`,
`REL = 1024`, `REL_PAD = 1280`, `STAGES = 3`. The batch, the number of splits, the token count, the
request lengths, the page table and all strides are symbolic.

One CTA `(split, kv_head, request)` handles the key blocks `split, split + num_splits, ...` of one
request for the 6 query heads of one KV head and up to 10 query tokens (`BLOCK_M // G` tokens, rows
`60..63` are padding). For its valid rows it stores the fp32 partial output `OPart` and the log2
normalizer `LsePart` of its blocks (`attention.py:843-849`); the combine kernel that merges the
splits is outside this kernel.

A key `k` of a request sees the logit `scale · (q · K_k)`, plus the relative logit
`rel[token, head, k - rel_base]` when `k` is in a block with relative logits (`n >= n_bias`,
`attention.py:776-778`), and is visible to token `tok` when `k <= past + tok`
(`attention.py:780-786`). The kernel exponentiates `x = fma(s, scale_log2, -(m · scale_log2))`
with `scale_log2 = softmax_scale * 0f3FB8AA3B` (the f32 constant nearest `log2 e`, PTX line 1233)
and `s = q · K + bias * (1 / softmax_scale)` (PTX lines 1229-1231), so the weight of a key is
`2 ^ (c · (scale · S + bias))` with `c` that constant. `Post` states exactly that with base-2
exponentials. Floating values denote exact reals under the kernel's assumptions
(`Assumptions.lean`). The precondition describes launch bindings, parameter bytes, input bytes and
available storage; the schedule, buffer ownership, synchronization and progress are proof
obligations.
-/

namespace PTX.Kernels.InklingRelDecode
open PTX TensorDescriptor
noncomputable section

/-- All 2856 decoded instructions of the frozen program. -/
def kernel : Kernel := Decoded.kernel

theorem kernel_code_length : kernel.code.length = 2856 := Decoded.code_length

theorem kernel_groupUniform : kernel.TcGroupUniform := by
  unfold Kernel.TcGroupUniform
  decide +kernel

/-- Bytes of the dynamic shared memory one CTA uses (`manifest.json`: `shared_bytes`). -/
def sharedBytes : Nat := 213340

/-- Query heads, KV heads, the group size, the head dimension and the relative-logit width: the
compile-time constants `H`, `HKV`, `G = H / HKV`, `D` and `REL_PAD` of the configuration. -/
def heads : Nat := 12
def kvHeads : Nat := 2
def group : Nat := 6
def headDim : Nat := 128
def relPad : Nat := 1280

/-- The name of parameter `param_i` of the entry. -/
def param (i : String) : String := kernel.name ++ "_param_" ++ i

/-- The tensor-map parameter object: `.param .align 64 .b8 name[128]`. -/
def mapParam : ParamObjectDecl := ⟨param "1", 8, 128, 64⟩

/-- The parameter declarations of the compiled PTX. `param_1` is the by-value tensor map. -/
theorem kernel_params : kernel.params =
    [(param "0", 64), (param "2", 32), (param "3", 32), (param "4", 64), (param "5", 64),
      (param "6", 64), (param "7", 64), (param "8", 64), (param "9", 64), (param "10", 64),
      (param "11", 64), (param "12", 64), (param "13", 64), (param "14", 64), (param "15", 32),
      (param "16", 32), (param "17", 32), (param "18", 32), (param "19", 32), (param "20", 32),
      (param "21", 32), (param "22", 32), (param "23", 32), (param "24", 32), (param "25", 32),
      (param "26", 64), (param "27", 64)] := by
  decide +kernel

theorem kernel_paramObjects : kernel.paramObjects = [mapParam] := by
  decide +kernel

theorem kernel_reqThreads : kernel.reqThreads = some (256, 1, 1) := by decide +kernel

/-- The f32 constant `0f3FB8AA3B`, the nearest f32 to `log2 e`, that the kernel multiplies the
softmax scale by. -/
def log2eF32 : ℝ := 12102203 / 8388608

theorem log2eF32_pattern : (f32Value 0x3FB8AA3B).map (fun x : ℚ => (x : ℝ)) = some log2eF32 := by
  have : f32Value 0x3FB8AA3B = some (12102203 / 8388608 : ℚ) := by decide +kernel
  simp [this, log2eF32]

/-- The kernel's symbolic parameters. `qStart r` is `cu_seqlens_q[r]` (`r ≤ b`), `seqK r` is
`seq_lens[r]` and `page r s` is `block_table[r][s]`. `q`, `rel` and `kv` are the values of the bf16
inputs: Q by `(token, head, d)`, the sheared relative logits by `(token, head, column)`, and the
paged cache by `(physical row, column)` of the `kv_rows` view. -/
structure Params where
  b : Nat
  splits : Nat
  nTok : Nat
  qStart : Nat → Nat
  seqK : Nat → Nat
  page : Nat → Nat → Nat
  /-- `page_rows`, `head_rows`, `head_cols` (`attention.py:1233-1240`), the row length
  `slot_stride` and the row count of the `kv_rows` view. -/
  pageRows : Nat
  headRows : Nat
  headCols : Nat
  slotStride : Nat
  rows : Nat
  /-- The element strides `stride_q_t`, `stride_rel_t` and `stride_bt`. -/
  strideQ : Nat
  strideRel : Nat
  strideBt : Nat
  /-- `softmax_scale`, as the exact value of its f32 pattern. -/
  scale : ℝ
  qBase : Nat
  relBase : Nat
  btBase : Nat
  seqBase : Nat
  cuBase : Nat
  oBase : Nat
  lseBase : Nat
  kvBase : Nat
  kvMap : Nat
  kvClass : AllocationClass
  q : Nat → Nat → Nat → ℝ
  rel : Nat → Nat → Nat → ℝ
  kv : Nat → Nat → ℝ

/-- `cu_seqlens_q[r + 1] - cu_seqlens_q[r]`, the query tokens of request `r`
(`attention.py:908-909`). -/
def Params.qLen (P : Params) (r : Nat) : Nat := P.qStart (r + 1) - P.qStart r

/-- `past = seqlen_k - q_len`, the position of request `r`'s first query
(`attention.py:911,917`). -/
def Params.past (P : Params) (r : Nat) : Nat := P.seqK r - P.qLen r

/-- The key blocks of request `r`: `cdiv(seqlen_k, 128)`. -/
def Params.blocks (P : Params) (r : Nat) : Nat := (P.seqK r + 127) / 128

/-- The first block with relative logits, `max(past - (REL - 1), 0) // BLOCK_N`
(`attention.py:918`; `REL = 1024`). -/
def Params.nBias (P : Params) (r : Nat) : Nat := (P.past r - 1023) / 128

/-- The number of blocks split `s` of request `r` processes,
`max(cdiv(cdiv(seqlen_k, BLOCK_N) - split, num_splits), 0)` (`attention.py:927`). -/
def Params.numIters (P : Params) (r s : Nat) : Nat :=
  (P.blocks r - s + (P.splits - 1)) / P.splits

/-- Key `k` is in a block of split `s` of request `r`: block `k / 128` is `s + i * num_splits`
for some `i < num_iters` (`attention.py:763`). -/
def Params.inSplit (P : Params) (r s k : Nat) : Prop :=
  s ≤ k / 128 ∧ (k / 128 - s) % P.splits = 0 ∧ k / 128 < P.blocks r

/-- Physical row of key `k` of request `r` for KV head `kvh`: the page its 64-key slab maps to
(`attention.py:572-573`). -/
def Params.kvRow (P : Params) (r kvh k : Nat) : Nat :=
  P.page r (k / 64) * P.pageRows + kvh * P.headRows + k % 64

/-- Element `d` of the K row (`attention.py:577`) and of the V row (`:578`, column `+ D`). -/
def Params.kVal (P : Params) (r kvh k d : Nat) : ℝ :=
  P.kv (P.kvRow r kvh k) (kvh * P.headCols + d)

def Params.vVal (P : Params) (r kvh k d : Nat) : ℝ :=
  P.kv (P.kvRow r kvh k) (kvh * P.headCols + headDim + d)

/-- The unscaled score `q · K` of query token `tok` of request `r`, head `head`, with key `k`. -/
def score (P : Params) (r tok head k : Nat) : ℝ :=
  ∑ d ∈ Finset.range headDim,
    P.q (P.qStart r + tok) head d * P.kVal r (head / group) k d

/-- The relative-logit column of key `k` of request `r`: `k - rel_base` with
`rel_base = cdiv(seqlen_k, 128) * 128 - REL_PAD` (`attention.py:926`). -/
def relCol (P : Params) (r k : Nat) : Int := (k : Int) - (P.blocks r * 128 : Nat) + relPad

/-- The relative logit added to key `k`: zero before the first block with relative logits. -/
def bias (P : Params) (r tok head k : Nat) : ℝ :=
  if P.nBias r * 128 ≤ k then P.rel (P.qStart r + tok) head (relCol P r k).toNat else 0

/-- The unnormalized weight of key `k`: `2 ^ (c · (scale · S + bias))`. -/
def weight (P : Params) (r tok head k : Nat) : ℝ :=
  (2 : ℝ) ^ (log2eF32 * (P.scale * score P r tok head k + bias P r tok head k))

open Classical in
/-- The keys split `s` of request `r` gives weight to for query token `tok`: keys of its blocks
that the token sees, `k <= past + tok` (`attention.py:781-786`). -/
def keys (P : Params) (r s tok : Nat) : Finset Nat :=
  (Finset.range (P.blocks r * 128)).filter fun k => P.inSplit r s k ∧ k ≤ P.past r + tok

/-- The row sum of the weights and the numerator of dimension `d`. -/
def rowSum (P : Params) (r s tok head : Nat) : ℝ :=
  ∑ k ∈ keys P r s tok, weight P r tok head k

def numerator (P : Params) (r s tok head d : Nat) : ℝ :=
  ∑ k ∈ keys P r s tok, weight P r tok head k * P.vVal r (head / group) k d

/-- The normalized partial output: zero for a row with no visible key. -/
def oPart (P : Params) (r s tok head d : Nat) : ℝ :=
  if rowSum P r s tok head = 0 then 0 else numerator P r s tok head d / rowSum P r s tok head

/-- The log2 normalizer of a non-empty row. -/
def lsePart (P : Params) (r s tok head : Nat) : ℝ := Real.logb 2 (rowSum P r s tok head)

/-- The `f32` location of `OPart[split, token, head, d]` and `LsePart[split, token, head]`
(`attention.py:844-848`). -/
def oLoc (P : Params) (s t h d : Nat) : Loc :=
  ⟨.global, 0, P.oBase + 4 * (((s * P.nTok + t) * heads + h) * headDim + d)⟩

def lseLoc (P : Params) (s t h : Nat) : Loc :=
  ⟨.global, 0, P.lseBase + 4 * ((s * P.nTok + t) * heads + h)⟩

/-- Bytes of `OPart` and `LsePart`. -/
def oBytes (P : Params) : Nat := 4 * P.splits * P.nTok * heads * headDim
def lseBytes (P : Params) : Nat := 4 * P.splits * P.nTok * heads

/-- Byte `k` of the f32 `-inf` pattern an empty row stores as its normalizer. -/
def negInfByte (k : Nat) : Byte := ((FVal.inf true).toValue .f32).byteAt k

/-- Two byte ranges `[a, a + n)` and `[b, b + m)` do not overlap. -/
def Apart (a n b m : Nat) : Prop := a + n ≤ b ∨ b + m ≤ a

/-- Byte `k` of the little-endian 32-bit integer `x` as a stored value. -/
def i32Byte (x k : Nat) : Byte := (Value.bits 32 (BitVec.ofNat 64 x)).byteAt k

/-- The global byte addresses the kernel reads as inputs: the masked Q rows of the valid tokens,
the relative-logit rows, the K and V columns of every slab it loads, `cu_seqlens_q`, `seq_lens`
and the block-table entries of every slab. -/
def Params.reads (P : Params) (a : Nat) : Prop :=
  (∃ r < P.b, ∃ tok < P.qLen r, ∃ head < heads, ∃ d < headDim, ∃ byte < 2,
    a = P.qBase + 2 * ((P.qStart r + tok) * P.strideQ + head * headDim + d) + byte) ∨
  (∃ r < P.b, ∃ tok < P.qLen r, ∃ head < heads, ∃ c < relPad, ∃ byte < 2,
    a = P.relBase + 2 * ((P.qStart r + tok) * P.strideRel + head * relPad + c) + byte) ∨
  (∃ r < P.b, ∃ s < 2 * P.blocks r, ∃ kvh < kvHeads, ∃ i < 64, ∃ c < 2 * headDim, ∃ byte < 2,
    a = P.kvBase + 2 * ((P.page r s * P.pageRows + kvh * P.headRows + i) * P.slotStride +
      kvh * P.headCols + c) + byte) ∨
  (∃ r ≤ P.b, ∃ k < 4, a = P.cuBase + 4 * r + k) ∨
  (∃ r < P.b, ∃ k < 4, a = P.seqBase + 4 * r + k) ∨
  (∃ r < P.b, ∃ s < 2 * P.blocks r, ∃ k < 4, a = P.btBase + 4 * (r * P.strideBt + s) + k)

/-- The initial launch and memory requirements, without execution or protocol assumptions. -/
structure Pre (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  /-- The launch is the kernel's: grid `(num_splits, 2, b)`, block `(256, 1, 1)`, no cluster
  (`attention.py:1222`, `manifest.json`: `launch`). -/
  gridShape : L.nctaid = ⟨P.splits, kvHeads, P.b⟩
  grid : L.grid = P.splits * kvHeads * P.b
  block : L.block = 256
  ntid : L.ntid = ⟨256, 1, 1⟩
  clusterSize : L.clusterSize.val = 1
  clusterNctaid : L.clusterNctaid = ⟨1, 1, 1⟩
  preferredNctaid : L.preferredNctaid = ⟨1, 1, 1⟩
  nclusters : L.nclusters = L.grid
  clusterPlaces : L.clusterPlaces = ClusterPlace.uniform L.nctaid L.clusterNctaid
  launchValid : L.Valid kernel
  /-- Shape ranges: CUDA's grid limits, and the 32-bit arithmetic of the kernel. -/
  bPos : 0 < P.b
  bRange : P.b < 2 ^ 16
  splitsPos : 0 < P.splits
  /-- The numerators of the kernel's signed divisions by `num_splits`
  (`gl.cdiv(cdiv(seqlen_k, 128) - n_first, num_splits)`, `attention.py:927,972`) are
  `num_splits - 1 - split + blocks`: they stay below `2 ^ 31` since `blocks ≤ 2 ^ 24`. -/
  splitsRange : P.splits + 2 ^ 24 < 2 ^ 31
  nTokRange : P.nTok < 2 ^ 31
  /-- A launch has at least one token (`num_tokens`, `attention.py:1207`). -/
  nTokPos : 0 < P.nTok
  /-- The scalar parameters read as `u32` words (`param_16..18, 21..23`) are non-negative
  `int32` values: the kernel's index arithmetic on them is signed 32-bit. -/
  scalarsRange : P.strideQ < 2 ^ 31 ∧ P.strideRel < 2 ^ 31 ∧ P.strideBt < 2 ^ 31 ∧
    P.pageRows < 2 ^ 31 ∧ P.headRows < 2 ^ 31 ∧ P.headCols < 2 ^ 31
  /-- The requests' tokens are consecutive and fit the token count; a request has at most
  `BLOCK_M // G = 10` tokens and at most `seqlen_k` of them (`attention.py:1218`, `:911`). -/
  cuMono : ∀ r < P.b, P.qStart r ≤ P.qStart (r + 1)
  cuEnd : P.qStart P.b ≤ P.nTok
  qLenLe : ∀ r < P.b, P.qLen r ≤ 10
  qLenSeq : ∀ r < P.b, P.qLen r ≤ P.seqK r
  /-- `seqlen_k` leaves room for the block arithmetic: `128 · num_iters + 256` and
  `past + 128` stay below `2 ^ 31` (the score stage's 32-bit key and position sums). -/
  seqRange : ∀ r < P.b, P.seqK r + 511 < 2 ^ 31
  /-- 32-bit arithmetic of the kernel: the block-table index `req * stride_bt + slab`, the output
  row index `(split * num_tokens + token) * H + head` times `D` (`attention.py:844-848`), and the
  element strides of Q and the relative logits (64-bit pointer arithmetic, `token` is `int64`). -/
  btIndexRange : ∀ r < P.b, ∀ s < 2 * P.blocks r, r * P.strideBt + s < 2 ^ 31
  outRange : P.splits * P.nTok * heads * headDim < 2 ^ 31
  /-- The padding rows of a CTA (token index up to `q_len ≤ 10` past the last token) also compute
  an output row index; it stays below `2 ^ 24` too (`attention.py:844`: the index is computed for
  every row, the stores are masked). The last request can start at token `num_tokens` and a
  padding row has a token up to 10 with head up to 11, so the largest index is
  `(splits * num_tokens + 10) * 12 + 11 < (splits * num_tokens + 11) * 12`. -/
  outRangeSlack : (P.splits * P.nTok + 11) * heads * headDim ≤ 2 ^ 31
  strideQRange : headDim * heads ≤ P.strideQ ∧ P.nTok * P.strideQ < 2 ^ 40
  strideRelRange : relPad * heads ≤ P.strideRel ∧ P.nTok * P.strideRel < 2 ^ 40
  /-- The scalar parameters the kernel reads: pointers (`param_0, 6..11`), the f32
  `softmax_scale` (`param_15`) and the u32 strides, row counts, `num_splits` and `num_tokens`
  (`param_16..18, 21..25`). `Audit/ParamReads.lean` checks the list against the program. -/
  paramQ : L.params (param "0") = some (BitVec.ofNat 64 P.qBase)
  paramRel : L.params (param "6") = some (BitVec.ofNat 64 P.relBase)
  paramBt : L.params (param "7") = some (BitVec.ofNat 64 P.btBase)
  paramSeq : L.params (param "8") = some (BitVec.ofNat 64 P.seqBase)
  paramCu : L.params (param "9") = some (BitVec.ofNat 64 P.cuBase)
  paramO : L.params (param "10") = some (BitVec.ofNat 64 P.oBase)
  paramLse : L.params (param "11") = some (BitVec.ofNat 64 P.lseBase)
  paramScale : ∃ bits < 2 ^ 32, L.params (param "15") = some (BitVec.ofNat 64 bits) ∧
    (f32Value bits).map (fun x : ℚ => (x : ℝ)) = some P.scale
  paramStrideQ : L.params (param "16") = some (BitVec.ofNat 64 P.strideQ)
  paramStrideRel : L.params (param "17") = some (BitVec.ofNat 64 P.strideRel)
  paramStrideBt : L.params (param "18") = some (BitVec.ofNat 64 P.strideBt)
  paramPageRows : L.params (param "21") = some (BitVec.ofNat 64 P.pageRows)
  paramHeadRows : L.params (param "22") = some (BitVec.ofNat 64 P.headRows)
  paramHeadCols : L.params (param "23") = some (BitVec.ofNat 64 P.headCols)
  paramSplits : L.params (param "24") = some (BitVec.ofNat 64 P.splits)
  paramNTok : L.params (param "25") = some (BitVec.ofNat 64 P.nTok)
  /-- `softmax_scale` is a positive finite f32 (the combine of the logits divides by it). -/
  scalePos : 0 < P.scale
  /-- The tensor map `kv_desc`, published at the address of `param_1`. -/
  paramKv : L.paramObjects (param "1") = some (mapParam, P.kvMap)
  mapAlignment : P.kvMap % 64 = 0
  mapRange : P.kvMap + 128 ≤ 2 ^ 64
  mapKvBind : L.tensorMaps P.kvMap =
    some ⟨1, mapKv P.kvBase P.slotStride P.rows P.kvClass⟩
  /-- The cache view: a 16-byte aligned base, rows of whole 16-byte units, and every box the
  kernel issues lies inside it (no out-of-bounds fill is relied on, `attention.py:1241-1247`). -/
  kvAlign : P.kvBase % 16 = 0
  slotStridePos : 0 < P.slotStride
  slotStrideAlign : P.slotStride % 8 = 0
  slotStrideRange : P.slotStride ≤ 2 ^ 31
  rowsPos : 0 < P.rows
  rowsRange : P.rows ≤ 2 ^ 31
  kvRange : P.kvBase + 2 * P.rows * P.slotStride ≤ 2 ^ 64
  pageRowsPos : 0 < P.pageRows
  headColsAlign : P.headCols % 8 = 0
  kvCols : ∀ kvh < kvHeads, kvh * P.headCols + 2 * headDim ≤ P.slotStride
  slabInside : ∀ r < P.b, ∀ s < 2 * P.blocks r, ∀ kvh < kvHeads,
    P.page r s * P.pageRows + kvh * P.headRows + 64 ≤ P.rows
  /-- The inputs are bf16 values in memory. Q: the masked rows of the valid tokens. The relative
  logits: the whole `REL_PAD`-wide row of every valid token and head. The cache: the K and V
  columns of every slab the kernel loads, including the rows past `seqlen_k` of the last block. -/
  qInput : ∀ r < P.b, ∀ tok < P.qLen r, ∀ head < heads, ∀ d < headDim, ∀ byte < 2,
    mem0 ⟨.global, 0, P.qBase + 2 * ((P.qStart r + tok) * P.strideQ + head * headDim + d) + byte⟩ =
      some (some ((Value.float .bf16 (P.q (P.qStart r + tok) head d)).byteAt byte))
  relInput : ∀ r < P.b, ∀ tok < P.qLen r, ∀ head < heads, ∀ c < relPad, ∀ byte < 2,
    mem0 ⟨.global, 0,
        P.relBase + 2 * ((P.qStart r + tok) * P.strideRel + head * relPad + c) + byte⟩ =
      some (some ((Value.float .bf16 (P.rel (P.qStart r + tok) head c)).byteAt byte))
  kvInput : ∀ r < P.b, ∀ s < 2 * P.blocks r, ∀ kvh < kvHeads, ∀ i < 64, ∀ c < 2 * headDim,
    ∀ byte < 2,
    mem0 ⟨.global, 0, P.kvBase + 2 * ((P.page r s * P.pageRows + kvh * P.headRows + i) *
        P.slotStride + kvh * P.headCols + c) + byte⟩ =
      some (some ((Value.float .bf16 (P.kv (P.page r s * P.pageRows + kvh * P.headRows + i)
        (kvh * P.headCols + c))).byteAt byte))
  /-- The integer arrays: `cu_seqlens_q` (`b + 1` entries), `seq_lens` and the block table. -/
  cuInput : ∀ r ≤ P.b, ∀ k < 4,
    mem0 ⟨.global, 0, P.cuBase + 4 * r + k⟩ = some (some (i32Byte (P.qStart r) k))
  seqInput : ∀ r < P.b, ∀ k < 4,
    mem0 ⟨.global, 0, P.seqBase + 4 * r + k⟩ = some (some (i32Byte (P.seqK r) k))
  btInput : ∀ r < P.b, ∀ s < 2 * P.blocks r, ∀ k < 4,
    mem0 ⟨.global, 0, P.btBase + 4 * (r * P.strideBt + s) + k⟩ =
      some (some (i32Byte (P.page r s) k))
  cuAlign : P.cuBase % 4 = 0
  seqAlign : P.seqBase % 4 = 0
  btAlign : P.btBase % 4 = 0
  qAlign : P.qBase % 2 = 0
  relAlign : P.relBase % 2 = 0
  /-- The outputs are allocated and disjoint from each other and from every input. -/
  oAllocated : ∀ byte < oBytes P, mem0 ⟨.global, 0, P.oBase + byte⟩ ≠ none
  lseAllocated : ∀ byte < lseBytes P, mem0 ⟨.global, 0, P.lseBase + byte⟩ ≠ none
  oAlign : P.oBase % 4 = 0
  lseAlign : P.lseBase % 4 = 0
  oRange : P.oBase + oBytes P ≤ 2 ^ 64
  lseRange : P.lseBase + lseBytes P ≤ 2 ^ 64
  oApartLse : Apart P.oBase (oBytes P) P.lseBase (lseBytes P)
  /-- No address the kernel reads wraps past `2 ^ 64`: the global addresses of the input
  loads are the exact sums, not the modular ones. -/
  readsRange : ∀ a, P.reads a → a < 2 ^ 64
  outputsApart : ∀ a, P.reads a →
    ¬ (P.oBase ≤ a ∧ a < P.oBase + oBytes P) ∧ ¬ (P.lseBase ≤ a ∧ a < P.lseBase + lseBytes P)
  /-- The shared-memory window. -/
  sharedAlignment : L.sharedBase % 1024 = 0
  sharedRange : L.sharedBase + sharedBytes ≤ 2 ^ 18
  sharedAllocated : ∀ cta < L.grid, ∀ byte < sharedBytes,
    mem0 ⟨.shared, cta, L.sharedBase + byte⟩ ≠ none

/-- Complete ideal output of the kernel: for every request, split, valid token and query head,
element `d` of `OPart` is the normalized weighted value sum of the split's visible keys, read as
`f32`; the normalizer `LsePart` is `log2` of the row sum for a non-empty row and the `-inf`
pattern for an empty one; every global byte outside the two output arrays is preserved. Rows the
kernel masks out (padding rows, tokens past `q_len`) are not written and unconstrained. -/
def Post (P : Params) (mem0 : Mem0) (m : FinalMem) : Prop :=
  (∀ r < P.b, ∀ s < P.splits, ∀ tok < P.qLen r, ∀ head < heads, ∀ d < headDim,
    memFloat .f32 m (oLoc P s (P.qStart r + tok) head d) = .ok (oPart P r s tok head d)) ∧
  (∀ r < P.b, ∀ s < P.splits, ∀ tok < P.qLen r, ∀ head < heads,
    rowSum P r s tok head ≠ 0 →
    memFloat .f32 m (lseLoc P s (P.qStart r + tok) head) = .ok (lsePart P r s tok head)) ∧
  (∀ r < P.b, ∀ s < P.splits, ∀ tok < P.qLen r, ∀ head < heads,
    rowSum P r s tok head = 0 →
    ∀ k < 4, m ((lseLoc P s (P.qStart r + tok) head).at k) = some (some (negInfByte k))) ∧
  ∀ l, l.space = .global →
    ¬ (P.oBase ≤ l.addr ∧ l.addr < P.oBase + oBytes P) →
    ¬ (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P) → m l = mem0 l

end
end PTX.Kernels.InklingRelDecode
