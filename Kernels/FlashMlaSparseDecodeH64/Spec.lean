-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Kernels.FlashMlaSparseDecodeH64.Data.Decoded
public import Kernels.FlashMlaSparseDecodeH64.Data.Indices
public import Kernels.FlashMlaSparseDecodeH64.Data.Params
public import Kernels.FlashMlaSparseDecodeH64.Data.TensorMaps

@[expose] public section

/-!
The FlashMLA SM100 sparse decode kernel, head64, no split-KV (`v41_h64_no_split`), for a symbolic
batch, query count, sparse budget and paged KV cache.

Each CTA handles one `(query position, batch)` pair: `grid = (s_q, b, 1)`, `block = (384, 1, 1)`.
The kernel reads the top-k indices of the query row, gathers four KV rows at a time from the paged
e4m3 cache (528 bytes per token: 512 values and 16 ue8m0 scales), dequantizes them to bf16 and
computes `O = softmax(scale · Q Kᵀ) V` over the valid slots with `tcgen05.mma.ws`; `scale` is the
kernel's `sm_scale_div_log2`, so the exponentials are base 2. An optional per-head sink adds
`2 ^ (sink h * sinkLog2Factor)` to the denominator. `lse` is the base-two row sum logarithm
scaled by the compiled change-of-base constant. `Post` states exactly that and
nothing about `e`.

Floating values denote exact reals under the kernel's assumptions (`Assumptions.lean`); the
precondition describes launch bindings, parameter bytes, input bytes and available storage. The
schedule, buffer ownership, synchronization and progress are proof obligations.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64
open PTX TensorDescriptor
noncomputable section

/-- All 3612 decoded instructions of the frozen program. -/
def kernel : Kernel := Decoded.kernel

theorem kernel_code_length : kernel.code.length = 3612 := Decoded.code_length

theorem kernel_groupUniform : kernel.TcGroupUniform := by
  unfold Kernel.TcGroupUniform
  decide +kernel

/-- Bytes of the dynamic shared memory one CTA uses: `sizeof(SharedMemoryPlan)`. The kernel
addresses 222952 of them. -/
def sharedBytes : Nat := 223232

/-- The name of parameter `param_i` of the entry. -/
def param (i : String) : String := kernel.name ++ "_param_" ++ i

/-- The tensor-map parameter object: `.param .align 128 .b8 name[1024]`, eight 128-byte
descriptors (Q at `+128`, O at `+512`, KV at `+768`, extra KV at `+896`). -/
def mapParam : ParamObjectDecl := ⟨param "1", 8, 1024, 128⟩

/-- The scalar parameter object: `.param .align 8 .b8 name[304]`. -/
def scalarsParam : ParamObjectDecl := ⟨param "0", 8, 304, 8⟩

/-- The parameter declarations of the compiled PTX: the two by-value objects. -/
theorem kernel_params : kernel.params = [] := by
  decide +kernel

theorem kernel_paramObjects : kernel.paramObjects = [scalarsParam, mapParam] := by
  decide +kernel

theorem kernel_maxThreads : kernel.maxThreads = some 384 := by decide +kernel

/-- The kernel's symbolic parameters. `topkLen`/`extraTopkLen` are the actual per-batch lengths
(`topk`/`extra_topk` when the length pointer is null); `sink h` is the per-head sink, `none` when
the sink pointer is null. `extra_topk = 0` turns the extra cache off. -/
structure Params where
  b : Nat
  s_q : Nat
  topk : Nat
  extra_topk : Nat
  /-- Tokens per page block in the two caches. -/
  page : Nat
  extraPage : Nat
  /-- Physical blocks of the two caches. -/
  numBlocks : Nat
  extraNumBlocks : Nat
  /-- Bytes per physical block of the two caches; a multiple of 528. -/
  blockStride : Nat
  extraBlockStride : Nat
  /-- Actual valid lengths of the sparse index rows. -/
  topkLen : Nat → Nat
  extraTopkLen : Nat → Nat
  /-- Sparse indices, by `(batch, query, slot)`; `-1` is the invalid marker. -/
  idx : Nat → Nat → Nat → Int
  extraIdx : Nat → Nat → Nat → Int
  /-- Q values by `(batch, query, head, head-dimension index)`. -/
  q : Nat → Nat → Nat → Nat → ℝ
  /-- The raw bytes of the two caches, by `(physical row, byte)`. -/
  kvByte : Nat → Nat → Fin 256
  extraKvByte : Nat → Nat → Fin 256
  /-- The kernel's `sm_scale_div_log2`, as the exact value of its f32 pattern. -/
  scale : ℝ
  /-- The optional per-head sink, as the exact value of its f32 pattern. -/
  sink : Nat → Option ℝ
  /-- The bases of the two by-value parameter objects. -/
  param0Base : Nat
  param1Base : Nat
  /-- Global bases of the input and output tensors and the two caches. -/
  qBase : Nat
  outBase : Nat
  lseBase : Nat
  kvBase : Nat
  extraKvBase : Nat
  indicesBase : Nat
  extraIndicesBase : Nat
  /-- Bases of the optional length and sink arrays. -/
  topkLenBase : Option Nat
  extraTopkLenBase : Option Nat
  sinkBase : Option Nat
  /-- Allocation classes of the four tensor maps. -/
  qClass : AllocationClass
  oClass : AllocationClass
  kvClass : AllocationClass
  extraKvClass : AllocationClass
  sharedBase : Nat

/-- The 32-bit pattern of the signed integer `z`. -/
def i32Bits (z : Int) : Nat := (z % 2 ^ 32).toNat

/-- A byte of a little-endian 32-bit value in global memory. -/
def word32Byte (x k : Nat) : Byte := (Value.bits 32 (BitVec.ofNat 64 x)).byteAt k

/-- A 32-bit integer field of a by-value parameter object: four little-endian bytes. -/
def intBytes (x off : Nat) (p : String) (L : Launch) : Prop :=
  ∀ k < 4, L.paramBytes p (off + k) = some (leByte x k)

/-- A pointer field of a by-value parameter object, zero for the null pointer. -/
def ptrBytes (x off : Nat) (p : String) (L : Launch) : Prop :=
  ∀ k < 8, L.paramBytes p (off + k) = some (leByte x k)

/-- A float field of a by-value parameter object: the four bytes of the pattern `bits`, whose
value is `x`. -/
def floatBytes (bits : Nat) (x : ℝ) (off : Nat) (p : String) (L : Launch) : Prop :=
  (∀ k < 4, L.paramBytes p (off + k) = some (leByte bits k)) ∧
    (f32Value bits).map (fun q : ℚ => (q : ℝ)) = some x

/-- Two byte ranges with their respective lengths do not overlap. -/
def Apart (an bn a b : Nat) : Prop := a + an ≤ b ∨ b + bn ≤ a

/-- A present optional array has a nonzero, aligned address and fits in the address space. -/
def OptionalGlobalRange (base : Option Nat) (bytes : Nat) : Prop :=
  ∀ x, base = some x → 0 < x ∧ x % 4 = 0 ∧ x + bytes ≤ 2 ^ 64

/-- The byte range of a present optional array is disjoint from an output range. -/
def OptionalApart (base : Option Nat) (n out outBytes : Nat) : Prop :=
  ∀ x, base = some x → Apart n outBytes x out

/-- The cluster placement of a `(s_q, b, 1)` grid of single-CTA clusters: CTA `k` has
`%ctaid = (k % s_q, k / s_q % b, 0)`. This is CUDA's linear block order, `x` varying fastest;
`ClusterPlace.uniform` linearizes cluster identifiers with `z` fastest, which for single-CTA
clusters would swap the roles of `%ctaid.x` and `%ctaid.y`. -/
def gridPlace (s_q b : Nat) : Nat → ClusterPlace := fun k =>
  let p : Dim3 := ⟨k % s_q, k / s_q % b, 0⟩
  ⟨p, ⟨1, 1, 1⟩, p, ⟨s_q, b, 1⟩⟩

/-- The value of an e4m3 byte (e4m3fn: sign, 4-bit exponent with bias 7, 3-bit mantissa;
`0x7f` and `0xff` are NaN). The kernel's input premise excludes the NaN patterns. -/
def e4m3Val (b : Nat) : ℝ :=
  let s : ℝ := if b / 128 = 1 then -1 else 1
  let e := b / 8 % 16
  let m := b % 8
  if e = 0 then s * (m / 8 : ℝ) * (2 : ℝ) ^ (-6 : ℤ)
  else s * (1 + (m / 8 : ℝ)) * (2 : ℝ) ^ ((e : ℤ) - 7)

/-- The value of a ue8m0 scale byte: `2^(b-127)` for `b ≤ 254` (CUDA 13.2 reads pattern `0` as
`2^-127`; PTX leaves it without a value, see assumption A4). Pattern `0xff` is NaN and the input
premise excludes it. -/
def ue8m0Val (b : Nat) : ℝ := (2 : ℝ) ^ ((b : ℤ) - 127)

/-- The dequantized value of dimension `t` of a cache row whose 528 bytes are `row`. -/
def dequant (row : Nat → Nat) (t : Nat) : ℝ :=
  e4m3Val (row t) * ue8m0Val (row (512 + t / 32))

/-- Bytes of the contiguous `(b, s_q, 64, 512)` bf16 output tensor. -/
def tensorBytes (P : Params) : Nat := 2 * P.b * P.s_q * 64 * 512

/-- Bytes of the contiguous `(b, s_q, 64)` f32 LSE tensor. -/
def lseBytes (P : Params) : Nat := 4 * P.b * P.s_q * 64

/-- Bytes of the concatenated 528-byte rows of a cache map. -/
def cacheBytes (numBlocks blockStride : Nat) : Nat := numBlocks * blockStride

/-- The valid slots of a query row: position `j` of cache `extra` is valid when it is within the
cache's actual length and its index is not the `-1` marker. The kernel processes a padded block
count, but only these slots receive a weight. -/
def slotValid (P : Params) (e q : Nat) (extra : Bool) (j : Nat) : Prop :=
  j < (if extra then P.extraTopkLen e else P.topkLen e) ∧
    (if extra then P.extraIdx e q j else P.idx e q j) ≠ -1

instance slotValidDecidable (P : Params) (e q : Nat) (extra : Bool) (j : Nat) :
    Decidable (slotValid P e q extra j) := by
  unfold slotValid
  infer_instance

/-- The physical row of a valid index in a cache with `page` tokens per block and `blockStride`
bytes per block. -/
def tokenRow (page blockStride : Nat) (idx : Int) : Nat :=
  (idx.toNat / page) * (blockStride / 528) + idx.toNat % page

/-- The raw bytes of the row a slot selects. -/
def rowBytes (P : Params) (e q : Nat) (extra : Bool) (j : Nat) : Nat → Nat :=
  fun byte => if extra then
    (P.extraKvByte (tokenRow P.extraPage P.extraBlockStride (P.extraIdx e q j)) byte).val
  else
    (P.kvByte (tokenRow P.page P.blockStride (P.idx e q j)) byte).val

/-- The value of dimension `t` of the row a slot selects. -/
def slotValue (P : Params) (e q : Nat) (extra : Bool) (j t : Nat) : ℝ :=
  dequant (rowBytes P e q extra j) t

/-- The sparse QK score of a slot: `Σ_t Q · D`. -/
def score (P : Params) (e q h : Nat) (extra : Bool) (j : Nat) : ℝ :=
  ∑ t ∈ Finset.range 512, P.q e q h t * slotValue P e q extra j t

/-- The unnormalized base-2 weight of a slot. -/
def weight (P : Params) (e q h : Nat) (extra : Bool) (j : Nat) : ℝ :=
  if slotValid P e q extra j then (2 : ℝ) ^ (P.scale * score P e q h extra j) else 0

/-- The row sum `Z_e,q,h` of the weights. -/
def rowSum (P : Params) (e q h : Nat) : ℝ :=
  (∑ j ∈ Finset.range P.topk, weight P e q h false j) +
    ∑ j ∈ Finset.range P.extra_topk, weight P e q h true j

/-- The numerator `Σ_j w_j V_j` of dimension `d`. -/
def numerator (P : Params) (e q h d : Nat) : ℝ :=
  (∑ j ∈ Finset.range P.topk, weight P e q h false j * slotValue P e q false j d) +
    ∑ j ∈ Finset.range P.extra_topk, weight P e q h true j * slotValue P e q true j d

/-- The exact real value of the binary32 multiplier for the sink, `0x3FB8AA3B`. -/
def sinkLog2Factor : ℝ := 12102203 / 8388608

/-- The exact real value of the binary32 multiplier for the LSE, `0x3F317218`. -/
def lseLog2Factor : ℝ := 1453635 / 2097152

/-- The sink's contribution to the denominator, or zero without a sink. -/
def sinkWeight (P : Params) (h : Nat) : ℝ :=
  match P.sink h with
  | some s => (2 : ℝ) ^ (s * sinkLog2Factor)
  | none => 0

/-- The attention output of one element. -/
def attn (P : Params) (e q h d : Nat) : ℝ :=
  if rowSum P e q h = 0 then 0 else numerator P e q h d / (rowSum P e q h + sinkWeight P h)

/-- The log-base-two row sum scaled by the PTX's f32 change-of-base constant. -/
def lse (P : Params) (e q h : Nat) : ℝ :=
  lseLog2Factor * (Real.log (rowSum P e q h) / Real.log 2)

/-- The global location of output element `(batch, query, head, d)`. -/
def oLoc (P : Params) (e q h d : Nat) : Loc :=
  ⟨.global, 0, P.outBase + 2 * (((e * P.s_q + q) * 64 + h) * 512 + d)⟩

/-- The global location of LSE element `(batch, query, head)`. -/
def lseLoc (P : Params) (e q h : Nat) : Loc :=
  ⟨.global, 0, P.lseBase + 4 * ((e * P.s_q + q) * 64 + h)⟩

/-- Byte `k` of the f32 `+inf` pattern that an empty row writes as its LSE. -/
def infByte (k : Nat) : Byte := ((FVal.inf false).toValue .f32).byteAt k

/-- The initial launch and memory requirements, without execution or protocol assumptions. -/
structure Pre (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  /-- The launch is the kernel's: grid `(s_q, b, 1)`, block `(384, 1, 1)`, cluster
  `(1, 1, 1)`. -/
  gridShape : L.nctaid = ⟨P.s_q, P.b, 1⟩
  grid : L.grid = P.s_q * P.b
  block : L.block = 384
  ntid : L.ntid = ⟨384, 1, 1⟩
  clusterSize : L.clusterSize.val = 1
  clusterNctaid : L.clusterNctaid = ⟨1, 1, 1⟩
  preferredNctaid : L.preferredNctaid = ⟨1, 1, 1⟩
  nclusters : L.nclusters = L.grid
  clusterPlaces : L.clusterPlaces = gridPlace P.s_q P.b
  launchValid : L.Valid kernel
  /-- Shape and sparse-budget constraints of the no-split instance. -/
  bPos : 0 < P.b
  /-- The host's `b` is an `int`, and the kernel compares it with the signed `%ctaid.y`. -/
  bLt : P.b < 2 ^ 31
  sqPos : 0 < P.s_q
  sqLt : P.s_q < 2 ^ 31
  topkPos : 0 < P.topk
  topkDiv64 : P.topk % 64 = 0
  extraDiv64 : P.extra_topk % 64 = 0
  /-- Every row's combined padded token count fits the signed loop arithmetic. -/
  paddedRange : ∀ e < P.b,
    origPadded (P.topkLen e) + ceilToMultiple (P.extraTopkLen e) topkBlock < 2 ^ 31
  scalePos : 0 < P.scale
  numBlocksPos : 0 < P.numBlocks
  pagePos : 0 < P.page
  blockStrideMod : P.blockStride % 528 = 0
  pageFits : P.page * 528 ≤ P.blockStride
  extraPos : 0 < P.extra_topk →
    0 < P.extraPage ∧ 0 < P.extraNumBlocks ∧ P.extraBlockStride % 528 = 0 ∧
      P.extraPage * 528 ≤ P.extraBlockStride
  /-- Integer and TMA coordinate ranges. -/
  topkRange : P.s_q * P.topk < 2 ^ 31
  extraTopkRange : P.s_q * P.extra_topk < 2 ^ 31
  /-- The main index batch offset uses a 32-bit product followed by sign extension. -/
  indicesRange : (P.b - 1) * (P.s_q * P.topk) < 2 ^ 31
  blockStrideRange : P.blockStride < 2 ^ 31
  extraBlockStrideRange : P.extraBlockStride < 2 ^ 31
  rowsRange : P.numBlocks * (P.blockStride / 528) < 2 ^ 31
  extraRowsRange : P.extraNumBlocks * (P.extraBlockStride / 528) < 2 ^ 31
  qAlign : P.qBase % 16 = 0
  outAlign : P.outBase % 16 = 0
  kvAlign : P.kvBase % 16 = 0
  extraKvAlign : P.extraKvBase % 16 = 0
  qoBatchStrideRange : 32768 * P.s_q < 2 ^ 31
  tensorRange : P.qBase + tensorBytes P ≤ 2 ^ 64 ∧
    P.outBase + tensorBytes P ≤ 2 ^ 64 ∧ P.lseBase + lseBytes P ≤ 2 ^ 64
  cacheRange : P.kvBase + cacheBytes P.numBlocks P.blockStride ≤ 2 ^ 64 ∧
    P.extraKvBase + cacheBytes P.extraNumBlocks P.extraBlockStride ≤ 2 ^ 64
  /-- The two by-value parameter objects: independent storage, declared alignments, read-only. -/
  param0Object : L.paramObjects (param "0") = some (scalarsParam, P.param0Base)
  param1Object : L.paramObjects (param "1") = some (mapParam, P.param1Base)
  /-- The 1024-byte tensor-map object fits the 64-bit address space, so the parameter-pointer
  arithmetic's truncation is the identity. -/
  param1Range : P.param1Base + 1024 ≤ 2 ^ 64
  param0Align : P.param0Base % 8 = 0
  param1Align : P.param1Base % 128 = 0
  param0Range : P.param0Base + 304 ≤ 2 ^ 64
  paramApart : Apart 304 1024 P.param0Base P.param1Base
  /-- The scalar parameter bytes the kernel reads. Offsets are `SparseAttnDecodeParams`'
  (`csrc/params.h`); `Audit/ParamReads.lean` checks the list against the decoded program. -/
  paramB : intBytes P.b 0 (param "0") L
  paramHq : intBytes 64 8 (param "0") L
  paramScale : ∃ bits < 2 ^ 32, floatBytes bits P.scale 28 (param "0") L
  paramPage : intBytes P.page 36 (param "0") L
  paramTopk : intBytes P.topk 40 (param "0") L
  paramExtraPage : intBytes P.extraPage 116 (param "0") L
  paramExtraTopk : intBytes P.extra_topk 120 (param "0") L
  paramStrideKvBlock : intBytes P.blockStride 164 (param "0") L
  paramStrideIndicesB : intBytes (P.s_q * P.topk) 172 (param "0") L
  paramStrideIndicesSq : intBytes P.topk 176 (param "0") L
  paramStrideLseB : intBytes (P.s_q * 64) 180 (param "0") L
  paramStrideLseSq : intBytes 64 184 (param "0") L
  paramStrideExtraKvBlock : intBytes P.extraBlockStride 200 (param "0") L
  paramStrideExtraIndicesB : intBytes (P.s_q * P.extra_topk) 208 (param "0") L
  paramStrideExtraIndicesSq : intBytes P.extra_topk 212 (param "0") L
  paramIndices : ptrBytes P.indicesBase 72 (param "0") L
  paramLse : ptrBytes P.lseBase 96 (param "0") L
  paramExtraIndices : ptrBytes P.extraIndicesBase 136 (param "0") L
  paramTopkLen : match P.topkLenBase with
    | none => (∀ k < 8, L.paramBytes (param "0") (80 + k) = some 0) ∧
      ∀ e < P.b, P.topkLen e = P.topk
    | some x => ptrBytes x 80 (param "0") L ∧ x % 4 = 0 ∧
      ∀ e < P.b, ∀ k < 4, mem0 ⟨.global, 0, x + 4 * e + k⟩ =
        some (some (word32Byte (P.topkLen e) k)) ∧
      ∀ e < P.b, P.topkLen e ≤ P.topk
  paramSink : match P.sinkBase with
    | none => (∀ k < 8, L.paramBytes (param "0") (88 + k) = some 0) ∧
      ∀ h < 64, P.sink h = none
    | some x => ptrBytes x 88 (param "0") L ∧ x % 4 = 0 ∧
      ∀ h < 64, ∃ s bits, P.sink h = some s ∧ bits < 2 ^ 32 ∧
        (∀ k < 4, mem0 ⟨.global, 0, x + 4 * h + k⟩ =
          some (some (word32Byte bits k))) ∧
          (f32Value bits).map (fun q : ℚ => (q : ℝ)) = some s
  paramExtraTopkLen : match P.extraTopkLenBase with
    | none => (∀ k < 8, L.paramBytes (param "0") (144 + k) = some 0) ∧
      ∀ e < P.b, P.extraTopkLen e = P.extra_topk
    | some x => ptrBytes x 144 (param "0") L ∧ x % 4 = 0 ∧
      ∀ e < P.b, ∀ k < 4, mem0 ⟨.global, 0, x + 4 * e + k⟩ =
        some (some (word32Byte (P.extraTopkLen e) k)) ∧
      ∀ e < P.b, P.extraTopkLen e ≤ P.extra_topk
  topkLenAddressable : OptionalGlobalRange P.topkLenBase (4 * P.b)
  sinkAddressable : OptionalGlobalRange P.sinkBase (4 * 64)
  extraTopkLenAddressable : OptionalGlobalRange P.extraTopkLenBase (4 * P.b)
  /-- The four tensor maps, published at the descriptor slots of `param_1`. -/
  mapQBind : L.tensorMaps (P.param1Base + 128) =
    some ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩
  mapOBind : L.tensorMaps (P.param1Base + 512) =
    some ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩
  mapKVBind : L.tensorMaps (P.param1Base + 768) =
    some ⟨1, mapKv P.kvBase P.numBlocks P.blockStride P.kvClass⟩
  mapExtraKvBind : P.extra_topk = 0 ∨ L.tensorMaps (P.param1Base + 896) =
    some ⟨1, mapExtraKv P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass⟩
  /-- A large-class cache map with the gather4 box's out-of-bounds words needs the device's
  large-allocation backing. -/
  kvBacking : P.kvClass = .large → TensorLargeBacking L mem0 P.kvBase
  extraKvBacking : P.extra_topk ≠ 0 → P.extraKvClass = .large →
    TensorLargeBacking L mem0 P.extraKvBase
  /-- Q is a contiguous bf16 `(b, s_q, 64, 512)` tensor. -/
  qInput : ∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, ∀ t < 512, ∀ byte < 2,
    mem0 (((⟨.global, 0, P.qBase + 2 * (((e * P.s_q + q) * 64 + h) * 512 + t)⟩ : Loc)).at byte) =
      some (some ((Value.float .bf16 (P.q e q h t)).byteAt byte))
  /-- The caches are raw bytes, 528 per row. -/
  kvInput : ∀ r < P.numBlocks * (P.blockStride / 528), ∀ byte < 528,
    mem0 ⟨.global, 0, P.kvBase + r * 528 + byte⟩ =
      some (some (Value.bits 8 (BitVec.ofNat 64 (P.kvByte r byte)), 0))
  extraKvInput : ∀ r < P.extraNumBlocks * (P.extraBlockStride / 528), ∀ byte < 528,
    mem0 ⟨.global, 0, P.extraKvBase + r * 528 + byte⟩ =
      some (some (Value.bits 8 (BitVec.ofNat 64 (P.extraKvByte r byte)), 0))
  /-- The sparse indices are little-endian int32 rows of `topk` (extra: `extra_topk`). -/
  indicesBase : P.indicesBase % 8 = 0
  idxInput : ∀ e < P.b, ∀ q < P.s_q, ∀ j < P.topk, ∀ k < 4,
    mem0 ⟨.global, 0, P.indicesBase + 4 * ((e * P.s_q + q) * P.topk + j) + k⟩ =
      some (some (word32Byte (i32Bits (P.idx e q j)) k))
  extraIdxInput : P.extra_topk = 0 ∨
    (P.extraIndicesBase % 8 = 0 ∧
      ∀ e < P.b, ∀ q < P.s_q, ∀ j < P.extra_topk, ∀ k < 4,
        mem0 ⟨.global, 0, P.extraIndicesBase + 4 * ((e * P.s_q + q) * P.extra_topk + j) + k⟩ =
          some (some (word32Byte (i32Bits (P.extraIdx e q j)) k)))
  /-- Valid indices name rows of their cache. -/
  idxRange : ∀ e < P.b, ∀ q < P.s_q, ∀ j, slotValid P e q false j →
    0 ≤ P.idx e q j ∧ (P.idx e q j).toNat < P.numBlocks * P.page
  extraIdxRange : ∀ e < P.b, ∀ q < P.s_q, ∀ j, slotValid P e q true j →
    0 ≤ P.extraIdx e q j ∧ (P.extraIdx e q j).toNat < P.extraNumBlocks * P.extraPage
  /-- Only the selected rows must be decodable, and their e4m3/ue8m0 bytes are not NaN. -/
  e4m3Ok : ∀ e < P.b, ∀ q < P.s_q, ∀ extra j, slotValid P e q extra j →
    ∀ t < 512, (rowBytes P e q extra j) t ≠ 0x7f ∧ (rowBytes P e q extra j) t ≠ 0xff
  ue8m0Ok : ∀ e < P.b, ∀ q < P.s_q, ∀ extra j, slotValid P e q extra j →
    ∀ t < 512, (rowBytes P e q extra j) (512 + t / 32) ≠ 0xff
  /-- The outputs are allocated, contiguous and disjoint from the inputs. -/
  oAllocated : ∀ byte < tensorBytes P, mem0 ⟨.global, 0, P.outBase + byte⟩ ≠ none
  lseAlign : P.lseBase % 4 = 0
  lseAllocated : ∀ byte < lseBytes P, mem0 ⟨.global, 0, P.lseBase + byte⟩ ≠ none
  qApartO : P.qBase + tensorBytes P ≤ P.outBase ∨ P.outBase + tensorBytes P ≤ P.qBase
  kvApartO : P.kvBase + cacheBytes P.numBlocks P.blockStride ≤ P.outBase ∨
    P.outBase + tensorBytes P ≤ P.kvBase
  extraKvApartO : P.extra_topk = 0 ∨
    (P.extraKvBase + cacheBytes P.extraNumBlocks P.extraBlockStride ≤ P.outBase ∨
      P.outBase + tensorBytes P ≤ P.extraKvBase)
  idxApartO : P.indicesBase + 4 * P.b * P.s_q * P.topk ≤ P.outBase ∨
    P.outBase + tensorBytes P ≤ P.indicesBase
  outApartLse : P.outBase + tensorBytes P ≤ P.lseBase ∨ P.lseBase + lseBytes P ≤ P.outBase
  inputApartLse : P.qBase + tensorBytes P ≤ P.lseBase ∨ P.lseBase + lseBytes P ≤ P.qBase
  kvApartLse : P.kvBase + cacheBytes P.numBlocks P.blockStride ≤ P.lseBase ∨
    P.lseBase + lseBytes P ≤ P.kvBase
  extraKvApartLse : P.extra_topk = 0 ∨
    (P.extraKvBase + cacheBytes P.extraNumBlocks P.extraBlockStride ≤ P.lseBase ∨
      P.lseBase + lseBytes P ≤ P.extraKvBase)
  idxApartLse : P.indicesBase + 4 * P.b * P.s_q * P.topk ≤ P.lseBase ∨
    P.lseBase + lseBytes P ≤ P.indicesBase
  indicesAddressable : P.indicesBase + 4 * P.b * P.s_q * P.topk ≤ 2 ^ 64
  extraIndicesAddressable : 0 < P.extra_topk →
    P.extraIndicesBase + 4 * P.b * P.s_q * P.extra_topk ≤ 2 ^ 64
  extraIdxApartO : 0 < P.extra_topk →
    Apart (4 * P.b * P.s_q * P.extra_topk) (tensorBytes P) P.extraIndicesBase P.outBase
  extraIdxApartLse : 0 < P.extra_topk →
    Apart (4 * P.b * P.s_q * P.extra_topk) (lseBytes P) P.extraIndicesBase P.lseBase
  topkLenApartO : OptionalApart P.topkLenBase (4 * P.b) P.outBase (tensorBytes P)
  extraTopkLenApartO : OptionalApart P.extraTopkLenBase (4 * P.b) P.outBase (tensorBytes P)
  sinkApartO : OptionalApart P.sinkBase (4 * 64) P.outBase (tensorBytes P)
  topkLenApartLse : OptionalApart P.topkLenBase (4 * P.b) P.lseBase (lseBytes P)
  extraTopkLenApartLse : OptionalApart P.extraTopkLenBase (4 * P.b) P.lseBase (lseBytes P)
  sinkApartLse : OptionalApart P.sinkBase (4 * 64) P.lseBase (lseBytes P)
  /-- The shared-memory window. -/
  sharedAlignment : P.sharedBase % 1024 = 0
  sharedBase : L.sharedBase = P.sharedBase
  sharedRange : P.sharedBase + sharedBytes ≤ 2 ^ 18
  sharedAllocated : ∀ cta < L.grid, ∀ byte < sharedBytes,
    mem0 ⟨.shared, cta, P.sharedBase + byte⟩ ≠ none

variable {P : Params} {L : Launch} {mem0 : Mem0}

theorem Pre.bRange (h : Pre P L mem0) : P.b ≤ 2 ^ 32 := by
  have := h.bLt
  omega

theorem Pre.sqRange (h : Pre P L mem0) : P.s_q ≤ 2 ^ 32 := by
  have := h.sqLt
  omega

theorem Pre.strideRange (h : Pre P L mem0) : 65536 * P.s_q < 2 ^ 40 := by
  have := h.qoBatchStrideRange
  omega

theorem Pre.topkAdd63Lt (h : Pre P L mem0) : P.topk + 63 < 2 ^ 31 := by
  have := Nat.le_mul_of_pos_left P.topk h.sqPos
  have := h.topkRange
  have := h.topkDiv64
  omega

theorem Pre.extraTopkAdd63Lt (h : Pre P L mem0) : P.extra_topk + 63 < 2 ^ 31 := by
  have := Nat.le_mul_of_pos_left P.extra_topk h.sqPos
  have := h.extraTopkRange
  have := h.extraDiv64
  omega

theorem Pre.mainIndexBatchOffsetLt (h : Pre P L mem0) {e : Nat} (he : e < P.b) :
    e * (P.s_q * P.topk) < 2 ^ 31 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega : e ≤ P.b - 1)) h.indicesRange

theorem Pre.extraIndexBatchOffsetLt (h : Pre P L mem0) {e : Nat} (he : e < P.b) :
    e * (P.s_q * P.extra_topk) < 2 ^ 63 := by
  have hb : e < 2 ^ 31 := he.trans h.bLt
  have hp := h.extraTopkRange
  calc
    e * (P.s_q * P.extra_topk) ≤ (2 ^ 31 : Nat) * 2 ^ 31 :=
      Nat.mul_le_mul (Nat.le_of_lt hb) (Nat.le_of_lt hp)
    _ < 2 ^ 63 := by decide

theorem Pre.topkLenNonNull {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    ∀ x, P.topkLenBase = some x → 0 < x :=
  fun x hx => (h.topkLenAddressable x hx).1

theorem Pre.topkLenBaseLt {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    ∀ x, P.topkLenBase = some x → x < 2 ^ 64 := by
  intro x hx
  have hr := (h.topkLenAddressable x hx).2.2
  have hb := h.bPos
  omega

theorem Pre.extraTopkLenNonNull {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    ∀ x, P.extraTopkLenBase = some x → 0 < x :=
  fun x hx => (h.extraTopkLenAddressable x hx).1

theorem Pre.extraTopkLenBaseLt {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    ∀ x, P.extraTopkLenBase = some x → x < 2 ^ 64 := by
  intro x hx
  have hr := (h.extraTopkLenAddressable x hx).2.2
  have hb := h.bPos
  omega

theorem Pre.sinkNonNull {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    ∀ x, P.sinkBase = some x → 0 < x :=
  fun x hx => (h.sinkAddressable x hx).1

theorem Pre.sinkBaseLt {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    ∀ x, P.sinkBase = some x → x < 2 ^ 64 := by
  intro x hx
  have hr := (h.sinkAddressable x hx).2.2
  norm_num at hr
  omega

/-- The final global bytes of the output are the attention: element `(batch, query, head, d)` of
O is `attn` and LSE is `lse` for a non-empty row and `+inf` for an empty one, and
every other global byte is preserved. -/
def Post (P : Params) (mem0 : Mem0) (m : FinalMem) : Prop :=
  (∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, ∀ d < 512,
    memFloat .bf16 m (oLoc P e q h d) = .ok (attn P e q h d)) ∧
  (∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, rowSum P e q h ≠ 0 →
    memFloat .f32 m (lseLoc P e q h) = .ok (lse P e q h)) ∧
  (∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, rowSum P e q h = 0 →
    ∀ k < 4, m ((lseLoc P e q h).at k) =
      some (some (infByte k))) ∧
  ∀ l, l.space = .global →
    ¬ (P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P) →
    ¬ (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P) → m l = mem0 l

end
end PTX.Kernels.FlashMlaSparseDecodeH64
