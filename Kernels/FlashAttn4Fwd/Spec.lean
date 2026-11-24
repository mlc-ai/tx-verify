-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Arith.FastDivmod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Kernels.FlashAttn4Fwd.Data.TensorMaps
public import Kernels.FlashAttn4Fwd.Data.Decoded

@[expose] public section

/-!
The FlashAttention-4 forward kernel (CuTeDSL, `flash_fwd_sm100.py`), head dimension 128, fp16,
non-causal, for a symbolic shape: batch `b`, heads `h`, `seqlen_q = sq`, `seqlen_k = sk`.

The host passes Q, K, V and O as contiguous `(batch, seqlen, heads, 128)` f16 tensors. The
kernel's scale parameter is `softmax_scale · log₂ e` and the kernel exponentiates in base 2, so
the output is `softmax(scale · Q Kᵀ) V` with base-2 exponentials; `Post` states exactly that
and nothing about `e`. Floating values denote exact reals under the kernel's assumptions
(`Assumptions.lean`). The precondition describes launch bindings, parameter bytes, input bytes
and available storage; the schedule, buffer ownership, synchronization and progress are proof
obligations. The reasons for each field are in `DECISIONS.md` ("Spec").
-/

namespace PTX.Kernels.FlashAttn4Fwd
open PTX TensorDescriptor
noncomputable section

/-- All 4897 decoded instructions of the frozen program. -/
def kernel : Kernel := Decoded.kernel

theorem kernel_code_length : kernel.code.length = 4897 := Decoded.code_length

theorem kernel_groupUniform : kernel.TcGroupUniform := by
  unfold Kernel.TcGroupUniform
  decide +kernel

/-- Bytes of the dynamic shared memory one CTA uses: the size of the kernel's `SharedStorage`
(232448), which coincides with the sm_100 maximum of 227 KiB per CTA. -/
def sharedBytes : Nat := 232448

/-- The name of parameter `param_i` of the entry, `i` written in decimal (`"0"` .. `"14"`). -/
def param (i : String) : String := kernel.name ++ "_param_" ++ i

/-- A tensor-map parameter: `.param .align 64 .b8 name[128]`. -/
def mapParam (i : String) : ParamObjectDecl := ⟨param i, 8, 128, 64⟩

/-- The actual parameter declarations of the compiled PTX: the scalars `param_8` (`.f32`),
`param_13` and `param_14` (`.u32`); by-value objects: the tensor structs `param_0` ..
`param_3` (16 bytes), the tensor maps `param_4` .. `param_7` (128 bytes), `param_9` and
`param_10` (64 bytes) and the divmod objects `param_11`, `param_12` (12 bytes). -/
theorem kernel_params :
    kernel.params = [(param "8", 32), (param "13", 32), (param "14", 32)] := by
  decide +kernel

theorem kernel_paramObjects : kernel.paramObjects =
    [⟨param "0", 8, 16, 4⟩, ⟨param "1", 8, 16, 4⟩, ⟨param "2", 8, 16, 4⟩, ⟨param "3", 8, 16, 4⟩,
      mapParam "4", mapParam "5", mapParam "6", mapParam "7", ⟨param "9", 8, 64, 32⟩,
      ⟨param "10", 8, 64, 32⟩, ⟨param "11", 8, 12, 4⟩, ⟨param "12", 8, 12, 4⟩] := by
  decide +kernel

/-- Byte `k` (little-endian) of the number `x`. -/
def leByte (x k : Nat) : BitVec 8 := BitVec.ofNat 8 (x / 256 ^ k)

/-- A CuTeDSL `FastDivmodDivisor` parameter object (12 bytes, of which the kernel reads ten):
the divisor and the multiplier as little-endian 32-bit words at bytes 0 and 4, and the two shift
amounts as bytes 8 and 9. -/
structure Divmod where
  divisor : Nat
  mul : Nat
  shift1 : Nat
  shift2 : Nat

/-- Byte `k < 10` of the object. -/
def Divmod.byte (p : Divmod) (k : Nat) : BitVec 8 :=
  if k < 4 then leByte p.divisor k
  else if k < 8 then leByte p.mul (k - 4)
  else if k = 8 then BitVec.ofNat 8 p.shift1
  else BitVec.ofNat 8 p.shift2

/-- The object divides by `d`: it stores `d`, its fields fit their bytes, and the kernel's
instruction sequence (`FastDivmod.quot`: `mul.hi.u32`, `sub.s32`, `shr.u32`, `add.s32`,
`shr.u32`) yields the exact quotient of every 32-bit dividend. -/
def Divmod.Exact (p : Divmod) (d : Nat) : Prop :=
  p.divisor = d ∧ p.mul < 2 ^ 32 ∧ p.shift1 < 2 ^ 8 ∧ p.shift2 < 2 ^ 8 ∧
    ∀ n < 2 ^ 32, FastDivmod.quot p.mul p.shift1 p.shift2 n = n / d

structure Params where
  /-- Batch size, head count, `seqlen_q`, `seqlen_k`. -/
  b : Nat
  h : Nat
  sq : Nat
  sk : Nat
  /-- Number of clusters (CTA pairs) of the grid. -/
  clusters : Nat
  qBase : Nat
  kBase : Nat
  vBase : Nat
  oBase : Nat
  qMap : Nat
  kMap : Nat
  vMap : Nat
  oMap : Nat
  qClass : AllocationClass
  kClass : AllocationClass
  vClass : AllocationClass
  oClass : AllocationClass
  qFill : Fill
  kFill : Fill
  vFill : Fill
  oFill : Fill
  /-- The scheduler's divmod objects (`param_11`, `param_12`). -/
  blockDivmod : Divmod
  headDivmod : Divmod
  /-- Input values by (batch, head, row, head-dimension index). -/
  q : Nat → Nat → Nat → Nat → ℝ
  k : Nat → Nat → Nat → Nat → ℝ
  v : Nat → Nat → Nat → Nat → ℝ
  /-- The kernel's scale (`param_8`): `softmax_scale · log₂ e` as the host passes it. -/
  scale : ℝ

/-- Work items of 512 query rows per (batch, head): `ceil(sq / 512)`. -/
def Params.blocks (P : Params) : Nat := (P.sq + 511) / 512

/-- `total_blocks_cluster` (`param_13`): one item per cluster per (batch, head, 512 rows). -/
def Params.items (P : Params) : Nat := P.blocks * P.h * P.b

/-- Bytes of a contiguous `(b, rows, h, 128)` f16 tensor. -/
def tensorBytes (P : Params) (rows : Nat) : Nat := 256 * P.b * P.h * rows

/-- The global location of element `(batch, head, row, d)` of a contiguous
`(b, rows, h, 128)` f16 tensor; its two bytes are `at 0` and `at 1`. -/
def elementLoc (P : Params) (base rows batch head row d : Nat) : Loc :=
  ⟨.global, 0, base + 2 * (((batch * rows + row) * P.h + head) * 128 + d)⟩

/-- The unscaled score of query row `row` with key `j`: `S = Q Kᵀ`. -/
def score (P : Params) (batch head row j : Nat) : ℝ :=
  ∑ t ∈ Finset.range 128, P.q batch head row t * P.k batch head j t

/-- The unnormalized base-2 attention weight of key `j`: `2 ^ (scale · S)`. -/
def weight (P : Params) (batch head row j : Nat) : ℝ :=
  (2 : ℝ) ^ (P.scale * score P batch head row j)

/-- The attention output: `Σ_j w_j V_j / Σ_j w_j` over the `sk` keys. -/
def attn (P : Params) (batch head row d : Nat) : ℝ :=
  (∑ j ∈ Finset.range P.sk, weight P batch head row j * P.v batch head j d) /
    ∑ j ∈ Finset.range P.sk, weight P batch head row j

/-- Two byte ranges of length `n` do not overlap. -/
def Apart (n a b : Nat) : Prop := a + n ≤ b ∨ b + n ≤ a

/-- Initial launch and memory requirements, without execution or protocol assumptions. -/
structure Pre (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  grid : L.grid = 2 * P.clusters
  clustersPos : 0 < P.clusters
  block : L.block = 512
  cluster : L.clusterSize.val = 2
  /-- The launch is one-dimensional: a one-dimensional grid made of whole one-dimensional
  clusters. -/
  oneDimLaunch : L.oneDimLaunch
  bPos : 0 < P.b
  hPos : 0 < P.h
  sqPos : 0 < P.sq
  sqDiv512 : P.sq % 512 = 0
  skPos : 0 < P.sk
  skDiv128 : P.sk % 128 = 0
  sqRange : P.sq < 2 ^ 31
  skRange : P.sk < 2 ^ 31
  batchRange : P.b ≤ 2 ^ 32
  strideRange : 256 * P.h * P.sq < 2 ^ 40 ∧ 256 * P.h * P.sk < 2 ^ 40
  scheduleRange : P.items + P.clusters ≤ 2 ^ 31
  /-- `param_1` (the K tensor object): its first 32-bit word, the only one read, is `sk`. -/
  paramSeqK : ∀ k < 4, L.paramBytes (param "1") k = some (leByte P.sk k)
  paramBlockDivmod : ∀ k < 10, L.paramBytes (param "11") k = some (P.blockDivmod.byte k)
  blockDivmod : P.blockDivmod.Exact P.blocks
  paramHeadDivmod : ∀ k < 10, L.paramBytes (param "12") k = some (P.headDivmod.byte k)
  headDivmod : P.headDivmod.Exact P.h
  paramItems : L.params (param "13") = some (BitVec.ofNat 64 P.items)
  paramScale : ∃ bits < 2 ^ 32, L.params (param "8") = some (BitVec.ofNat 64 bits) ∧
    (f32Value bits).map (fun x : ℚ => (x : ℝ)) = some P.scale
  paramQ : L.paramObjects (param "4") = some (mapParam "4", P.qMap)
  paramK : L.paramObjects (param "5") = some (mapParam "5", P.kMap)
  paramV : L.paramObjects (param "6") = some (mapParam "6", P.vMap)
  paramO : L.paramObjects (param "7") = some (mapParam "7", P.oMap)
  mapQ : L.tensorMaps P.qMap =
    some ⟨3, FlashAttn4Fwd.mapQ P.qBase P.sq P.h P.b P.qFill P.qClass⟩
  mapK : L.tensorMaps P.kMap =
    some ⟨3, FlashAttn4Fwd.mapK P.kBase P.sk P.h P.b P.kFill P.kClass⟩
  mapV : L.tensorMaps P.vMap =
    some ⟨3, FlashAttn4Fwd.mapV P.vBase P.sk P.h P.b P.vFill P.vClass⟩
  mapO : L.tensorMaps P.oMap =
    some ⟨3, FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass⟩
  mapAlignment : P.qMap % 64 = 0 ∧ P.kMap % 64 = 0 ∧ P.vMap % 64 = 0 ∧ P.oMap % 64 = 0
  mapRange : P.qMap + 128 ≤ 2 ^ 64 ∧ P.kMap + 128 ≤ 2 ^ 64 ∧ P.vMap + 128 ≤ 2 ^ 64 ∧
    P.oMap + 128 ≤ 2 ^ 64
  mapApart : Apart 128 P.qMap P.kMap ∧ Apart 128 P.qMap P.vMap ∧ Apart 128 P.qMap P.oMap ∧
    Apart 128 P.kMap P.vMap ∧ Apart 128 P.kMap P.oMap ∧ Apart 128 P.vMap P.oMap
  tensorAlignment : P.qBase % 16 = 0 ∧ P.kBase % 16 = 0 ∧ P.vBase % 16 = 0 ∧ P.oBase % 16 = 0
  tensorRange : P.qBase + tensorBytes P P.sq ≤ 2 ^ 64 ∧
    P.kBase + tensorBytes P P.sk ≤ 2 ^ 64 ∧ P.vBase + tensorBytes P P.sk ≤ 2 ^ 64 ∧
    P.oBase + tensorBytes P P.sq ≤ 2 ^ 64
  outputApartQ : P.qBase + tensorBytes P P.sq ≤ P.oBase ∨
    P.oBase + tensorBytes P P.sq ≤ P.qBase
  outputApartK : P.kBase + tensorBytes P P.sk ≤ P.oBase ∨
    P.oBase + tensorBytes P P.sq ≤ P.kBase
  outputApartV : P.vBase + tensorBytes P P.sk ≤ P.oBase ∨
    P.oBase + tensorBytes P P.sq ≤ P.vBase
  inputQ : ∀ batch < P.b, ∀ head < P.h, ∀ row < P.sq, ∀ d < 128, ∀ byte < 2,
    mem0 ((elementLoc P P.qBase P.sq batch head row d).at byte) =
      some (some ((Value.float .f16 (P.q batch head row d)).byteAt byte))
  inputK : ∀ batch < P.b, ∀ head < P.h, ∀ row < P.sk, ∀ d < 128, ∀ byte < 2,
    mem0 ((elementLoc P P.kBase P.sk batch head row d).at byte) =
      some (some ((Value.float .f16 (P.k batch head row d)).byteAt byte))
  inputV : ∀ batch < P.b, ∀ head < P.h, ∀ row < P.sk, ∀ d < 128, ∀ byte < 2,
    mem0 ((elementLoc P P.vBase P.sk batch head row d).at byte) =
      some (some ((Value.float .f16 (P.v batch head row d)).byteAt byte))
  outputAllocated : ∀ byte < tensorBytes P P.sq, mem0 ⟨.global, 0, P.oBase + byte⟩ ≠ none
  sharedAlignment : L.sharedBase % 1024 = 0
  sharedRange : L.sharedBase + sharedBytes ≤ 2 ^ 18
  sharedAllocated : ∀ cta < L.grid, ∀ byte < sharedBytes,
    mem0 ⟨.shared, cta, L.sharedBase + byte⟩ ≠ none

/-- Complete ideal attention output: element `(batch, head, row, d)` of O, read as `f16`
(`memFloat`: the bytes as `ld` rebuilds them, read as an `f16` operand), is the base-2 softmax
attention `attn`; every other global byte is preserved. Output contents at launch are
unconstrained. -/
def Post (P : Params) (mem0 : Mem0) (m : FinalMem) : Prop :=
  (∀ batch < P.b, ∀ head < P.h, ∀ row < P.sq, ∀ d < 128,
    memFloat .f16 m (elementLoc P P.oBase P.sq batch head row d) =
      .ok (attn P batch head row d)) ∧
  ∀ l, l.space = .global →
    ¬ (l.cta = 0 ∧ P.oBase ≤ l.addr ∧ l.addr < P.oBase + tensorBytes P P.sq) → m l = mem0 l

end
end PTX.Kernels.FlashAttn4Fwd
