-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Kernels.TmlFa4Fwd.Data.Decoded
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd

open TensorDescriptor
noncomputable section

abbrev kernel : Kernel := Decoded.kernel

/-- A byte range in global memory. -/
structure Region where
  base : Nat
  bytes : Nat

def Region.Contains (r : Region) (l : Loc) : Prop :=
  l.space = .global ∧ l.cta = 0 ∧ r.base ≤ l.addr ∧ l.addr < r.base + r.bytes

def Region.Apart (a b : Region) : Prop :=
  a.base + a.bytes ≤ b.base ∨ b.base + b.bytes ≤ a.base

def globalLoc (addr : Nat) : Loc := ⟨.global, 0, addr⟩

/-- Runtime element strides of a paged BF16 cache with a contiguous head dimension. -/
structure CacheLayout where
  base : Nat
  rowStride : Nat
  headStride : Nat
  pageStride : Nat

def CacheLayout.loc (c : CacheLayout) (page head row d : Nat) : Loc :=
  globalLoc (c.base + 2 * (page * c.pageStride + head * c.headStride + row * c.rowStride + d))

def CacheLayout.region (c : CacheLayout) (pages heads : Nat) : Region :=
  ⟨c.base, 2 * ((pages - 1) * c.pageStride + (heads - 1) * c.headStride + 15 * c.rowStride + 128)⟩

/-- Compiled specialization: 128-dimensional BF16 Q/K/V and sheared bias, page size 16,
six Q heads per KV head, two Q stages per CTA, FP32 O and LSE. -/
structure Params where
  batch : Nat
  kvHeads : Nat
  pages : Nat
  pageTableStride : Nat
  qOffset : Nat → Nat
  kLength : Nat → Nat
  page : Nat → Nat → Nat
  qBase : Nat
  biasBase : Nat
  oBase : Nat
  lseBase : Nat
  lseStride : Nat
  cuQBase : Nat
  usedKBase : Nat
  pageTableBase : Nat
  kLayout : CacheLayout
  vLayout : CacheLayout
  qMapAddress : Nat
  oMapAddress : Nat
  biasMapAddress : Nat
  qAllocation : AllocationClass
  oAllocation : AllocationClass
  biasAllocation : AllocationClass
  scaleLog2Bits : Nat
  invScaleBits : Nat
  q : Nat → Nat → Nat → ℝ
  k : Nat → Nat → Nat → Nat → ℝ
  v : Nat → Nat → Nat → Nat → ℝ
  /-- The supplied sheared tensor, indexed by absolute Q row, head and packed bias column.
  `none` supplies the BF16 negative-infinity encoding. -/
  bias : Nat → Nat → Nat → Option ℝ

def Params.heads (p : Params) : Nat := 6 * p.kvHeads
def Params.totalQ (p : Params) : Nat := p.qOffset p.batch
def Params.qLength (p : Params) (b : Nat) : Nat := p.qOffset (b + 1) - p.qOffset b
def Params.grid (p : Params) : Nat := (p.totalQ + 255 * p.batch) / 256 * p.heads

def Params.qLoc (p : Params) (q h d : Nat) : Loc :=
  globalLoc (p.qBase + 2 * ((q * p.heads + h) * 128 + d))

def Params.biasLoc (p : Params) (q h col : Nat) : Loc :=
  globalLoc (p.biasBase + 2 * ((q * p.heads + h) * 1280 + col))

def Params.oLoc (p : Params) (q h d : Nat) : Loc :=
  globalLoc (p.oBase + 4 * ((q * p.heads + h) * 128 + d))

def Params.lseLoc (p : Params) (q h : Nat) : Loc :=
  globalLoc (p.lseBase + 4 * (h * p.lseStride + q))

def Params.inputRegions (p : Params) : List Region :=
  [⟨p.qBase, 256 * p.heads * p.totalQ⟩, ⟨p.biasBase, 2560 * p.heads * (p.totalQ + 128)⟩,
   p.kLayout.region p.pages p.kvHeads, p.vLayout.region p.pages p.kvHeads,
   ⟨p.cuQBase, 4 * (p.batch + 1)⟩, ⟨p.usedKBase, 4 * p.batch⟩,
   ⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩]

def Params.oRegion (p : Params) : Region :=
  ⟨p.oBase, 512 * p.heads * p.totalQ⟩

def Params.lseRegion (p : Params) : Region :=
  ⟨p.lseBase, 4 * ((p.heads - 1) * p.lseStride + p.totalQ)⟩

def Params.qMap (p : Params) : Descriptor 2 :=
  ⟨.bf16, p.qBase, ![128, p.totalQ, p.heads], ![256 * p.heads, 256],
   ⟨![64, 128, 1], ![1, 1, 1]⟩, .b128, .zero, p.qAllocation⟩

def Params.biasMap (p : Params) : Descriptor 2 :=
  ⟨.bf16, p.biasBase, ![1280, p.totalQ + 128, p.heads], ![2560 * p.heads, 2560],
   ⟨![64, 128, 1], ![1, 1, 1]⟩, .b128, .zero, p.biasAllocation⟩

/-- The output TMA coordinates are `(d, 2^30 - qLength + row, head, qEnd)`.
The extra extent lets the row axis clip a request's final tile before the next request. -/
def Params.oMap (p : Params) : Descriptor 3 :=
  ⟨.f32, p.oBase - 2 ^ 30 * (512 * p.heads),
   ![128, 2 ^ 30, p.heads, 2 ^ 31 - 1], ![512 * p.heads, 512, 512 * p.heads],
   ⟨![32, 128, 1, 1], ![1, 1, 1, 1]⟩, .b128, .zero, p.oAllocation⟩

def param (i : Nat) : String := kernel.name ++ "_param_" ++ toString i

def mapParam (i : Nat) : ParamObjectDecl := ⟨param i, 8, 128, 64⟩

/-- Each tuple gives the parameter index, byte offset and size, and little-endian value. -/
def Params.objectWords (p : Params) : List (Nat × Nat × Nat × Nat) :=
  [(1, 0, 8, p.kLayout.base), (1, 8, 4, 16), (1, 12, 4, p.kvHeads),
   (1, 24, 8, p.kLayout.rowStride), (1, 32, 8, p.kLayout.headStride),
   (1, 40, 8, p.kLayout.pageStride),
   (2, 0, 8, p.vLayout.base), (2, 24, 8, p.vLayout.rowStride),
   (2, 32, 8, p.vLayout.headStride), (2, 40, 8, p.vLayout.pageStride),
   (4, 0, 8, p.lseBase), (4, 16, 8, p.lseStride),
   (5, 0, 8, p.cuQBase), (6, 0, 8, p.usedKBase),
   (7, 0, 8, p.pageTableBase), (7, 16, 8, p.pageTableStride), (24, 0, 8, p.cuQBase)]

def Params.scalarWords (p : Params) : List (Nat × Nat) :=
  [(12, p.scaleLog2Bits), (14, p.invScaleBits), (17, p.heads), (19, p.batch), (22, 800)]

def leByte (n k : Nat) : BitVec 8 := BitVec.ofNat 8 (n / 256 ^ k)

def HasValue (m : Mem0) (l : Loc) (v : Value) : Prop :=
  ∀ byte < v.bytes, m (l.at byte) = some (some (v.byteAt byte))

def biasValue : Option ℝ → Value
  | none => .bits 16 0xFF80
  | some x => .float .bf16 x

/-- The packed bias columns end at the last causal key block of this 128-row Q stage. -/
def Params.biasColumn (p : Params) (b row j : Nat) : Int :=
  let stageEnd := (row / 128 + 1) * 128
  let past := p.kLength b - p.qLength b
  let blockEnd := (min (stageEnd + past) (p.kLength b) + 127) / 128 * 128
  (j : Int) + 1280 - blockEnd

def Params.keyCount (p : Params) (b row : Nat) : Nat :=
  min (p.kLength b) (p.kLength b - p.qLength b + row + 1)

/-- Launch, ABI bindings and byte contents of the Inkling 2 forward entry. -/
structure Pre (p : Params) (l : Launch) (m : Mem0) : Prop where
  launch : l.Valid kernel
  grid : 0 < p.grid ∧ l.grid = p.grid ∧ l.grid < 2 ^ 31
  block : l.block = 512
  cluster : l.clusterSize.val = 1 ∧ l.explicitCluster = false ∧ l.OneDim
  shape : 0 < p.batch ∧ p.batch < 2 ^ 31 ∧ 0 < p.kvHeads ∧ 0 < p.pages ∧
    p.qOffset 0 = 0 ∧ p.totalQ + 256 * p.batch < 2 ^ 30
  lengths : ∀ b < p.batch, p.qOffset b ≤ p.qOffset (b + 1) ∧
    p.qLength b ≤ p.kLength b ∧ p.kLength b + 256 < 2 ^ 31
  pageTable : ∀ b < p.batch, (p.kLength b + 15) / 16 ≤ p.pageTableStride ∧
    ∀ i < (p.kLength b + 15) / 16, p.page b i < p.pages ∧ p.page b i < 2 ^ 31
  values : ∀ i ∈ p.scalarWords, i.2 < 2 ^ 32 ∧ l.params (param i.1) = some (BitVec.ofNat 64 i.2)
  objectBytes : ∀ (i off bytes value : Nat), (i, off, bytes, value) ∈ p.objectWords →
    value < 256 ^ bytes ∧ ∀ k < bytes, l.paramBytes (param i) (off + k) = some (leByte value k)
  scales : ∃ s t : ℚ, f32Value p.scaleLog2Bits = some s ∧ f32Value p.invScaleBits = some t ∧
    0 < s ∧ 0 < t
  maps : ∀ (i address : Nat) (binding : (outer : Nat) × Descriptor outer),
    (i, address, binding) ∈ [(9, p.qMapAddress, ⟨2, p.qMap⟩), (10, p.oMapAddress, ⟨3, p.oMap⟩),
      (11, p.biasMapAddress, ⟨2, p.biasMap⟩)] →
    l.paramObjects (param i) = some (mapParam i, address) ∧
    address % 64 = 0 ∧ address + 128 ≤ 2 ^ 64 ∧
    l.tensorMaps address = some binding ∧ TensorDescriptor.Valid binding.2 ∧
    (binding.2.allocationClass = .large → TensorLargeBacking l m binding.2.base)
  raggedBase : 2 ^ 30 * (512 * p.heads) ≤ p.oBase
  alignment : p.kLayout.base % 16 = 0 ∧ p.vLayout.base % 16 = 0 ∧
    p.kLayout.rowStride % 8 = 0 ∧ p.kLayout.headStride % 8 = 0 ∧ p.kLayout.pageStride % 8 = 0 ∧
    p.vLayout.rowStride % 8 = 0 ∧ p.vLayout.headStride % 8 = 0 ∧ p.vLayout.pageStride % 8 = 0 ∧
    p.cuQBase % 4 = 0 ∧ p.usedKBase % 4 = 0 ∧ p.pageTableBase % 4 = 0 ∧ p.lseBase % 4 = 0
  lseStride : p.totalQ ≤ p.lseStride
  ranges : ∀ r ∈ p.oRegion :: p.lseRegion :: p.inputRegions, r.base + r.bytes ≤ 2 ^ 64
  separate : p.oRegion.Apart p.lseRegion ∧
    ∀ r ∈ p.inputRegions, p.oRegion.Apart r ∧ p.lseRegion.Apart r
  cuQ : ∀ b ≤ p.batch, HasValue m (globalLoc (p.cuQBase + 4 * b))
    (.bits 32 (BitVec.ofNat 64 (p.qOffset b)))
  usedK : ∀ b < p.batch, HasValue m (globalLoc (p.usedKBase + 4 * b))
    (.bits 32 (BitVec.ofNat 64 (p.kLength b)))
  pageBytes : ∀ b < p.batch, ∀ i < (p.kLength b + 15) / 16,
    HasValue m (globalLoc (p.pageTableBase + 4 * (b * p.pageTableStride + i)))
      (.bits 32 (BitVec.ofNat 64 (p.page b i)))
  qBytes : ∀ q < p.totalQ, ∀ h < p.heads, ∀ d < 128,
    HasValue m (p.qLoc q h d) (.float .bf16 (p.q q h d))
  kvBytes : ∀ page < p.pages, ∀ h < p.kvHeads, ∀ r < 16, ∀ d < 128,
    HasValue m (p.kLayout.loc page h r d) (.float .bf16 (p.k page h r d)) ∧
    HasValue m (p.vLayout.loc page h r d) (.float .bf16 (p.v page h r d))
  biasBytes : ∀ q < p.totalQ + 128, ∀ h < p.heads, ∀ col < 1280,
    HasValue m (p.biasLoc q h col) (biasValue (p.bias q h col))
  biasMask : ∀ b < p.batch, ∀ row < p.qLength b, ∀ h < p.heads, ∀ j,
    let col := p.biasColumn b row j
    0 ≤ col → col < 1280 →
    (p.bias (p.qOffset b + row) h col.toNat).isSome = decide (j < p.keyCount b row)
  outputs : ∀ l', p.oRegion.Contains l' ∨ p.lseRegion.Contains l' → m l' ≠ none
  shared : l.sharedBase % 1024 = 0 ∧ l.sharedBase + 232448 ≤ 2 ^ 18 ∧
    ∀ cta < l.grid, ∀ k < 232448, m ⟨.shared, cta, l.sharedBase + k⟩ ≠ none
  localMemory : l.localBase % 32 = 0 ∧ l.localBase + 128 ≤ 2 ^ 32 ∧
    ∀ g < l.threads, ∀ k < 128, m ⟨.local, g, l.localBase + k⟩ ≠ none

def abiFloat (bits : Nat) : ℝ := ((f32Value bits).getD 0 : ℚ)

def score (p : Params) (b h row j : Nat) : ℝ :=
  let page := p.page b (j / 16)
  let dot := ∑ d ∈ Finset.range 128, p.q (p.qOffset b + row) h d * p.k page (h / 6) (j % 16) d
  let col := p.biasColumn b row j
  let bias := if 0 ≤ col ∧ col < 1280 then (p.bias (p.qOffset b + row) h col.toNat).getD 0 else 0
  abiFloat p.scaleLog2Bits * (dot + abiFloat p.invScaleBits * bias)

def weight (p : Params) (b h row j : Nat) : ℝ :=
  (2 : ℝ) ^ score p b h row j

def mass (p : Params) (b h row : Nat) : ℝ :=
  ∑ j ∈ Finset.range (p.keyCount b row), weight p b h row j

def attention (p : Params) (b h row d : Nat) : ℝ :=
  (∑ j ∈ Finset.range (p.keyCount b row),
    weight p b h row j * p.v (p.page b (j / 16)) (h / 6) (j % 16) d) / mass p b h row

/-- The PTX uses the FP32 encoding of ln(2) to rescale a base-two LSE. -/
def lse (p : Params) (b h row : Nat) : ℝ :=
  abiFloat 0x3F317218 * Real.logb 2 (mass p b h row)

def Post (p : Params) (m0 : Mem0) (m : FinalMem) : Prop :=
  (∀ b < p.batch, ∀ h < p.heads, ∀ row < p.qLength b,
    (∀ d < 128, memFloat .f32 m (p.oLoc (p.qOffset b + row) h d) = .ok (attention p b h row d)) ∧
    memFloat .f32 m (p.lseLoc (p.qOffset b + row) h) = .ok (lse p b h row)) ∧
  ∀ l, l.space = .global → ¬ p.oRegion.Contains l →
    (∀ q < p.totalQ, ∀ h < p.heads, ∀ k < 4, l ≠ (p.lseLoc q h).at k) → m l = m0 l

end
end PTX.Kernels.TmlFa4Fwd
