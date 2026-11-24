-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaOperands

@[expose] public section

namespace PTX.TcMma

/-! ## THREAD-TC-MMA-RESULT-LAYOUT — D matrix cells and lane masks
Statement: Element (i, j) of D occupies one 32-bit Tensor Memory word, also for FP16, at the lane
  and column that the layout of the shape and CTA group assigns (Layouts A, B, D, E, F and G of
  §9.7.18.10.5), counted from the D address. The D address is split into its lane field
  (`base / 2^16`) and column field (`base % 2^16`). A lane whose bit in the disable-output-lane mask
  is 1 is not written, and keeps its prior contents. A D address whose lane field is not a permitted
  alignment or whose columns pass the 512th has no cells.

Defs: TcMma.Cell, TcMma.halfDatapath, TcMma.columnBlocks, TcMma.aCell, TcMma.operandRow,
  TcMma.LaneAligned, TcMma.laneAlignedDecidable, TcMma.resultColumns, TcMma.resultCell,
  TcMma.OutputMaskValid, TcMma.outputMaskValidDecidable, TcMma.writeCell

Source:
- §9.7.18.10.5 Table and Figures 211–222 (Layouts A, B, C, D, E, F; Layout G by the table's 1x4
    organization)
- §9.7.18.10.4.1 (unpacked subword D)
- §9.7.18.10.10.1 (disable-output-lane); NVIDIA CUTLASS (commit e406c186)
    include/cute/atom/mma_traits_sm100.hpp tmem_frg, include/cute/atom/mma_traits_sm100_frag.hpp
    tmem_frg N_SM=2, mma_traits_sm100.hpp tmem_frg_ws
- EXT-TCFIG

Direction: reading

Applies: MMA with M = 128 per CTA of the group (Layouts A and D), M = 128 with cta_group::2 (Layout
  B), M = 64 with cta_group::1 (Layout F; Layout E with .ws) or M = 32 with .ws (Layout G), with a
  32-bit, FP16 or FP32 D

Premises: A valid decoded instruction shape, an in-range matrix coordinate, a D address whose lane
  field is a permitted datapath lane alignment (0, or 16 for Layout F) and whose column range fits
  the 512 physical columns; write queries additionally require `4 * group size` 32-bit mask words.

Effect: Potential/result-write footprint only. Unsupported or out-of-range queries return none
  without aliasing another cell. CTA identities are supplied by makeOperands.

### EXT-TCFIG — the operand and result layouts of tcgen05.mma

Statement: The model makes seven readings of the layouts of `tcgen05.mma`. (1) D layouts given by
  figures. The model reads the D layouts that the ISA gives only by figures (Layouts D, F, E and G)
  as explicit coordinate maps. Layout D for M = 128 with cta_group::1 (Figures 217 and 218) puts row
  `i` of D in lane `i` and column `j` in column `base + j`. Layout F for M = 64 with cta_group::1
  (Figures 221 and 222, and CUTLASS's 1SM M = 64 atom `((16,4),N):((1,32),128)`) puts row `i` in
  lane `alignment + i % 16 + 32 (i / 16)`. The `.ws` Layouts E (M = 64, Figures 219–220, 2x2) and G
  (M = 32, 1x4), as CUTLASS's `tmem_frg_ws` atoms `(64,(N/2,2)):(1,(128,64))` and
  `(32,(N/4,4)):(1,(128,32))` (lane stride 1, column stride 128), put element `(i, j)` in lane
  `i + r (j / (N r / 128))`, column `j % (N r / 128)` for `r` = 64 or 32. (2) Result layouts of a
  CTA pair. With `cta_group::2` and M = 256 (Layout A, Figures 211–212), row `i` of D is lane `i %
  128` of the even CTA for `i < 128` and of the odd CTA otherwise, at column `base + j`. The pair's
  even-rank CTA holds the first half of the rows of D and the odd-rank CTA the second half. With
  M = 128 (Layout B, Figures 213–214) each CTA holds 64 rows in the 2x2 datapath organization of
  Layout E, with N split into two column blocks at lanes 0–63 and 64–127. The
  `disable-output-lane` mask of a pair has 8 words that number 256 lanes: bits 0–127 are the even
  CTA's lanes and bits 128–255 the odd CTA's lanes. Bit 0 of the first element of the mask is lane
  0. (3) A in Tensor Memory. An A operand read from Tensor Memory (`[a-tmem]`) uses the same
  datapath organization as D (§9.7.18.10.5: half-datapath layouts "must use the same Tensor Memory
  lane alignment across matrices A , D"). It puts each row on the lane of the corresponding row of
  D. Its K-row bytes are packed contiguously into 32-bit words, the lower-numbered element in the
  lower bytes, as §9.7.18.10.4.3 states for 8-bit containers and as CUTLASS's `tmem_frg` for
  `SM100_MMA_*_TS` atoms lays out A with `sizeof_bits<uint32_t> / sizeof_bits<T>` elements per
  column. For 16-bit elements (kind::f16) a word holds two consecutive K elements, the
  lower-numbered one in its low half. With `cta_group::2` and M = 256 (Layout A) row `i` of A is
  lane `i % 128` of the even CTA of the pair for `i < 128` and of the odd CTA otherwise, as D's
  rows (reading 2), so each CTA's Tensor Memory holds the A rows of its own D rows. Layout B
  (M = 128 with `cta_group::2`), where CUTLASS duplicates A across subpartitions, has no A cells
  here, so such an issue is unsafe (ERR-TC-MMA). (4) `.ws` reads A per D lane. With `.ws`
  and M below 128, each lane of D reads its own copy of A: output (i, j) uses the A row on lane
  i + M (j / (N M / 128)), and with A in shared memory lane L reads row L mod M. Shared A is the
  same data for every lane of a row. (5) The operand partition of a CTA pair. With `.cta_group::2`,
  A is split along M and B along N; the first half of each is read from the shared memory of the
  pair's even-rank CTA and the second half from that of the odd-rank CTA, at the same descriptor
  offset in each. The pair's CTAs are the cluster ranks `2k` and `2k + 1` (that part is
  §9.7.18.5.1: "Any 2 CTAs within the cluster whose %cluster_ctarank differs by the last bit only is
  said to form a CTA pair"). (6) The layout of the 32-byte-atomic mode. In the 128-byte swizzling
  mode with 32-byte atomicity, an MN-major operand is laid out like in the other MN-major modes with
  swizzle atoms of 128 bytes along M or N by 4 rows along K, and the 32-byte-atomicity XOR of §5.5.7
  is applied to the absolute address. Read with the K extent of the atom reduced from 8 to 4, this
  gives 128 contiguous bytes along M/N, four such rows per atom (row stride 128 bytes), a leading
  offset between M/N atoms and the stride offset between K groups of four, and the absolute-address
  XOR of the §5.5.7 32-byte-atomicity table (chunk bits 5-6 XOR row bits 7-8, CUTLASS
  Swizzle<2,5,2>). A K-major operand in this mode has no address. (7) Operand rows of
  kind::f8f6f4. A row of a `kind::f8f6f4` operand with K = 32 occupies 32 bytes for every element
  type, as the shared-memory packing that the ISA states for `kind::mxf8f6f4` with dense K = 32. An
  operand row of `kind::f8f6f4` with dense K = 32 is 32 bytes in shared memory and in Tensor Memory:
  one byte per element for E4M3 and E5M2, and for the 6- and 4-bit types each 16 elements packed
  into 12 or 8 bytes followed by 4 or 8 padding bytes. The model reads these 32 bytes as the
  operand's footprint, addresses them as 32 one-byte elements, and gives no element value to a 6- or
  4-bit element: which bits of a 16-byte chunk hold which element is given only by Figures 207 and
  208, so the arithmetic of those types is left to a kernel assumption.

Source:
- §9.7.18.10.5.1
- §9.7.18.10.5.2 and their figures
- §9.7.18.10.10.1: "corresponds to a lane of the Tensor Memory"
- NVIDIA CUTLASS `include/cute/atom/mma_traits_sm100_frag.hpp` `tmem_frg` with `N_SM = 2`
- NVIDIA CUTLASS (`include/cute/atom/mma_traits_sm100.hpp`, `SM100_MMA_*_2x1SM_SS` `ALayout` and
    `BLayout`); PTX ISA 9.5 §9.7.18.5.1
- §9.7.18.5.2 (the pair has an even and an odd CTA; the peer of one is the other) and §9.7.18.10 (B:
    "in Shared Memory of the current CTA and optionally in peer CTA"
- §9.7.18.10.4.2: "The 6-bit and 4-bit floating point types have different packing format
    requirements for different MMA kinds in both Tensor memory and Shared memory."
- §9.7.18.10.4.4 (the packing of `kind::mxf8f6f4` in shared memory)
- §9.7.18.9.1.1 and §9.7.18.9.1.2 (the 16-element chunks with padding)

Why it is not spec text: (1) The layouts are given by figures only, with no textual coordinate map.
  (2) The `cta_group::2` layouts are also given by figures only. The text does not say which CTA of
  the pair holds the first half of the rows of D, and it does not say how an 8-word
  `disable-output-lane` mask maps onto the two CTAs' lanes. (3) The sentence of §9.7.18.10.5 on the
  same Tensor Memory lane alignment states that A shares the datapath organization of D. It does not
  say that a row of A is on the lane of the same row of D. The text states the packing of K elements
  into 32-bit words for 8-bit containers only (§9.7.18.10.4.3), and it does not say which CTA of a
  pair holds which rows of A. (4) With `.ws` and M < 128 (Layouts E and G) the ISA does not say
  which lane's A a column block uses. (5) The text says that the pair's two CTAs take part and that
  an operand may be in the peer CTA's shared memory. It does not say along which dimension an
  operand is split or which half lies in which CTA of the pair. (6) Table 67 gives the swizzle atom
  (8 x 4 elements of 128 bits, M/N-major only; Figure 225), and the text states neither the strides
  of atoms nor the XOR in the MMA's address space. For 4-byte elements Table 65 lists "All swizzling
  modes" for K-major, and Table 67 has no K-major atom of this mode, so K-major with it is undefined
  here. (7) §9.7.18.10.4 states the packing for `kind::mxf8f6f4`, `kind::mxf4` and `kind::mxf4nvf4`
  only; `kind::f8f6f4` takes the same element types and the model gives it the `kind::mxf8f6f4`
  packing.

Evidence: (1) NVIDIA CUTLASS (commit e406c186) `include/cute/atom/mma_traits_sm100.hpp` gives the
  same maps (`tmem_frg`, `tmem_frg_ws`). (3) The figures and CuTe layouts of PTX ISA §9.7.18.
  CUTLASS `SM100_MMA_F16BF16_2x1SM_TS` (commit e406c186) lays A out with
  `tmem_frg_2sm<a_type, a_type, TmemAllocMode::Duplicated>`, whose allocation for 128 rows per CTA
  is that of D (its source comment: with 128 rows all datapaths are occupied and the allocation mode
  changes nothing) and whose `ALayout` gives SM `v` rows `v * M / 2` onward. Layout D is checked
  against a CPU reference on a B200 by `Kernels/TcGemm/run_tc_gemm.cu`, and the A packing
  (kind::i8, M = 128, 64 and 32) by `Tools/probes/tcgen05_ws_ts_i8.ptx` (MMA reading A written with
  `tcgen05.st`). The 16-bit packing and the `cta_group::2` row split rest on CUTLASS alone; no probe
  checks them. (4) On a B200 each D lane reads its own copy: output `(i, j)` uses lane
  `i + M (j / (N M / 128))`. In `Tools/probes/tcgen05_ws_ts_i8.ptx` (A in Tensor Memory, N = 64,
  decoys in every lane but row `i`'s), the lane of row `i` alone mismatched 2048 of 4096 (M = 64)
  and 1536 of 2048 (M = 32) outputs, and the per-lane model none (two seeds each); M = 128 cannot
  distinguish them. Layout F for A in Tensor Memory follows from the same alignment rule.
  (6) CUTLASS `make_umma_desc` (LayoutType::B128_BASE32B above, local checkout of
  include/cute/arch/mma_sm100_desc.hpp and `Layout_MN_SW128_32B_Atom` in
  include/cute/atom/mma_traits_sm100.hpp). (7) The manual states the shared-memory packing for
  `kind::mxf8f6f4` in §9.7.18.10.4.4 with Figures 207 and 208, and the Tensor Memory containers in
  Table 66 of §9.7.18.10.4.3. CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) gives
  `kind::f8f6f4` the same 32-byte row: it maps 6- and 4-bit inputs to the `*_unpacksmem_t` types
  (`sm1xx_kernel_input_element_to_mma_input_element` in
  include/cutlass/gemm/collective/builders/sm1xx_common.inl), allocates them as `uint8_t` in shared
  memory (sm100_umma_builder.inl), loads them with the TMA types
  `CU_TENSOR_MAP_DATA_TYPE_16U6_ALIGN16B` and `CU_TENSOR_MAP_DATA_TYPE_16U4_ALIGN16B` (16 packed
  elements, then a gap, in every 16 bytes) and fixes K = 32 in `MMA_Traits<SM100_MMA_F8F6F4_SS>`.
  The hardware probe txverify-archive/core-coverage/probes/tcgen05_f8f6f4/ runs an M = 128, N = 16
  MMA for each type as A and as B, with the padding bytes set to 0xFF and to random values, and
  compares D with the product of the elements packed from bit 0 up. It ran on a B200 on 2026-11-16
  and agreed in all 22 cases, with either padding.

Direction: reading

Effect: The maps of readings 1 to 3 decide which Tensor Memory cells an MMA writes and which cells a
  later `tcgen05.ld` or `tcgen05.st` reads as which D element, and the A bytes an MMA reads from
  Tensor Memory. If the hardware maps differ, the proven results differ. The A elements of each D
  lane (reading 4) are fixed by the lane map; if the hardware lanes read other copies, the products
  differ from the ones proven. A different operand split of a CTA pair (reading 5) would make the
  value of D a different function of the shared bytes. The shared byte of each operand element in
  the 32-byte-atomic mode (reading 6) is fixed by its layout; if the hardware layout differs, the
  operand bytes an MMA reads differ from the ones proven. The bytes an MMA of `kind::f8f6f4` reads,
  and so its conflicts with other accesses, are fixed by the footprint of reading 7; if the hardware
  reads another footprint, a write the model orders after the read may change the operand. Disclosed
  by every kernel whose statement names `Op.tcMma`: FlashAttn4Fwd, FlashMlaSparseDecodeH64,
  Fp16Gemm8192, InklingRelDecode, TcGemm.
-/
/-- A 32-bit word of Tensor Memory: one lane and one column of the Tensor Memory of one CTA. -/
structure Cell where
  /-- The CTA whose Tensor Memory holds the word. -/
  cta : Nat
  /-- The lane, from 0 to 127. -/
  lane : Nat
  /-- The column. -/
  column : Nat
  deriving DecidableEq, Repr

/-- Layout F (M = 64, cta_group::1, without `.ws`): the 64 rows use half of each datapath
subpartition. -/
def halfDatapath (d : Descriptor) : Bool :=
  d.group = .one ∧ d.m = 64 ∧ d.ws = false

/-- Column blocks of a 2x2 or 1x4 datapath organization: `128 / r` for `r` rows per CTA. -/
def columnBlocks (d : Descriptor) : Nat := 128 / (d.m / d.group.size)

/-- Datapath lane alignment of the D address (§9.7.18.10.5 table). -/
def LaneAligned (d : Descriptor) (lane : Nat) : Prop :=
  lane = 0 ∨ (halfDatapath d = true ∧ lane = 16)

instance laneAlignedDecidable (d : Descriptor) (lane : Nat) : Decidable (LaneAligned d lane) := by
  unfold LaneAligned
  infer_instance

/-- The number of columns that D occupies from the column of its address. -/
def resultColumns (d : Descriptor) : Nat :=
  if d.m = 128 * d.group.size ∨ halfDatapath d = true then d.n else d.n / columnBlocks d

/-- The Tensor Memory cell of element (`row`, `col`) of D for an MMA with operands `s` and D
address `base`, by the layout of its shape (§9.7.18.10.5); `none` for an invalid shape, a lane
field that is not a permitted alignment, a coordinate out of range or columns past the 512th. -/
def resultCell (s : OperandSpec) (base row col : Nat) : Option Cell :=
  let d := s.descriptor
  let lane0 := base / 2 ^ 16
  let col0 := base % 2 ^ 16
  if Valid d ∧ LaneAligned d lane0 ∧ row < d.m ∧ col < d.n ∧ col0 + resultColumns d ≤ 512 then
    let halfM := d.m / d.group.size
    let cta := if row < halfM then s.lowCta else s.highCta
    if d.m = 128 * d.group.size then some ⟨cta, row % 128, col0 + col⟩
    else if halfDatapath d then
      some ⟨cta, lane0 + row % halfM % 16 + 32 * (row % halfM / 16), col0 + col⟩
    else
      let r := d.m / d.group.size
      some ⟨cta, row % r + r * (col / (d.n / columnBlocks d)), col0 + col % (d.n / columnBlocks d)⟩
  else none

/-- Byte `index` of the A read that comes from Tensor Memory, as its cell and the byte's
position in that word. A in Tensor Memory (`[a-tmem]`, EXT-TCFIG): A row `q` of the read
(`Operand.rows`) uses the datapath lane of that D row and its bytes fill 32-bit columns in
order. Represented for the full-datapath layouts (M = 128 per CTA, lane field 0), Layout F
(lane field 0 or 16: row `r` is lane `field + r % 16 + 32 (r / 16)`) and, with `.ws` and
M < 128 (Layouts E, G), one row per D lane: row `q < 128` is lane `q` (EXT-TCFIG). -/
def aCell (s : OperandSpec) (index : Nat) : Option (Cell × Nat) :=
  let d := s.descriptor
  let bytes := d.kind.k * d.kind.width
  s.aTmem.bind fun address =>
    let row := index / bytes
    let field := address / 2 ^ 16
    if Valid d ∧ row < Operand.rows .a d ∧ address % 2 ^ 16 + (bytes + 3) / 4 ≤ 512 ∧
        ((d.m = 128 * d.group.size ∧ field = 0) ∨ (halfDatapath d ∧ (field = 0 ∨ field = 16)) ∨
          (d.ws ∧ d.m < 128 ∧ field = 0)) then
      some (⟨if row < d.m / d.group.size then s.lowCta else s.highCta,
        if halfDatapath d then field + row % 16 + 32 * (row / 16) else row % 128,
        address % 2 ^ 16 + index % bytes / 4⟩, index % bytes % 4)
    else none

/-- The A row (of the A read) of output `(row, col)`: its D lane with `.ws` and
M < 128 (Layouts E, G: EXT-TCFIG), otherwise the row. -/
def operandRow (d : Descriptor) (row col : Nat) : Nat :=
  if d.ws ∧ d.m < 128 then row + d.m * (col / (d.n / columnBlocks d)) else row

/-- The disable-output-lane mask has four 32-bit words per CTA of the group. -/
def OutputMaskValid (group : CtaGroup) (mask : List Nat) : Prop :=
  mask.length = 4 * group.size ∧ ∀ word ∈ mask, word < 2 ^ 32

instance outputMaskValidDecidable (group : CtaGroup) (mask : List Nat) :
    Decidable (OutputMaskValid group mask) := by
  unfold OutputMaskValid
  infer_instance

/-- The cell that element (`row`, `col`) of D is written to: its result cell, unless the bit of
its lane in the disable-output-lane mask is 1. The mask numbers 128 lanes per CTA of the group,
the first CTA's lanes first. -/
def writeCell (s : OperandSpec) (base : Nat) (mask : List Nat) (row col : Nat) : Option Cell := do
  let d := s.descriptor
  if ¬OutputMaskValid d.group mask then none else do
    let cell ← resultCell s base row col
    let lane := (row / (d.m / d.group.size)) * 128 + cell.lane
    let word ← mask[lane / 32]?
    if word / 2 ^ (lane % 32) % 2 = 0 then some cell else none

end PTX.TcMma
