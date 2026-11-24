-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

namespace PTX

/-! ## THREAD-TC-DATA-ADDRESS — Tensor Memory cells of tcgen05.ld and tcgen05.st
Statement: Register j of thread lane l of a `tcgen05.ld` or `tcgen05.st` is the Tensor Memory cell
  that the fragment of the shape assigns to (l, j), offset by the lane and column of the base
  address of the access, inside the 32-lane chunk of the issuing warp's position in its warpgroup.
  An address whose lanes would leave that chunk, or a `.16x32bx2` offset that would leave the column
  field, has no rule.

Defs: laneBase, tmemLaneFieldOk, TcShape.base, TcShape.laneIn, TcShape.columnIn, TcShape.splitOk,
  tcDataAddressOk, chunkOffset, tcDataCell

Source:
- §9.7.18.1.1 (the address layout puts the lane index in bits 31 to 16)
- §9.7.18.8.1 (warp w of a warpgroup accesses lanes 32 w to 32 w + 31, and a lane is accessed by a
    single warp)
- §9.7.18.2.3.1.1 to §9.7.18.2.3.1.5: "A warp executing tcgen05{.ld,.st}.32x32b will access 32 lanes
    of the Tensor Memory."
- §9.7.18.2.3.1.1 to §9.7.18.2.3.1.5 (the `.16x64b`, `.16x128b`, `.16x256b` and `.16x32bx2` accesses
    cover 16 lanes)
- Figures 186 to 190 (which register of which thread is which cell; figures only,
    EXT-TMEM-LANE-FIELD)
- §9.7.18.8.3 and §9.7.18.8.4: "The shape .16x32bx2 performs two accesses into Tensor Memory of the
    shape .16x32b . The base address of the first access is specified by taddr and the base address
    of the second access is specified by taddr+immHalfSplitoff , where immHalfSplitoff is an
    immediate argument."
- EXT-TMEM-LANE-FIELD

Direction: reading

Applies: Represented tcgen05.ld and tcgen05.st of every shape (`TcShape`)

Premises: The address lane field keeps every access of the shape inside the issuing warp's chunk
  (`tmemLaneFieldOk`, EXT-TMEM-LANE-FIELD); a `.16x32bx2` half-split offset stays in the column
  field (`TcShape.splitOk`, EXT-TMEM-LANE-FIELD).

Effect: One address adapter for issue and for every load, store, value, conflict, lifetime and
  allocation query (`tcDataCell`). Register `j` of thread lane `l` of warp `w` of its warpgroup is
  the cell at lane `32 w + o + TcShape.laneIn l j` and column `c + TcShape.columnIn l j`, where `o`
  and `c` are the chunk offset and the column field of the base address of the access the thread
  takes part in (`TcShape.base`). The fragment of each shape, with `k = j / regs` the repetition
  (`.num` index) and `r = j % regs` the register within it (`TcShape.regs`), as Figures 186 to 190
  draw it:
  | shape | lane in the access | column from the base |
  | --- | --- | --- |
  | `.32x32b` | `l` | `k` |
  | `.16x64b` | `l / 4 + 8 (l % 2)` | `2 k + (l / 2) % 2` |
  | `.16x128b` | `l / 4 + 8 r` | `4 k + l % 4` |
  | `.16x256b` | `l / 4 + 8 (r / 2)` | `8 k + 2 (l % 4) + r % 2` |
  | `.16x32bx2` | `l % 16` | `k` |
  For `.16x32bx2` thread lanes 0 to 15 take part in the first access (base `taddr`) and lanes 16 to
  31 in the second (base `taddr + immHalfSplitoff`). For every shape, distinct registers of one
  thread are distinct cells. `tmemLaneFieldOk L g field n` accepts the lane field of an access of
  `n ≥ 1` lanes when it is an offset within the warp's chunk (`field + n ≤ 32`, first lane
  `laneBase + field`) or an absolute lane inside the chunk (`laneBase ≤ field` and
  `field + n ≤ laneBase + 32`, first lane `field`). For warp 0 the two coincide; for a warp `w > 0`
  they are disjoint because `n ≥ 1` (`tmemLaneField_disjoint`), so the first lane is determined. In
  both readings the first lane is `laneBase + field % 32` (`laneBase` is a multiple of 32), at most
  `laneBase + 32 - n`; `chunkOffset` is that offset, bounded by `32 - n` so that the adapter is
  total. A `.32x32b` access covers 32 lanes, so its first lane is `laneBase`. Column allocation,
  conflicts and the collective's equal-operand requirement are separate rules
  (ERR-TMEM-ACCESS-LIFETIME, ERR-TMEM-RACE, ERR-ALIGNED-MISMATCH): a column past the allocation is
  an unsafe access, and two lanes of one `.16x32bx2` store that write one cell are an unordered
  write pair.

### EXT-TMEM-LANE-FIELD — the layout readings of tcgen05.ld and tcgen05.st

Statement: The model makes four readings of `tcgen05.ld` and `tcgen05.st`. (1) The register
  fragments of Figures 186 to 190 are explicit coordinate maps, the table of
  THREAD-TC-DATA-ADDRESS, with each further `.num` repetition of a fragment at the next columns.
  Thread lane `l`, register `j` of repetition `k = j / regs` and `r = j % regs` is lane `l` and
  column `k` for `.32x32b`; lane `l / 4 + 8 (l % 2)` and column `2 k + (l / 2) % 2` for `.16x64b`;
  lane `l / 4 + 8 r` and column `4 k + l % 4` for `.16x128b`; lane `l / 4 + 8 (r / 2)` and column
  `8 k + 2 (l % 4) + r % 2` for `.16x256b`; lane `l % 16` and column `k` of its half's access for
  `.16x32bx2`. (2) The lane field of a `tcgen05.ld` or `tcgen05.st` address is accepted either as an
  offset into the issuing warp's 32-lane chunk or as an absolute lane inside that chunk, provided
  every accessed lane stays in the chunk; any other lane field has no rule. For an access of
  `n ≥ 1` lanes issued by warp `w` of a warpgroup, the address lane field `f` is accepted when it is
  an offset into the warp's chunk (`f + n ≤ 32`, lanes `32 w + f` onward) or an absolute lane of
  that chunk (`32 w ≤ f`, `f + n ≤ 32 w + 32`, lanes `f` onward). (3) The second access of a
  `.16x32bx2` load or store starts `immHalfSplitoff` columns after the first, on the same 16 lanes,
  and thread lanes 16 to 31 take part in it as its lanes 0 to 15. The second access has the base
  address `taddr + immHalfSplitoff`, a Tensor Memory address read with its lane and column fields
  (§9.7.18.1.1). The model accepts only an offset that stays in the column field of `taddr`
  (`taddr % 2^16 + immHalfSplitoff < 2^16`), so both accesses have the lane field of `taddr` and
  cover the same 16 lanes. Any other offset is forbidden (no rule). (4) For
  `tcgen05.ld.<shape>.pack::16b` and `tcgen05.st.<shape>.unpack::16b` of a single-access shape,
  register `j` of thread lane `l` uses the lane of the unpacked fragment and the columns `c + 2 x`
  (low half of the register) and `c + 2 x + 1` (high half), with `x` the unpacked column offset. The
  16-bit element in a column is the column's low 16 bits. An unpacking store leaves the high 16 bits
  of the written words unknown.

Source:
- §9.7.18.2.3.1.1 to §9.7.18.2.3.1.5: "A warp executing tcgen05{.ld,.st}.32x32b will access 32 lanes
    of the Tensor Memory."
- §9.7.18.1.1 (the address layout puts the lane index in bits 31 to 16) and §9.7.18.8.1: "A lane of
    the Tensor Memory can be accessed by a single warp in the warpgroup. … ID of the warp within the
    warpgroup Accessible Lanes 0 0-31 1 32-63 2 64-95 3 96-127"
- §9.7.18.8.3: "The base address of the first access is specified by taddr and the base address of
    the second access is specified by taddr+immHalfSplitoff , where immHalfSplitoff is an immediate
    argument."
- §9.7.18.2.3.1.5: "A warp executing tcgen05{.ld,.st}.16x32bx2 will access 16 lanes of the Tensor
    Memory."
- Figure 190 (which draws threads T16 to T31 from the top of the second access, whose start the
    figure labels as the base address plus the immediate)
- §9.7.18.8.2 to §9.7.18.8.4 and Figure 196

Why it is not spec text: (1) The fragments are given by Figures 186 to 190 only, with no textual
  coordinate map. The figures draw `.x2` for `.32x32b` and `.16x64b`, and only `.x1` followed by "…"
  for the other shapes. The model reads every further repetition as the next `regs` registers at the
  next columns, as the drawn `.x2` cases do. (2) The text gives the lanes each warp may access. It
  does not say whether the address lane field is an absolute lane or an offset into the warp's
  chunk. (3) The text does not say how the immediate combines with the lane and column fields, and
  Figure 190 draws the second access at lanes 16 to 31 while the text says the warp accesses 16
  lanes; the model takes the reading on which both hold for the offsets it accepts, and does not
  decide the others. That thread `16 + i` is lane `i` of the second access is read from the figure.
  (4) The text says that two 16-bit elements of adjacent columns form one register. It does not say
  which 16 bits of a column hold the element, which half of the register comes from the lower
  column, or where the columns of a multi-register fragment go. Figure 196 draws the `.16x128b`
  fragment with each register occupying two adjacent 16-bit columns, the register of thread `T0` in
  the first two, and the next thread's register in the next two; it does not mark the bit halves.

Evidence: (1) CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23),
  include/cute/atom/copy_traits_sm100.hpp, gives the same maps (`SM100_TMEM_LOAD_32dp32b1x`,
  `_16dp64b1x`, `_16dp128b1x`, `_16dp256b1x`, `_16dp32b1x`, and their `2x` forms). On a B200, the
  unpacked control lines of the probe txverify-archive/core-coverage/probes/tcgen05_pack16/ agreed
  with these maps for `.x1`, `.x2` and `.x4` of the four shapes. (2)
  https://docs.nvidia.com/cuda/parallel-thread-execution/#tcgen05-tensor-memory-ld-st-access-restrictions
  https://docs.nvidia.com/cuda/parallel-thread-execution/_images/tcgen05-mma-fragment-3232b.png
  https://docs.nvidia.com/cutlass/4.8.0/media/docs/pythonDSL/primitives.html#cutlass.experimental.primitives.tcgen05_ld
  (3) NVIDIA CUTLASS 4.1.0 `include/cute/arch/copy_sm100.hpp` issues
  `tcgen05.ld.sync.aligned.16x32bx2.x<n>.b32` with `immHalfSplitoff = n`, and its
  `include/cute/atom/copy_traits_sm100.hpp` layout `SM100_TMEM_LOAD_16dp32b1x` puts thread `t` at
  lane `t % 16`, 32-bit column `t / 16`.
  https://docs.nvidia.com/cuda/parallel-thread-execution/_images/tcgen05-mma-fragment-1632b2.png
  (4) (manual) Figure 196 (`_images/tcgen05-ld-st-pack-unpack.png`): a register of the `.16x128b`
  fragment maps to two adjacent 16-bit columns, in fragment order. (CUTLASS) CUTLASS
  (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23), include/cute/atom/copy_traits_sm100.hpp,
  `Copy_Traits<SM100_TMEM_LOAD_32dp32b1x_16b>` and the other `_16b` atoms:
  `ValID = Shape<Shape<_16, X>, lanes>, Stride<Stride<_1, _32>, DP_b>`, so logical bit `i` of a lane
  is Tensor Memory bit `32 (i / 16) + i % 16` (16-bit chunk `k` in the low half of column `k`), with
  the register map (`DstLayout`) of the unpacked atom of the same logical width; the
  `SM100_TMEM_STORE_*_16b` atoms use the same layouts. (B200) probe
  `txverify-archive/core-coverage/probes/tcgen05_pack16/`, which compares packed loads and unpacking
  stores of every single-access shape with this map. It ran on a B200 on 2026-11-16 and agreed for
  `.x1`, `.x2` and `.x4` of every shape. It also prints what the high 16 bits of the words an
  unpacking store writes hold, which the model leaves unknown; they were 0 in every case.

Direction: reading

Effect: These maps decide which Tensor Memory cells a `tcgen05.ld` or `tcgen05.st` reads or writes
  as which register. If the hardware maps differ, the proven results differ. The lane field is a
  reading of how hardware interprets the field, and real kernels use both encodings. If hardware
  used only one interpretation, a program using the other would access another warp's lanes and be
  wrongly accepted. If the hardware placed the second access of a `.16x32bx2` elsewhere for a column
  offset, the cells the upper half-warp loads and stores, and so values and conflicts, would differ
  from the model's. If the hardware placed the halves or the columns of a packed access otherwise,
  the values a packed load returns and the cells an unpacking store writes would differ from the
  model's, and so would every value and conflict computed from them. Disclosed by every kernel whose
  statement names `Op.tcLd` or `Op.tcSt`: FlashAttn4Fwd, FlashMlaSparseDecodeH64, Fp16Gemm8192,
  InklingRelDecode, TcGemm.

Review: CUTLASS and TcGemm fill the absolute lane `32 w`; Fp16Gemm8192 fills 0 in every warp.
-/

/-- Physical first TMEM lane accessible by the issuing warp. -/
def laneBase (L : Launch) (g : Nat) : Nat := g % L.block / 32 % 4 * 32

/-- An access of `n ≥ 1` lanes with address lane field `field` by thread `g` stays in its warp's
chunk, the field read as an offset into the chunk or as an absolute lane (EXT-TMEM-LANE-FIELD). -/
def tmemLaneFieldOk (L : Launch) (g field n : Nat) : Bool :=
  decide (0 < n) && (decide (field + n ≤ 32) ||
    (decide (laneBase L g ≤ field) && decide (field + n ≤ laneBase L g + 32)))

/-- The base address of the access thread lane `l` takes part in: `taddr`, or, for lanes 16 to
31 of `.16x32bx2`, the second access's `taddr + immHalfSplitoff` (EXT-TMEM-LANE-FIELD). -/
def TcShape.base : TcShape → Nat → Nat → Nat
  | .s16x32bx2 off, a, l => if l < 16 then a else a + off
  | .packed16 s, a, l => s.base a l
  | _, a, _ => a

/-- The lane, within its access, of register `j` of thread lane `l` (Figures 186 to 190). -/
def TcShape.laneIn : TcShape → Nat → Nat → Nat
  | .s32x32b, l, _ => l
  | .s16x64b, l, _ => l / 4 + 8 * (l % 2)
  | .s16x128b, l, j => l / 4 + 8 * (j % 2)
  | .s16x256b, l, j => l / 4 + 8 * (j % 4 / 2)
  | .s16x32bx2 _, l, _ => l % 16
  | .packed16 s, l, j => s.laneIn l (j / 2)

/-- The column, from its access's base column, of register `j` of thread lane `l` (Figures 186
to 190). -/
def TcShape.columnIn : TcShape → Nat → Nat → Nat
  | .s32x32b, _, j => j
  | .s16x64b, l, j => 2 * j + l / 2 % 2
  | .s16x128b, l, j => 4 * (j / 2) + l % 4
  | .s16x256b, l, j => 8 * (j / 4) + 2 * (l % 4) + j % 2
  | .s16x32bx2 _, _, j => j
  | .packed16 s, l, j => 2 * s.columnIn l (j / 2) + j % 2

/-- A `.16x32bx2` half-split offset stays in the column field of `address`
(EXT-TMEM-LANE-FIELD); the other shapes have one access. A packed shape has a rule only over a
single-access shape (THREAD-TC-PACK16). -/
def TcShape.splitOk : TcShape → Nat → Bool
  | .s16x32bx2 off, a => decide (a % 2 ^ 16 + off < 2 ^ 16)
  | .packed16 s, _ => s.singleAccess
  | _, _ => true

/-- Scope of the address `address` of a load or store of shape `s` by thread `g`: a supported
half-split offset, and a lane field that keeps the shape's lanes in the warp's chunk. Both
accesses of `.16x32bx2` have the lane field of `address`. -/
def tcDataAddressOk (L : Launch) (g : Nat) (s : TcShape) (address : Nat) : Bool :=
  s.splitOk address && tmemLaneFieldOk L g (address / 2 ^ 16) s.lanes

/-- The first lane, within the warp's chunk, of an access of `n` lanes with lane field `field`:
`field % 32` under either reading of EXT-TMEM-LANE-FIELD, bounded by `32 - n`. -/
def chunkOffset (field n : Nat) : Nat := min (field % 32) (32 - n)

/-- Register slot `j` of a load or store of shape `s` at `address` by thread `g`, in its issuing
CTA. The issue rule establishes `tcDataAddressOk`; this total adapter does not itself assert that
an arbitrary raw address can issue an instruction. -/
def tcDataCell (L : Launch) (g : Nat) (s : TcShape) (address j : Nat) : TcMma.Cell :=
  ⟨g / L.block,
    laneBase L g + chunkOffset (s.base address (laneOf L g) / 2 ^ 16) s.lanes +
      s.laneIn (laneOf L g) j,
    s.base address (laneOf L g) % 2 ^ 16 + s.columnIn (laneOf L g) j⟩

end PTX
