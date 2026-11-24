-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Isa.Matrix

@[expose] public section

/-!
# Fragment layouts of the warp-level matrix instructions

Which lane, register and byte of a warp holds which element of a matrix that `ldmatrix`,
`stmatrix`, `movmatrix`, `mma` or `mma.sp` moves or multiplies.

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

/-! ## THREAD-MATRIX-LAYOUT — fragment layouts

Statement: Each lane of a warp holds fixed elements of the matrices of a warp-level matrix
  instruction. For `mma` and `mma.sp` the row and column of each fragment element follow the
  manual's formulas, and for `ldmatrix`, `stmatrix`, `movmatrix`, the sparse metadata and the sparse
  B fragments that only the manual's figures give they follow the figures. The registers of a lane
  hold their elements from the low bits up.

Defs: MatrixMove.source, transposeSource, MmaSpec.perReg, MmaSpec.fragA, MmaSpec.fragB,
  MmaSpec.fragCD, MmaSpec.metaCols, MmaSpec.metaLoc, MmaSpec.sparseCol

Source:
- §9.7.16.5.1: "A warp executing mma.m8n8k4 with .f16 floating point type will compute 4 MMA
    operations of shape .m8n8k4"
- §9.7.16.5.1: "MMA computation 1 Threads with %laneid 0-3 (low group) and 16-19 (high group)"
- §9.7.16.5.1: "row = % laneid % 4 if % laneid < 16 ( % laneid % 4 ) + 4 otherwise col = i for ai
    where i = { 0 ,.., 3 }"
- §9.7.16.5.1: "row = X if % laneid < 16 X + 4 otherwise where X = ( % laneid & 0b1 ) + ( i & 0b10 )
    for ci where i = { 0 ,.., 7 } col = ( i & 0b100 ) + ( % laneid & 0b10 ) + ( i & 0b1 )"
- §9.7.16.5.2 to §9.7.16.5.13: "groupID = % laneid >> 2 threadID_in_group = % laneid % 4"
- §9.7.16.5.8: "row = groupID for ai where 0 <= i < 2 || 4 <= i < 6 groupID + 8 Otherwise col = (
    threadID_in_group * 2 ) + ( i & 0x1 ) for ai where i < 4 ( threadID_in_group * 2 ) + ( i & 0x1 )
    + 8 for ai where i >= 4"
- §9.7.16.5.8: "row = groupID for ci where i < 2 groupID + 8 for ci where i >= 2 col = (
    threadID_in_group * 2 ) + ( i & 0x1 ) for ci where i = { 0 ,.., 3 }"
- §9.7.16.5.10: "row = ( threadID_in_group * 4 ) + ( i & 0x3 ) for bi where i < 4 (
    threadID_in_group * 4 ) + ( i & 0x3 ) + 16 for bi where i >= 4 col = groupID"
- §9.7.16.5.14: "The registers in each thread hold a fragment of matrix as described in Matrix
    multiply-accumulate operation using mma instruction ."
- §9.7.16.5.15: "Each thread in a warp loads fragments of a row, with thread 0 receiving the first
    fragment in its register r , and so on."
- §9.7.16.5.15: "The eight addresses required for each matrix are provided by eight threads"
- §9.7.16.5.15: "Optional qualifier .trans indicates that the matrix is loaded in column-major
    format."
- §9.7.16.5.16: "Each element in the source operand r is of type .b32 and contains four 8 bit
    elements e0 , e1 , e2 , e3 with e0 and e3 containing the LSB and MSB respectively of register r
    ."
- §9.7.16.5.17: "Each thread in a warp holds a fragment of a column of the result matrix, with
    thread 0 holding the first fragment in register d , and so on."
- §9.7.16.6.2: "Tk: [m..n] present in cell [x][y..z] indicates that bits m through n (with m being
    higher) in the metadata operand of thread with %laneid=k contains the indices of the non-zero
    elements from the chunk [x][y]..[x][z] of matrix A."
- §9.7.16.6.2: "col = [ firstcol ... lastcol ] // As per the mapping of non-zero elements"
- §9.7.16.6.3: "Instruction mma.sp::ordered_metadata requires the indices in the sparsity metadata
    to be sorted in an increasing order starting from LSB, otherwise behavior is undefined."
- EXT-MATRIX-FIGURES
- EXT-MMA-SPARSE-FIGURES
- EXT-MMA-FRAGMENTS

Direction: reading

Applies: The supported forms of THREAD-MATRIX and THREAD-MMA-SYNC

Premises: None.

Effect: Element positions used by DEP-WARP-MATRIX and DEP-WARP-MMA. The notation is: lane `l` has
  `g = l / 4` (groupID) and `t = l % 4` (threadID_in_group). A register of an operand with elements
  of `w` bits holds `32 / w` elements (one `.f64` element per 64-bit register), and element `i` of a
  lane's fragment is at bits `i * w` of the concatenated registers, register 0 first: the manual
  numbers fragment elements from low to high. `MatrixMove.source m l r b` is the row (the lane that
  supplied its address) and the byte in that row of byte `b` of register `r` of lane `l`. Without
  `.trans`, lane `l` holds bytes `4t` to `4t + 3` of row `g` of each `.m8n8` matrix. With `.trans`
  the register holds the transposed matrix: the element in row `i` and column `j` of the figure is
  element `i` of memory row `j`. `transposeSource l b` is the lane and byte of the `movmatrix`
  source that byte `b` of lane `l`'s destination holds. `MmaSpec.fragA s l i`, `fragB` and `fragCD`
  give `(q, row, col)` of element `i` of lane `l`'s fragment, where `q` is the computation (0 to 3
  for the four-MMA form, 0 otherwise). Every other shape follows one formula per operand, which
  agrees with every formula of §9.7.16.5.2 to §9.7.16.5.13: for A, register `r` of `e` elements has
  row `g + 8 (r mod 2)` and column `e t + (i mod e) + 4 e (r / 2)`; for B, register `r` has row
  `4 e r + e t + (i mod e)` and column `g`; for C and D, element `i` has row `g + 8 (i / 2)` and
  column `2 t + (i mod 2)`. The A operand of `mma.sp` holds the non-zero elements of the compressed
  `m × k/2` matrix in the layout of the dense shape with `k/2` columns, which is what the formulas
  of §9.7.16.6.2 give for `[firstcol ... lastcol]`. `MmaSpec.metaCols` is the number of columns of A
  one 4-bit metadata field covers, `MmaSpec.metaLoc` the lane and bit of the field of a row and
  chunk, and `MmaSpec.sparseCol` the column of A that a compressed element has under the field: for
  16- and 8-bit types two 2-bit indices select two of four columns, for `.tf32` the field `0b0100`
  selects the first and `0b1110` the second of two columns, and for 4-bit types two 2-bit indices
  select two of four pairs of columns; the first compressed element of a chunk takes the index in
  the low bits.

### EXT-MATRIX-FIGURES — the layouts and the row accesses of ldmatrix, stmatrix and movmatrix

Statement: The model makes two readings of `ldmatrix`, `stmatrix` and `movmatrix`. (1) The fragment
  layouts are those of the manual's figures, a register holds its elements from the low bits up,
  `.trans` exchanges the rows and columns of the figure, and a 16-row matrix takes its addresses
  from 16 consecutive threads and its two registers from consecutive register positions.
  `MatrixMove.source` and `transposeSource`: for `.m8n8` lane `l` holds row `l / 4`, bytes `4 (l mod
  4)` to `4 (l mod 4) + 3` (Figures 107 and 110); for `.m16n16` register `2 k + h` of lane `l` holds
  byte `4 (l mod 4) + b` of row `8 h + l / 4` of matrix `k` in its byte `b` (Figure 108), whose rows
  are supplied by threads `16 k` to `16 k + 15`; for `.m16n8` element `e` of lane `l` is in row `l /
  4 + 8 (e / 2)` and column `2 (l mod 4) + e mod 2` (Figure 111); with `.trans` the element in row
  `i` and column `j` of the figure is element `i` of the memory row whose address is the `j`-th; the
  `movmatrix` source of lane `l` is row `l / 4`, columns `2 (l mod 4)` and `2 (l mod 4) + 1`, and
  its result is column `l / 4`, rows `2 (l mod 4)` and `2 (l mod 4) + 1` (Figures 112 and 113); the
  element with the smaller row or column index is in the low half of the register. (2) The 16 bytes
  of a matrix row of `ldmatrix` or `stmatrix` are read or written by the thread that supplies the
  row's address, as one weak access of that thread. `matrixMoveTmpl` gives each row-address thread
  one `.read` (`ldmatrix`) or `.write` (`stmatrix`) of 16 bytes at its address, and no other thread
  accesses memory.

Source:
- §9.7.16.5.15 to §9.7.16.5.17, as quoted in THREAD-MATRIX-LAYOUT, and Figures 107 to 113 (images of
    the HTML manual)
- §9.7.16.5.15 and §9.7.16.5.16, as quoted in THREAD-MATRIX

Why it is not spec text: (1) The layouts are drawn in figures; the text says which thread receives
  the first fragment and how many elements a register holds, and that `.trans` loads in column-major
  format, without giving positions. The address table names eight threads per matrix, which does not
  cover the sixteen rows of an `.m16n16` matrix, and the text does not say which of the four
  registers of `.m16n16.x2` hold which matrix. (2) The text says that the instruction is a weak
  memory operation and that a group of four threads loads or stores 16 bytes, but not which
  thread's operation each access is, which decides the program order and the base causality edges
  the memory model gives it.

Evidence: (1) Manual: §9.7.16.5.15 to §9.7.16.5.17 and Figures 107 to 113, as above. CUTLASS
  (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23): the layouts of `SM75_U32x{1,2,4}_LDSM_N`,
  `SM75_U16x{2,4,8}_LDSM_T`, `SM90_U32x{1,2,4}_STSM_N`, `SM90_U16x{2,4,8}_STSM_T`,
  `SM100_U8x8_LDSM_T`, `SM100_U8x16_LDSM_T` (with the byte regrouping their `copy` applies),
  `SM100_SU4_DU8x16_x1_LDSM_N`, `SM100_SU6_DU8x16_x1_LDSM_N` and `SM100_U8x{4,8,16}_STSM_T` agree
  with `MatrixMove.source` for every register byte
  (txverify-archive/core-coverage/probes/cutlass_check.py); `SM75_U32x1_MOVM_T` gives no independent
  `movmatrix` map. Hardware probe:
  txverify-archive/core-coverage/probes/matrix_move/matrix_move.cu covers every `ldmatrix`,
  `stmatrix` and `movmatrix` form above. It ran on a B200 on 2026-11-16 and agreed with the model in
  every form. (2) The manual's address table assigns the rows of each matrix to threads, as quoted
  in THREAD-MATRIX. CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) describes the same
  assignment in the SrcLayout of `SM75_U32x{1,2,4}_LDSM_N`
  (include/cute/atom/copy_traits_sm75.hpp), where only the supplying threads have nonzero stride,
  and in the DstLayout of the `SM90_*_STSM_*` atoms; it says nothing about which thread performs the
  access. The value part (which lanes' addresses are used) is checked by the hardware probe
  txverify-archive/core-coverage/probes/matrix_move/matrix_move.cu, where non-supplying lanes point
  at a poison row. The attribution part is checked as far as a tool can see it by
  matrix_row_access.cu in the same directory, which runs under compute-sanitizer memcheck and
  expects the one invalid 16-byte access to be reported for the supplying thread. Both ran on a
  B200 on 2026-11-16 and agreed: memcheck reported one invalid 16-byte shared access, by the
  supplying thread 5, for `ldmatrix` and for `stmatrix`, and none for lanes 8 to 31.

Direction: reading

Effect: If the hardware placed the elements otherwise, the register values that the model derives
  for `ldmatrix` and `movmatrix` and the memory contents it derives for `stmatrix` would differ from
  the hardware's. If the hardware attributed a row's access to another thread of the warp, an
  execution the model accepts could race with that thread's earlier or later accesses to the row.
  Disclosed by every kernel whose statement names `Op.matrix`: none.

### EXT-MMA-SPARSE-FIGURES — the sparse metadata layout

Statement: The metadata of `mma.sp` is laid out as the manual's figures show, a 2-bit index in the
  low bits belongs to the first non-zero element of its chunk, and the B fragments of the sparse
  shapes that only figures give continue the formula of the dense shapes. `MmaSpec.metaLoc` and
  `MmaSpec.sparseCol`: with four fields per row (`.m16n8k16` of 16-bit types, `.m16n8k8` of `.tf32`)
  the thread of the selector in each group of four holds row `g` in bits 0 to 15 and row `g + 8` in
  bits 16 to 31, field `u` at bit `4 u` (Figures 122 and 130); with eight fields per row of 16- or
  32-bit types (`.m16n8k32` of 16-bit types, `.m16n8k16` of `.tf32`) thread `2 f` of the group holds
  the first four fields of rows `g` and `g + 8` and thread `2 f + 1` the last four (Figures 125 and
  128); with eight fields per row of 8- or 4-bit types thread `2 f` holds row `g` and thread
  `2 f + 1` row `g + 8`, field `u` at bit `4 u` (Figures 132 and 142); with sixteen fields per row
  thread `2 h + v` holds half `h` of row `g + 8 v` (Figures 139, 140, 149 and 150). The B fragments
  of `.m16n8k32` of 16-bit types, `.m16n8k16` of `.tf32`, `.m16n8k64` of 8-bit types and
  `.m16n8k128` of 4-bit types follow `MmaSpec.fragB` (Figures 124, 127, 135 to 138 and 145 to 148).

Source:
- §9.7.16.6.1 and §9.7.16.6.2, as quoted in THREAD-MATRIX-LAYOUT, and Figures 115 to 150 (images of
    the HTML manual)

Why it is not spec text: The metadata layouts and these B fragments are drawn only in figures; the
  text gives the meaningful index values, which for the ordered variant put the smaller index in the
  low bits, and the order of the non-zero elements in the fragment is not stated.

Evidence: Manual: §9.7.16.6.1 and §9.7.16.6.2 with Figures 115 to 150, as above. CUTLASS
  (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) has no CuTe `mma.sp` atom for these shapes; its
  CUTLASS 2.x wrappers (include/cutlass/arch/mma_sparse_sm80.h) issue `mma.sp::ordered_metadata`
  with 2-bit indices and two selector values for `m16n8k32` of 16-bit types, the range the model
  allows, and keep the metadata placement in reorder code that was not evaluated. The hardware probe
  txverify-archive/core-coverage/probes/mma_fragments/ runs every sparse shape and type with every
  allowed selector, ordered and unordered metadata, and random bits in the metadata the model says
  is unused. It ran on a B200 on 2026-11-16 with two random seeds and agreed with the model in
  every sparse form.

Direction: reading

Effect: If the hardware read the metadata otherwise, the columns of A that the model multiplies with
  B, and so the results it derives, would differ from the hardware's. Disclosed by every kernel
  whose statement names `MmaSpec.sparse`: none.

### EXT-MMA-FRAGMENTS — the fragment layouts of mma.sync, including the A columns of `mma.m16n8k256`

Statement: The model reads the A, B and C fragments of the dense `mma` shapes by the manual's
  formulas, with one exception. Elements 32 to 63 of the A fragment of `mma.m16n8k256` are in
  columns `32 t + (i & 0x1F)` of row `g + 8`, as in `mma.m16n8k128`. The manual's formula gives `32
  t + i`. `MmaSpec.fragA` uses `32 t + (i & 0x1F) + 128 (r / 2)` for every element of `.b1` A.

Source:
- §9.7.16.5.13: "( threadID_in_group * 32 ) + i for ai where i < 64 ( threadID_in_group * 32 ) + ( i
    & 0x1F ) + 128 for ai where i >= 64"
- §9.7.16.5.12: "col = ( threadID_in_group * 32 ) + ( i & 0x1F ) for ai where i = { 0 , ..., 63 }"

Why it is not spec text: Read literally, the formula gives lane `t` columns `32 t + 32` to
  `32 t + 63` of row `g + 8`, which are the columns of lane `t + 1`'s first register, so two lanes
  would hold one element and columns 0 to 31 of row `g + 8` none.

Evidence: Manual: the two formulas quoted above. CUTLASS (NVIDIA/cutlass) commit b2f249ac
  (v4.8.0-23): the A, B and C layouts of the SM80 and SM90 `mma` atoms of 16-, 32-, 64-, 8-, 4- and
  1-bit types agree with `MmaSpec.fragA`, `fragB` and `fragCD`
  (txverify-archive/core-coverage/probes/cutlass_check.py); the ALayout of
  `SM80_16x8x256_S32U1U1S32_TN_XORPOPC` (include/cute/atom/mma_traits_sm80.hpp),
  `((4,8),(32,2,2)):((512,1),(16,8,2048))`, puts element i of lane l in column `32 t + (i & 0x1F) +
  128 (i / 64)`, which is this reading (txverify-archive/core-coverage/probes/cutlass_check.py).
  Read literally, the manual's formula leaves 512 of the 4096 positions of A held by no lane or by
  two. The hardware probe txverify-archive/core-coverage/probes/mma_fragments/ covers every dense
  `mma` shape and type and runs `m16n8k256` with `.and.popc` and `.xor.popc` against this reading.
  It ran on a B200 on 2026-11-16 with two random seeds and agreed with the model in every dense
  form.

Direction: reading

Effect: If the hardware used another placement, the single-bit products the model derives for this
  shape would differ from the hardware's. Disclosed by every kernel whose statement names
  `Op.matrix`: none.
-/

/-- The row (the index of the lane that supplied its address) and the byte in that row of byte
`b` of register `r` of lane `l` of a matrix load or store (EXT-MATRIX-FIGURES). The `.m16n16` and
`.m16n8` forms have `.trans` (`MatrixMove.supported`). -/
def MatrixMove.source (m : MatrixMove) (l r b : Nat) : Nat × Nat :=
  let g := l / 4
  let t := l % 4
  match m.shape, m.trans with
  | .m8n8, false => (8 * r + g, 4 * t + b)
  | .m8n8, true => (8 * r + 2 * t + b / 2, 2 * g + b % 2)
  | .m16n16, _ => (16 * (r / 2) + 4 * t + b, 8 * (r % 2) + g)
  | .m16n8, _ => (8 * r + 2 * t + b % 2, g + 8 * (b / 2))
  | .m8n16, _ => (8 * r + g, 4 * t + b)

/-- The source lane and byte of byte `b` of lane `l`'s `movmatrix` result (EXT-MATRIX-FIGURES):
its element `b / 2` is the source element in row `2 t + b / 2` and column `g`. -/
def transposeSource (l b : Nat) : Nat × Nat :=
  let g := l / 4
  let t := l % 4
  (4 * (2 * t + b / 2) + g / 2, 2 * (g % 2) + b % 2)

/-- The elements per register of an operand of type `ty`. -/
def MmaSpec.perReg (ty : DType) : Nat := MmaSpec.regBits ty / ty.width

/-- `(q, row, col)` of element `i` of lane `l`'s A fragment; for `mma.sp` the column is that of
the compressed matrix (EXT-MMA-FRAGMENTS for `.b1`). -/
def MmaSpec.fragA (s : MmaSpec) (l i : Nat) : Nat × Nat × Nat :=
  let g := l / 4
  let t := l % 4
  if s.quad then
    let hi := 4 * (l / 16)
    if s.aRow then (l / 4 % 4, t + hi, i) else (l / 4 % 4, i % 4 + hi, t)
  else
    let e := MmaSpec.perReg s.types.a
    let r := i / e
    (0, g + 8 * (r % 2), e * t + i % e + 4 * e * (r / 2))

/-- `(q, row, col)` of element `i` of lane `l`'s B fragment. -/
def MmaSpec.fragB (s : MmaSpec) (l i : Nat) : Nat × Nat × Nat :=
  let g := l / 4
  let t := l % 4
  if s.quad then
    let hi := 4 * (l / 16)
    if s.bCol then (l / 4 % 4, i, t + hi) else (l / 4 % 4, t, i + hi)
  else
    let e := MmaSpec.perReg s.types.b
    (0, 4 * e * (i / e) + e * t + i % e, g)

/-- `(q, row, col)` of element `i` of lane `l`'s C or D fragment of type `ty`. -/
def MmaSpec.fragCD (s : MmaSpec) (ty : DType) (l i : Nat) : Nat × Nat × Nat :=
  let g := l / 4
  let t := l % 4
  if s.quad then
    let hi := 4 * (l / 16)
    if ty == .float .f16 then (l / 4 % 4, t + hi, i)
    else (l / 4 % 4, l % 2 + i / 2 % 2 * 2 + hi, i / 4 * 4 + l / 2 % 2 * 2 + i % 2)
  else (0, g + 8 * (i / 2), 2 * t + i % 2)

/-- The columns of A one 4-bit metadata field of `mma.sp` covers: 2 for `.tf32`, 8 for 4-bit
types, 4 otherwise. -/
def MmaSpec.metaCols (s : MmaSpec) : Nat :=
  if s.types.a.width == 32 then 2 else if s.types.a.width == 4 then 8 else 4

/-- The lane and bit of the metadata field of row `row` and chunk `u` of A under sparsity
selector `sel` (EXT-MMA-SPARSE-FIGURES). -/
def MmaSpec.metaLoc (s : MmaSpec) (sel row u : Nat) : Nat × Nat :=
  let g := row % 8
  let h := row / 8
  let fields := s.k / s.metaCols
  if fields == 4 then (4 * g + sel, 16 * h + 4 * u)
  else if fields == 8 then
    if 16 ≤ s.types.a.width then (4 * g + 2 * sel + u / 4, 16 * h + 4 * (u % 4))
    else (4 * g + 2 * sel + h, 4 * u)
  else (4 * g + 2 * (u / 8) + h, 4 * (u % 8))

/-- The column of A of compressed element `c` of a row whose chunk has the 4-bit metadata field
`f`, or none for a field the variant does not allow (§9.7.16.6.1, §9.7.16.6.3): two equal indices,
or for the ordered variant indices not in increasing order; for `.tf32` a field other than `0b0100`
and `0b1110`. -/
def MmaSpec.sparseCol (s : MmaSpec) (ordered : Bool) (f c : Nat) : Option Nat :=
  let i0 := f % 4
  let i1 := f / 4 % 4
  let valid := if ordered then decide (i0 < i1) else decide (i0 ≠ i1)
  match s.metaCols with
  | 2 => if f == 4 then some (2 * c) else if f == 14 then some (2 * c + 1) else none
  | 8 =>
    if valid then some (8 * (c / 4) + 2 * (if c % 4 < 2 then i0 else i1) + c % 2) else none
  | _ => if valid then some (4 * (c / 2) + (if c % 2 = 0 then i0 else i1)) else none

end PTX
