-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Fragments

@[expose] public section

/-!
# Where the lanes hold the matrices of a tile

Index identities only: no machine value and no register occurs here. `Math/Fragments.lean` says
which real matrices one tile computes. The compiled code keeps each of them spread over the 32
lanes of a warp, and moves it between four layouts:

* the layout of an A operand, a B operand and an accumulator of a multiply-accumulate
  (`WarpMatrix.aRow/aCol`, `bRow/bCol`, `cRow/cCol`, `Lemmas/Matrix/Mma.lean`);
* the layout of `ldmatrix`, `stmatrix` and `movmatrix` (`WarpMatrix.toFrag`, `ofFrag`,
  `toFrag1`, `Lemmas/Matrix/Move.lean`): four 8 × 8 matrices, lane `4 g + t` holding row `g`,
  columns `2 t` and `2 t + 1` of matrix `r` in register `r`.

Each lemma below is one passage of the code from one layout to another, in the notation of the
register table (`Gen/Tables/matrix_table.json`): lane `l`, register `r`, half `h` (0 is the low
half of a register that holds two 16-bit elements).

* `ldmatrix` of a 16 × 16 block of `k_decayed`, `q_decayed`, `INV` or `Mqk` gives an A operand:
  `WarpMatrix.aFrag_eq`, `keyTiles`.
* `ldmatrix` of 16 rows of `state_acc` gives two B operands: `stateTiles_frag`.
* `ldmatrix … .trans` of a 16 × 16 block of `k_restored` gives the transposed A operand:
  `restoredTiles_frag`.
* The block of `v` (loaded like an A operand) against the accumulator `u_acc`: `aRow_cRow`,
  `aCol_cCol`.
* Two narrowed accumulator registers packed into one register: `rowPair_eq`.
* `movmatrix` of such a register gives a B register: `rowTile_transpose`.
* `stmatrix` of four such registers into the output stage: `ofFrag_pairFrag`.
* `stmatrix … .trans` of four such registers into `state_acc`: `transpose_pairFrag`,
  `stateTiles_pairFrag`.
-/

namespace PTX.Kernels.FlashKdaFwd.Math.Fragments
open PTX.WarpMatrix

variable {α : Type}

/-! ## Halves -/

/-- The halves of a value block are 8 channels apart. -/
theorem halfBase_add (warp block half : ℕ) :
    halfBase warp block 0 + 8 * half = halfBase warp block half := by
  unfold halfBase
  omega

/-- The value blocks of a warp are 16 channels apart, and the warps 32. -/
theorem halfBase_zero (warp block : ℕ) : halfBase warp block 0 = 32 * warp + 16 * block := by
  unfold halfBase
  omega

/-! ## Loads -/

/-- The four 8 × 8 matrices whose rows an `ldmatrix` of key block `m` of a tile array
`a[row][key feature]` reads: lane `8 q + i` reads row `i` of matrix `q`, and element `j` of that
row is `a (i + 8 (q % 2)) (16 m + j + 8 (q / 2))`. They are the tiles of the A operand
`keyBlock a m` (`WarpMatrix.aFrag_eq`). -/
theorem keyTiles (a : ℕ → ℕ → ℝ) (m q i j : ℕ) :
    aTiles (keyBlock a m) q i j = a (i + 8 * (q % 2)) (16 * m + (j + 8 * (q / 2))) :=
  rfl

/-- The four 8 × 8 matrices whose rows an `ldmatrix` of key block `m` of the state copy reads
(and a transposing `stmatrix` writes), for the value block that starts at channel `c0`: lane
`8 q + i` reads row `i` of matrix `q`, whose element `j` is the state entry of key feature
`16 m + 8 (q % 2) + j` and value channel `c0 + 8 (q / 2) + i`. A row of `state_acc` is one value
channel and eight consecutive key features. -/
def stateTiles (s : ℕ → ℕ → ℝ) (c0 m q i j : ℕ) : ℝ :=
  s (16 * m + 8 * (q % 2) + j) (c0 + 8 * (q / 2) + i)

/-- **The state load gives two B operands.** Registers 0 and 1 of the load are the B operand of
the half at channel `c0`, registers 2 and 3 the B operand of the half at channel `c0 + 8`: half
`h` of register `r` of lane `l` holds entry `(bRow l (r % 2) h, bCol l)` of
`stateBlock s (c0 + 8 (r / 2)) m`. -/
theorem stateTiles_frag (s : ℕ → ℕ → ℝ) (c0 m l r h : ℕ) :
    toFrag (stateTiles s c0 m) l r h =
      stateBlock s (c0 + 8 * (r / 2)) m (bRow l (r % 2) h) (bCol l) := by
  simp only [toFrag, toFrag1, stateTiles, stateBlock, bRow, bCol]
  congr 1
  omega

/-- The four 8 × 8 matrices whose rows the transposing `ldmatrix` of key block `m` of
`k_restored` reads: lane `8 q + i` reads row `i` of matrix `q`, whose element `j` is
`a (8 (q / 2) + i) (16 m + 8 (q % 2) + j)`. Compared with `keyTiles` the roles of `q % 2` and
`q / 2` are exchanged: the code computes these row addresses differently (the instruction
`mad.lo.s32 …, -896, …` before the load). -/
def restoredTiles (a : ℕ → ℕ → ℝ) (m q i j : ℕ) : ℝ :=
  a (8 * (q / 2) + i) (16 * m + 8 * (q % 2) + j)

/-- **The transposing load of `k_restored` gives the A operand `keyBlockT`**: its rows are the
key features of the block and its columns the rows of the tile. -/
theorem restoredTiles_frag (a : ℕ → ℕ → ℝ) (m l r h : ℕ) :
    toFrag (transposeMats (restoredTiles a m)) l r h =
      keyBlockT a m (aRow l r) (aCol l r h) := by
  simp only [toFrag, toFrag1, transposeMats, restoredTiles, keyBlockT, aRow, aCol]
  congr 1 <;> omega

/-! ## The values against the accumulator -/

/-- The block of `v` is loaded in the layout of an A operand, the accumulator `u_acc` of a value
block is two accumulators of 8 columns. The element of `v` in half `h` of register `r` is in
the row of accumulator register `2 (r % 2) + h` … -/
theorem aRow_cRow (l r : ℕ) {h : ℕ} (hh : h < 2) : aRow l r = cRow l (2 * (r % 2) + h) := by
  unfold aRow cRow
  omega

/-- … and in its column, in the half `r / 2` of the value block. -/
theorem aCol_cCol (l r : ℕ) {h : ℕ} (hh : h < 2) :
    aCol l r h = cCol l (2 * (r % 2) + h) + 8 * (r / 2) := by
  unfold aCol cCol
  omega

/-! ## Packed accumulator registers -/

/-- The content of the register that packs the narrowed accumulator registers `2 p` and
`2 p + 1` (`p` is 0 or 1) of a 16 × 8 matrix `M`: half `h` of lane `l` holds the entry of
accumulator register `2 p + h`. The register table calls this layout `rowPair`. -/
def rowPair (M : ℕ → ℕ → α) (p l h : ℕ) : α := M (cRow l (2 * p + h)) (cCol l (2 * p + h))

/-- Rows `8 p` to `8 p + 7` of a matrix, as an 8 × 8 matrix. -/
def rowTile (M : ℕ → ℕ → α) (p i j : ℕ) : α := M (8 * p + i) j

/-- A packed register holds, in the layout of `movmatrix` and `stmatrix`, the 8 × 8 matrix of
rows `8 p` to `8 p + 7`. -/
theorem rowPair_eq (M : ℕ → ℕ → α) (p l : ℕ) {h : ℕ} (hh : h < 2) :
    rowPair M p l h = toFrag1 (rowTile M p) l h := by
  simp only [rowPair, toFrag1, rowTile, cRow, cCol]
  congr 1 <;> omega

/-- **`movmatrix` of a packed register gives a B register.** The transpose of the tile of rows
`8 p` to `8 p + 7` of `M`, in the layout of `movmatrix`, is B register `p` of the B operand
`M` (`WarpMatrix.mov_elems` gives the transposed tile). -/
theorem rowTile_transpose (M : ℕ → ℕ → α) (p l h : ℕ) :
    toFrag1 (fun i j => rowTile M p j i) l h = M (bRow l p h) (bCol l) :=
  rfl

/-- The four registers a `stmatrix` stores: register `R` packs the accumulator registers
`2 (R % 2)` and `2 (R % 2) + 1` of the half `R / 2`; `M q` is the 16 × 8 matrix of half `q`. -/
def pairFrag (M : ℕ → ℕ → ℕ → α) (l R h : ℕ) : α := rowPair (M (R / 2)) (R % 2) l h

/-- **`stmatrix` into the output stage.** Lane `8 R + i` writes row `i` of the matrix that the
registers `R` hold (`WarpMatrix.st4_elems false`): its element `j` is entry
`(8 (R % 2) + i, j)` of the half `R / 2`. -/
theorem ofFrag_pairFrag (M : ℕ → ℕ → ℕ → α) (R i : ℕ) {j : ℕ} (hj : j < 8) :
    ofFrag (pairFrag M) R i j = M (R / 2) (8 * (R % 2) + i) j := by
  simp only [ofFrag, ofFrag1, pairFrag, rowPair, cRow, cCol]
  congr 1 <;> omega

/-- **Transposing `stmatrix`.** Lane `8 R + i` writes column `i` of the matrix that the
registers `R` hold (`WarpMatrix.st4_elems true`): its element `j` is entry
`(8 (R % 2) + j, i)` of the half `R / 2`. -/
theorem transpose_pairFrag (M : ℕ → ℕ → ℕ → α) (R j : ℕ) {i : ℕ} (hi : i < 8) :
    transposeMats (ofFrag (pairFrag M)) R i j = M (R / 2) (8 * (R % 2) + j) i :=
  ofFrag_pairFrag M R j hi

/-- **The transposing store of the new state writes the rows the state load reads.** When the
four stored registers hold the new state `s'` of key block `m` of the value block at channel
`c0` (the matrix of half `q` has the entry `s' (16 m + i) (c0 + 8 q + j)` at `(i, j)`, as
`nextState` does), the rows written are the tiles `stateTiles s' c0 m`: the next tile's load
reads `s'` as its state copy. -/
theorem stateTiles_pairFrag (s' : ℕ → ℕ → ℝ) (c0 m R j : ℕ) {i : ℕ} (hi : i < 8) :
    transposeMats (ofFrag (pairFrag fun q i j => s' (16 * m + i) (c0 + 8 * q + j))) R i j =
      stateTiles s' c0 m R i j := by
  rw [transpose_pairFrag _ R j hi]
  simp only [stateTiles]
  congr 1
  omega

end PTX.Kernels.FlashKdaFwd.Math.Fragments
