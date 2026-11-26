-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Source.Maps
public import Kernels.FlashKdaFwd.Proof.Ref.Source.Inputs
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Exports
public import Kernels.FlashKdaFwd.Proof.Values.Contract

@[expose] public section

/-! # The 70 loads of a tile: source, frame, content

For every tile `tt` of its sequence the load leader of a block (thread 128) issues 70 tensor
loads into the input stage `tt % 3` (an 18048-byte buffer at window byte
`32768 + 18048 (tt % 3)`); the load at *position* `p < 70` is the copy `tileLoad P L g tt p`
(`Ref/Producer/Shapes.lean`). The positions form five *families*:

| family | positions | array | stage offsets from | slots |
|---|---|---|---|---|
| values | `p < 16` | `v`, features `8 p ..` of the tile's 16 tokens | `256 p` | 8, 16, 2 |
| logits | 16 | `beta`, 32 elements | `4096` | 32, 1, 2 |
| rows | `17 + 16 a + j` | row array `a`, features `8 j ..` | `4224 + 4096 a + 256 j` | 8, 16, 2 |
| total | 65 | `g_total` | `16512` | 128, 1, 4 |
| square | `66 + 2 a + j` | square array `a`, columns `8 j ..` | `17024 + 512 a + 256 j` | 8, 16, 2|

Slots: the columns, rows and bytes per element of the load's box. Row arrays (`a < 3`,
`j < 16`): `k_decayed`, `q_decayed`, `k_restored`. Square arrays (`a < 2`, `j < 2`): `INV`,
`Mqk`. The 64 bytes at the stage offsets 4160 to 4223 are written by no load.

* `tileLoad_values`, `tileLoad_logits`, `tileLoad_rows`, `tileLoad_total`, `tileLoad_square`:
  the copy of each family through its shape of `Data/TensorMaps.lean`.
* **Source addresses** `tileLoad_read_*` (as offsets in `Spec.lean`'s arrays) and
  `tileLoad_loc_*` (in `Spec.lean`'s location functions `Params.valueLoc`, `logitLoc`,
  `rowLoc`, `totalDecayLoc`, `squareLoc`): the global byte of slot `(x, y, k)`. The workspace
  loads are inside their arrays. A slot of a values load is outside `v` exactly when its token
  row `first token of the tile + y` is not a token of the batch (a padding row beyond the last
  token of the batch); a slot of the logits load is outside `beta` exactly when its
  index is `H * T_total` or more. Those slots are filled with zero.
* **Frame** `tileLoad_input`: every byte a tile load reads is a launch input byte (allocated, no
  output and no final-state byte: the load part of `DirectFacts.globalReadFrame`).
* **Destination** `tileLoad_write_*`: the window byte of slot `(x, y, k)`.
* **Content** `tile_values`, `tile_logits`, `tile_rows`, `tile_total`, `tile_square`: for a
  stage offset `o` of the family, the slot that is written at window byte
  `32768 + 18048 (tt % 3) + o`, and that the record of the load, once notified, holds there the
  byte `Values.stageByte P mem0 seq head tt o`, which is defined. `tile_load_content` is the
  five together: the load is `Producer.pieceOf o` and the slot `(tileX o, tileY o, tileK o)`.

Words: `T_total` is the number of tokens of the batch, `H` the number of heads; the *window*
of a block is its shared memory from the address of `shared_mem`; a *slot* `(x, y, k)` is byte
`k` of the element in column `x` of row `y` of a load's box. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
open PTX TensorDescriptor
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (cu ft)
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer (tileLoad tilesOf slotOf betaIdx mapFin)
open PTX.Kernels.FlashKdaFwd.Proof.Values (stageByte)
open PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g tt x y k : Nat}

/-! ### The copies, by family -/

/-- A load of the values `v` (position `p < 16`). -/
theorem tileLoad_values (P : Params) (L : Launch) (g tt : Nat) {p : Nat} (hp : p < 16) :
    tileLoad P L g tt p = copyOf (tokenMap P.valuesBase P.total P.heads (P.allocation 0))
      (originOf [8 * p, cu P (seqOf P g) + 16 * tt, headOf P g])
      ⟨.shared, g / L.block, P.sharedBase + 18048 * (tt % 3) + (32768 + 256 * p)⟩
      ⟨.shared, g / L.block, P.sharedBase + 98304 + 8 * (tt % 3)⟩ := by
  interval_cases p <;> rfl

/-- The load of the gate logits `beta` (position 16). -/
theorem tileLoad_logits (P : Params) (L : Launch) (g tt : Nat) :
    tileLoad P L g tt 16 = copyOf (logitMap P.logitsBase (P.heads * P.total) (P.allocation 1))
      (originOf [betaIdx P g tt])
      ⟨.shared, g / L.block, P.sharedBase + 18048 * (tt % 3) + 36864⟩
      ⟨.shared, g / L.block, P.sharedBase + 98304 + 8 * (tt % 3)⟩ := rfl

/-- A load of row array `a` (`k_decayed`, `q_decayed`, `k_restored`; position
`17 + 16 a + j`). -/
theorem tileLoad_rows (P : Params) (L : Launch) (g tt : Nat) {a j : Nat} (ha : a < 3)
    (hj : j < 16) :
    tileLoad P L g tt (17 + 16 * a + j) = copyOf
      (tileRowsMap (P.array (4096 * a)) P.slots (P.allocation (mapFin (17 + 16 * a + j))))
      (originOf [8 * j, 0, slotOf P g tt])
      ⟨.shared, g / L.block,
        P.sharedBase + 18048 * (tt % 3) + (36992 + 4096 * a + 256 * j)⟩
      ⟨.shared, g / L.block, P.sharedBase + 98304 + 8 * (tt % 3)⟩ := by
  interval_cases a <;> interval_cases j <;> rfl

/-- The load of `g_total` (position 65). -/
theorem tileLoad_total (P : Params) (L : Launch) (g tt : Nat) :
    tileLoad P L g tt 65 = copyOf (totalDecayMap (P.array 12288) P.slots (P.allocation 5))
      (originOf [0, slotOf P g tt])
      ⟨.shared, g / L.block, P.sharedBase + 18048 * (tt % 3) + 49280⟩
      ⟨.shared, g / L.block, P.sharedBase + 98304 + 8 * (tt % 3)⟩ := rfl

/-- A load of square array `a` (`INV`, `Mqk`; position `66 + 2 a + j`). -/
theorem tileLoad_square (P : Params) (L : Launch) (g tt : Nat) {a j : Nat} (ha : a < 2)
    (hj : j < 2) :
    tileLoad P L g tt (66 + 2 * a + j) = copyOf
      (tileSquareMap (P.array (12800 + 512 * a)) P.slots
        (P.allocation (mapFin (66 + 2 * a + j))))
      (originOf [8 * j, 0, slotOf P g tt])
      ⟨.shared, g / L.block,
        P.sharedBase + 18048 * (tt % 3) + (49792 + 512 * a + 256 * j)⟩
      ⟨.shared, g / L.block, P.sharedBase + 98304 + 8 * (tt % 3)⟩ := by
  interval_cases a <;> interval_cases j <;> rfl

/-- The five families cover the 70 positions. -/
theorem position_family {i : Nat} (hi : i < 70) :
    i < 16 ∨ i = 16 ∨ (∃ a j, a < 3 ∧ j < 16 ∧ i = 17 + 16 * a + j) ∨ i = 65 ∨
      ∃ a j, a < 2 ∧ j < 2 ∧ i = 66 + 2 * a + j := by
  by_cases h1 : i < 16
  · exact .inl h1
  by_cases h2 : i = 16
  · exact .inr (.inl h2)
  by_cases h3 : i < 65
  · exact .inr (.inr (.inl ⟨(i - 17) / 16, (i - 17) % 16, by omega, by omega, by omega⟩))
  by_cases h4 : i = 65
  · exact .inr (.inr (.inr (.inl h4)))
  · exact .inr (.inr (.inr (.inr ⟨(i - 66) / 2, (i - 66) % 2, by omega, by omega, by omega⟩)))

/-- The workspace slot of a tile, in the two notations (`Producer.slotOf`, `Params.slot`). -/
theorem slotOf_eq (P : Params) (g tt : Nat) :
    slotOf P g tt = P.slot (seqOf P g) (headOf P g) tt := by
  unfold slotOf Params.slot
  rw [Nat.mul_comm]

/-- The workspace holds the tile at the slot of a tile of the block's sequence. -/
theorem tile_stored (hpre : Pre P L mem0) (hg : g < L.threads) (htt : tt < tilesOf P g) :
    P.TileStored mem0 (P.slot (seqOf P g) (headOf P g) tt)
        (P.tile (seqOf P g) (headOf P g) tt) ∧
      P.slot (seqOf P g) (headOf P g) tt < P.slots :=
  ⟨hpre.workspace _ (seqOf_lt hpre g) _ (headOf_lt hpre hg) tt htt,
    slot_lt hpre (seqOf_lt hpre g) (headOf_lt hpre hg) htt⟩

/-! ### Source addresses -/

/-- **Values**: slot `(x, y, k)` of the load at position `p` reads byte `16 p + 2 x + k` of the
256-byte row of token `first token of the tile + y` and the block's head, when that token is a
token of the batch; otherwise the slot is outside `v`. -/
theorem tileLoad_read_values (hpre : Pre P L mem0) (hg : g < L.threads) (tt : Nat) {p : Nat}
    (hp : p < 16) (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.readLoc (tileLoad P L g tt p) x y k =
      if cu P (seqOf P g) + 16 * tt + y < P.total then
        some ⟨.global, 0, P.valuesBase +
          256 * ((cu P (seqOf P g) + 16 * tt + y) * P.heads + headOf P g) +
          (16 * p + 2 * x + k)⟩
      else none := by
  have hh := headOf_lt hpre hg
  have e : (cu P (seqOf P g) + 16 * tt + y) * (256 * P.heads) =
      256 * ((cu P (seqOf P g) + 16 * tt + y) * P.heads) := by ring
  rw [tileLoad_values P L g tt hp, read_token _ _ _ _ _ _ _ _ _ hx hy hk]
  by_cases hc : cu P (seqOf P g) + 16 * tt + y < P.total
  · rw [ite_eq_left ⟨by omega, hc, hh⟩, ite_eq_left hc]
    congr 2
    omega
  · rw [ite_eq_right (fun h => hc h.2.1), ite_eq_right hc]

/-- **Logits**: slot `(x, 0, k)` of the load reads byte `k` of element `betaIdx + x` of `beta`,
when that index is below `H * T_total`; otherwise the slot is outside `beta`. -/
theorem tileLoad_read_logits (P : Params) (L : Launch) (g tt : Nat) (hx : x < 32)
    (hk : k < 2) :
    TensorCopy.readLoc (tileLoad P L g tt 16) x 0 k =
      if betaIdx P g tt + x < P.heads * P.total then
        some ⟨.global, 0, P.logitsBase + 2 * (betaIdx P g tt + x) + k⟩
      else none := by
  rw [tileLoad_logits, read_logit _ _ _ _ _ _ hx hk]
  split_ifs
  · congr 2
    omega
  · rfl

/-- **Row arrays**: slot `(x, y, k)` of the load at position `17 + 16 a + j` reads byte
`256 y + 16 j + 2 x + k` of the tile's slot of row array `a`. -/
theorem tileLoad_read_rows (hpre : Pre P L mem0) (hg : g < L.threads) (htt : tt < tilesOf P g)
    {a j : Nat} (ha : a < 3) (hj : j < 16) (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.readLoc (tileLoad P L g tt (17 + 16 * a + j)) x y k =
      some ⟨.global, 0, P.array (4096 * a) + 4096 * P.slot (seqOf P g) (headOf P g) tt +
        (256 * y + 16 * j + 2 * x + k)⟩ := by
  have hs := (tile_stored hpre hg htt).2
  rw [← slotOf_eq] at hs ⊢
  rw [tileLoad_rows P L g tt ha hj, read_rows _ _ _ _ _ _ _ _ hx hy hk,
    ite_eq_left ⟨by omega, by omega, hs⟩]
  congr 2
  omega

/-- **`g_total`**: slot `(x, 0, k)` of the load reads byte `4 x + k` of the tile's slot. -/
theorem tileLoad_read_total (hpre : Pre P L mem0) (hg : g < L.threads) (htt : tt < tilesOf P g)
    (hx : x < 128) (hk : k < 4) :
    TensorCopy.readLoc (tileLoad P L g tt 65) x 0 k =
      some ⟨.global, 0, P.array 12288 + 512 * P.slot (seqOf P g) (headOf P g) tt +
        (4 * x + k)⟩ := by
  have hs := (tile_stored hpre hg htt).2
  rw [← slotOf_eq] at hs ⊢
  rw [tileLoad_total, read_total _ _ _ _ _ _ _ hx hk, ite_eq_left ⟨by omega, hs⟩]
  congr 2
  omega

/-- **Square arrays**: slot `(x, y, k)` of the load at position `66 + 2 a + j` reads byte
`32 y + 16 j + 2 x + k` of the tile's slot of square array `a`. -/
theorem tileLoad_read_square (hpre : Pre P L mem0) (hg : g < L.threads)
    (htt : tt < tilesOf P g) {a j : Nat} (ha : a < 2) (hj : j < 2) (hx : x < 8) (hy : y < 16)
    (hk : k < 2) :
    TensorCopy.readLoc (tileLoad P L g tt (66 + 2 * a + j)) x y k =
      some ⟨.global, 0, P.array (12800 + 512 * a) +
        512 * P.slot (seqOf P g) (headOf P g) tt + (32 * y + 16 * j + 2 * x + k)⟩ := by
  have hs := (tile_stored hpre hg htt).2
  rw [← slotOf_eq] at hs ⊢
  rw [tileLoad_square P L g tt ha hj, read_square _ _ _ _ _ _ _ _ hx hy hk,
    ite_eq_left ⟨by omega, by omega, hs⟩]
  congr 2
  omega

/-! ### The same addresses in the specification's location functions -/

/-- **Values**, in `Params.valueLoc`: slot `(x, y, k)` of the load at position `p` reads byte
`k` of the value of channel `8 p + x`, token `first token of the tile + y` and the block's
head. -/
theorem tileLoad_loc_values (hpre : Pre P L mem0) (hg : g < L.threads) (tt : Nat) {p : Nat}
    (hp : p < 16) (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.readLoc (tileLoad P L g tt p) x y k =
      if cu P (seqOf P g) + 16 * tt + y < P.total then
        some ((P.valueLoc (cu P (seqOf P g) + 16 * tt + y) (headOf P g)
          ⟨8 * p + x, by omega⟩).at k)
      else none := by
  rw [tileLoad_read_values hpre hg tt hp hx hy hk]
  split_ifs
  · congr 1
    simp only [Params.valueLoc, Loc.at, Loc.mk.injEq, true_and]
    omega
  · rfl

/-- **Logits**, in `Params.logitLoc`: slot `(x, 0, k)` reads byte `k` of the gate logit of
element `i = betaIdx + x` of the `[H, T_total]` array, that is of head `i / T_total` and token
`i % T_total`. -/
theorem tileLoad_loc_logits (P : Params) (L : Launch) (g tt : Nat) (hx : x < 32) (hk : k < 2) :
    TensorCopy.readLoc (tileLoad P L g tt 16) x 0 k =
      if betaIdx P g tt + x < P.heads * P.total then
        some ((P.logitLoc ((betaIdx P g tt + x) / P.total)
          ((betaIdx P g tt + x) % P.total)).at k)
      else none := by
  rw [tileLoad_read_logits P L g tt hx hk]
  split_ifs
  · congr 1
    simp only [Params.logitLoc, Loc.at, Nat.div_add_mod']
  · rfl

/-- **Row arrays**, in `Params.rowLoc`: slot `(x, y, k)` of the load at position
`17 + 16 a + j` reads byte `k` of element (row `y`, feature `8 j + x`) of the tile's slot. -/
theorem tileLoad_loc_rows (hpre : Pre P L mem0) (hg : g < L.threads) (htt : tt < tilesOf P g)
    {a j : Nat} (ha : a < 3) (hj : j < 16) (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.readLoc (tileLoad P L g tt (17 + 16 * a + j)) x y k =
      some ((P.rowLoc (4096 * a) (P.slot (seqOf P g) (headOf P g) tt) ⟨y, hy⟩
        ⟨8 * j + x, by omega⟩).at k) := by
  rw [tileLoad_read_rows hpre hg htt ha hj hx hy hk]
  congr 1
  simp only [Params.rowLoc, Loc.at, Loc.mk.injEq, true_and]
  omega

/-- **`g_total`**, in `Params.totalDecayLoc`: slot `(x, 0, k)` reads byte `k` of element `x`
of the tile's slot. -/
theorem tileLoad_loc_total (hpre : Pre P L mem0) (hg : g < L.threads) (htt : tt < tilesOf P g)
    (hx : x < 128) (hk : k < 4) :
    TensorCopy.readLoc (tileLoad P L g tt 65) x 0 k =
      some ((P.totalDecayLoc (P.slot (seqOf P g) (headOf P g) tt) ⟨x, hx⟩).at k) := by
  rw [tileLoad_read_total hpre hg htt hx hk]
  congr 1
  simp only [Params.totalDecayLoc, Loc.at, Loc.mk.injEq, true_and]
  omega

/-- **Square arrays**, in `Params.squareLoc`: slot `(x, y, k)` of the load at position
`66 + 2 a + j` reads byte `k` of element (row `y`, column `8 j + x`) of the tile's slot. -/
theorem tileLoad_loc_square (hpre : Pre P L mem0) (hg : g < L.threads) (htt : tt < tilesOf P g)
    {a j : Nat} (ha : a < 2) (hj : j < 2) (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.readLoc (tileLoad P L g tt (66 + 2 * a + j)) x y k =
      some ((P.squareLoc (12800 + 512 * a) (P.slot (seqOf P g) (headOf P g) tt) ⟨y, hy⟩
        ⟨8 * j + x, by omega⟩).at k) := by
  rw [tileLoad_read_square hpre hg htt ha hj hx hy hk]
  congr 1
  simp only [Params.squareLoc, Loc.at, Loc.mk.injEq, true_and]
  omega

/-! ### The slots of a load, from a read or a write -/

/-- The slots of a values load. -/
theorem box_values {p : Nat} (hp : p < 16) {l : Loc}
    (h : TensorCopy.readLoc (tileLoad P L g tt p) x y k = some l ∨
      TensorCopy.writeLoc (tileLoad P L g tt p) x y k = some l) : x < 8 ∧ y < 16 ∧ k < 2 := by
  obtain ⟨h0, h1, h2⟩ := box_token P.valuesBase P.total P.heads (P.allocation 0)
  rw [tileLoad_values P L g tt hp] at h
  have hb := h.elim TensorCopy.readLoc_bounds TensorCopy.writeLoc_bounds
  exact ⟨Nat.lt_of_lt_of_eq hb.1 h0, Nat.lt_of_lt_of_eq hb.2.1 h1, Nat.lt_of_lt_of_eq hb.2.2 h2⟩

/-- The slots of the logits load. -/
theorem box_logits {l : Loc}
    (h : TensorCopy.readLoc (tileLoad P L g tt 16) x y k = some l ∨
      TensorCopy.writeLoc (tileLoad P L g tt 16) x y k = some l) : x < 32 ∧ y = 0 ∧ k < 2 := by
  obtain ⟨h0, h1, h2⟩ := box_logit P.logitsBase (P.heads * P.total) (P.allocation 1)
  rw [tileLoad_logits] at h
  have hb := h.elim TensorCopy.readLoc_bounds TensorCopy.writeLoc_bounds
  have hy := Nat.lt_of_lt_of_eq hb.2.1 h1
  exact ⟨Nat.lt_of_lt_of_eq hb.1 h0, by omega, Nat.lt_of_lt_of_eq hb.2.2 h2⟩

/-- The slots of a row-array load. -/
theorem box_rowsLoad {a j : Nat} (ha : a < 3) (hj : j < 16) {l : Loc}
    (h : TensorCopy.readLoc (tileLoad P L g tt (17 + 16 * a + j)) x y k = some l ∨
      TensorCopy.writeLoc (tileLoad P L g tt (17 + 16 * a + j)) x y k = some l) :
    x < 8 ∧ y < 16 ∧ k < 2 := by
  obtain ⟨h0, h1, h2⟩ := box_rows (P.array (4096 * a)) P.slots
    (P.allocation (mapFin (17 + 16 * a + j)))
  rw [tileLoad_rows P L g tt ha hj] at h
  have hb := h.elim TensorCopy.readLoc_bounds TensorCopy.writeLoc_bounds
  exact ⟨Nat.lt_of_lt_of_eq hb.1 h0, Nat.lt_of_lt_of_eq hb.2.1 h1, Nat.lt_of_lt_of_eq hb.2.2 h2⟩

/-- The slots of the `g_total` load. -/
theorem box_totalLoad {l : Loc}
    (h : TensorCopy.readLoc (tileLoad P L g tt 65) x y k = some l ∨
      TensorCopy.writeLoc (tileLoad P L g tt 65) x y k = some l) : x < 128 ∧ y = 0 ∧ k < 4 := by
  obtain ⟨h0, h1, h2⟩ := box_total (P.array 12288) P.slots (P.allocation 5)
  rw [tileLoad_total] at h
  have hb := h.elim TensorCopy.readLoc_bounds TensorCopy.writeLoc_bounds
  have hy := Nat.lt_of_lt_of_eq hb.2.1 h1
  exact ⟨Nat.lt_of_lt_of_eq hb.1 h0, by omega, Nat.lt_of_lt_of_eq hb.2.2 h2⟩

/-- The slots of a square-array load. -/
theorem box_squareLoad {a j : Nat} (ha : a < 2) (hj : j < 2) {l : Loc}
    (h : TensorCopy.readLoc (tileLoad P L g tt (66 + 2 * a + j)) x y k = some l ∨
      TensorCopy.writeLoc (tileLoad P L g tt (66 + 2 * a + j)) x y k = some l) :
    x < 8 ∧ y < 16 ∧ k < 2 := by
  obtain ⟨h0, h1, h2⟩ := box_square (P.array (12800 + 512 * a)) P.slots
    (P.allocation (mapFin (66 + 2 * a + j)))
  rw [tileLoad_square P L g tt ha hj] at h
  have hb := h.elim TensorCopy.readLoc_bounds TensorCopy.writeLoc_bounds
  exact ⟨Nat.lt_of_lt_of_eq hb.1 h0, Nat.lt_of_lt_of_eq hb.2.1 h1, Nat.lt_of_lt_of_eq hb.2.2 h2⟩

/-! ### Frame -/

/-- **Every byte a tile load reads is a launch input byte.** -/
theorem tileLoad_input (hpre : Pre P L mem0) (hg : g < L.threads) (htt : tt < tilesOf P g)
    {i : Nat} (hi : i < 70) {l : Loc}
    (h : TensorCopy.readLoc (tileLoad P L g tt i) x y k = some l) : InputByte P mem0 l := by
  obtain ⟨hW, hs⟩ := tile_stored hpre hg htt
  have hh := headOf_lt hpre hg
  rcases position_family hi with hp | rfl | ⟨a, j, ha, hj, rfl⟩ | rfl | ⟨a, j, ha, hj, rfl⟩
  · obtain ⟨hx, hy, hk⟩ := box_values hp (.inl h)
    rw [tileLoad_read_values hpre hg tt hp hx hy hk] at h
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    exact values_input hpre hc hh (by omega)
  · obtain ⟨hx, rfl, hk⟩ := box_logits (.inl h)
    rw [tileLoad_read_logits P L g tt hx hk] at h
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    exact logits_input hpre hc hk
  · obtain ⟨hx, hy, hk⟩ := box_rowsLoad ha hj (.inl h)
    rw [tileLoad_read_rows hpre hg htt ha hj hx hy hk] at h
    obtain rfl := Option.some.inj h
    exact rows_input hpre hW hs ha (by omega)
  · obtain ⟨hx, rfl, hk⟩ := box_totalLoad (.inl h)
    rw [tileLoad_read_total hpre hg htt hx hk] at h
    obtain rfl := Option.some.inj h
    exact total_input hpre hW hs (by omega)
  · obtain ⟨hx, hy, hk⟩ := box_squareLoad ha hj (.inl h)
    rw [tileLoad_read_square hpre hg htt ha hj hx hy hk] at h
    obtain rfl := Option.some.inj h
    exact square_input hpre hW hs ha (by omega)

/-! ### Destinations -/

/-- **Values**: slot `(x, y, k)` of the load at position `p` is written at stage offset
`256 p + 16 y + 2 x + k`. -/
theorem tileLoad_write_values (P : Params) (L : Launch) (g tt : Nat) {p : Nat} (hp : p < 16)
    (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.writeLoc (tileLoad P L g tt p) x y k = some ⟨.shared, g / L.block,
      P.sharedBase + (32768 + 18048 * (tt % 3) + (256 * p + (16 * y + 2 * x + k)))⟩ := by
  rw [tileLoad_values P L g tt hp, write_token _ _ _ _ _ _ hx hy hk]
  congr 2
  simp only
  omega

/-- **Logits**: slot `(x, 0, k)` is written at stage offset `4096 + 2 x + k`. -/
theorem tileLoad_write_logits (P : Params) (L : Launch) (g tt : Nat) (hx : x < 32)
    (hk : k < 2) :
    TensorCopy.writeLoc (tileLoad P L g tt 16) x 0 k = some ⟨.shared, g / L.block,
      P.sharedBase + (32768 + 18048 * (tt % 3) + (4096 + (2 * x + k)))⟩ := by
  rw [tileLoad_logits, write_logit _ _ _ _ _ hx hk]
  congr 2
  simp only
  omega

/-- **Row arrays**: slot `(x, y, k)` of the load at position `17 + 16 a + j` is written at
stage offset `4224 + 4096 a + 256 j + 16 y + 2 x + k`. -/
theorem tileLoad_write_rows (P : Params) (L : Launch) (g tt : Nat) {a j : Nat} (ha : a < 3)
    (hj : j < 16) (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.writeLoc (tileLoad P L g tt (17 + 16 * a + j)) x y k = some ⟨.shared,
      g / L.block, P.sharedBase +
        (32768 + 18048 * (tt % 3) + (4224 + 4096 * a + 256 * j + (16 * y + 2 * x + k)))⟩ := by
  rw [tileLoad_rows P L g tt ha hj, write_rows _ _ _ _ _ hx hy hk]
  congr 2
  simp only
  omega

/-- **`g_total`**: slot `(x, 0, k)` is written at stage offset `16512 + 4 x + k`. -/
theorem tileLoad_write_total (P : Params) (L : Launch) (g tt : Nat) (hx : x < 128)
    (hk : k < 4) :
    TensorCopy.writeLoc (tileLoad P L g tt 65) x 0 k = some ⟨.shared, g / L.block,
      P.sharedBase + (32768 + 18048 * (tt % 3) + (16512 + (4 * x + k)))⟩ := by
  rw [tileLoad_total, write_total _ _ _ _ _ hx hk]
  congr 2
  simp only
  omega

/-- **Square arrays**: slot `(x, y, k)` of the load at position `66 + 2 a + j` is written at
stage offset `17024 + 512 a + 256 j + 16 y + 2 x + k`. -/
theorem tileLoad_write_square (P : Params) (L : Launch) (g tt : Nat) {a j : Nat} (ha : a < 2)
    (hj : j < 2) (hx : x < 8) (hy : y < 16) (hk : k < 2) :
    TensorCopy.writeLoc (tileLoad P L g tt (66 + 2 * a + j)) x y k = some ⟨.shared,
      g / L.block, P.sharedBase +
        (32768 + 18048 * (tt % 3) + (17024 + 512 * a + 256 * j + (16 * y + 2 * x + k)))⟩ := by
  rw [tileLoad_square P L g tt ha hj, write_square _ _ _ _ _ hx hy hk]
  congr 2
  simp only
  omega

/-! ### Content -/

/-- A notified load holds, at a slot whose source is a launch input byte, the launch value. -/
theorem copied_join (hX : Consistent L kernel Assumptions.all mem0 X) (hW : WriteFrame P X)
    {i : EvId} {rec : TensorCopy.Observation} (hrec : X.tensor i = some rec)
    (hn : rec.effects.notified = true) {l : Loc}
    (hl : TensorCopy.readLoc rec.spec x y k = some l) (hin : InputByte P mem0 l) :
    TensorCopy.writeByte rec x y k = (mem0 l).join ∧ ((mem0 l).join).isSome := by
  obtain ⟨v, hv⟩ := hin.2.1
  rw [writeByte_copied hX hrec hn hl hv (hin.unwritten hW), hv]
  exact ⟨rfl, rfl⟩

/-- **The content of the values `v` in a stage** (stage offsets below 4096). -/
theorem tile_values (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hW : WriteFrame P X) (hg : g < L.threads) (tt : Nat) {o : Nat} (ho : o < 4096) :
    TensorCopy.writeLoc (tileLoad P L g tt (o / 256)) (o % 16 / 2) (o % 256 / 16) (o % 2) =
        some ⟨.shared, g / L.block, L.sharedBase + (32768 + 18048 * (tt % 3) + o)⟩ ∧
      ∀ (i : EvId) (rec : TensorCopy.Observation), X.tensor i = some rec →
        rec.spec = tileLoad P L g tt (o / 256) → rec.effects.notified = true →
        TensorCopy.writeByte rec (o % 16 / 2) (o % 256 / 16) (o % 2) =
            stageByte P mem0 (seqOf P g) (headOf P g) tt o ∧
          (stageByte P mem0 (seqOf P g) (headOf P g) tt o).isSome := by
  have hp : o / 256 < 16 := by omega
  have hx : o % 16 / 2 < 8 := by omega
  have hy : o % 256 / 16 < 16 := by omega
  have hk : o % 2 < 2 := by omega
  have hh := headOf_lt hpre hg
  refine ⟨?_, fun i rec hrec hspec hn => ?_⟩
  · rw [tileLoad_write_values P L g tt hp hx hy hk, hpre.sharedBase]
    congr 3
    omega
  · have hl := tileLoad_read_values hpre hg tt hp hx hy hk
    rw [← hspec] at hl
    have hsb : stageByte P mem0 (seqOf P g) (headOf P g) tt o =
        if cu P (seqOf P g) + 16 * tt + o % 256 / 16 < P.total then
          (mem0 ⟨.global, 0, P.valuesBase +
            256 * ((cu P (seqOf P g) + 16 * tt + o % 256 / 16) * P.heads + headOf P g) +
            16 * (o / 256) + o % 16⟩).join
        else some ((Value.float .bf16 0).byteAt (o % 2)) := by
      simp only [stageByte, ho, ↓reduceIte]
    rw [hsb]
    by_cases hc : cu P (seqOf P g) + 16 * tt + o % 256 / 16 < P.total
    · rw [ite_eq_left hc] at hl ⊢
      have ea : P.valuesBase +
          256 * ((cu P (seqOf P g) + 16 * tt + o % 256 / 16) * P.heads + headOf P g) +
          16 * (o / 256) + o % 16 = P.valuesBase +
          256 * ((cu P (seqOf P g) + 16 * tt + o % 256 / 16) * P.heads + headOf P g) +
          (16 * (o / 256) + 2 * (o % 16 / 2) + o % 2) := by omega
      rw [ea]
      exact copied_join hX hW hrec hn hl (values_input hpre hc hh (by omega))
    · rw [ite_eq_right hc] at hl ⊢
      have hbox := box_values hp (l := ⟨.shared, g / L.block,
        P.sharedBase + (32768 + 18048 * (tt % 3) +
          (256 * (o / 256) + (16 * (o % 256 / 16) + 2 * (o % 16 / 2) + o % 2)))⟩)
        (.inr (tileLoad_write_values P L g tt hp hx hy hk))
      have hf := writeByte_filled hX hrec hn (x := o % 16 / 2) (y := o % 256 / 16) (k := o % 2)
        (by rw [hspec, tileLoad_values P L g tt hp]; exact (box_token _ _ _ _).1 ▸ hx)
        (by rw [hspec, tileLoad_values P L g tt hp]; exact (box_token _ _ _ _).2.1 ▸ hy)
        (by rw [hspec, tileLoad_values P L g tt hp]; exact hk) hl
      rw [hf, hspec, tileLoad_values P L g tt hp]
      exact ⟨rfl, rfl⟩

/-- **The content of the gate logits `beta` in a stage** (stage offsets 4096 to 4159). -/
theorem tile_logits (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hW : WriteFrame P X) (g tt : Nat) {o : Nat} (h1 : 4096 ≤ o) (h2 : o < 4160) :
    TensorCopy.writeLoc (tileLoad P L g tt 16) ((o - 4096) / 2) 0 (o % 2) =
        some ⟨.shared, g / L.block, L.sharedBase + (32768 + 18048 * (tt % 3) + o)⟩ ∧
      ∀ (i : EvId) (rec : TensorCopy.Observation), X.tensor i = some rec →
        rec.spec = tileLoad P L g tt 16 → rec.effects.notified = true →
        TensorCopy.writeByte rec ((o - 4096) / 2) 0 (o % 2) =
            stageByte P mem0 (seqOf P g) (headOf P g) tt o ∧
          (stageByte P mem0 (seqOf P g) (headOf P g) tt o).isSome := by
  have hx : (o - 4096) / 2 < 32 := by omega
  have hk : o % 2 < 2 := by omega
  refine ⟨?_, fun i rec hrec hspec hn => ?_⟩
  · rw [tileLoad_write_logits P L g tt hx hk, hpre.sharedBase]
    congr 3
    omega
  · have hl := tileLoad_read_logits P L g tt hx hk
    rw [← hspec] at hl
    have hb : 8 * ((headOf P g * P.total + (cu P (seqOf P g) + 16 * tt)) / 8) =
        betaIdx P g tt := by
      unfold betaIdx
      rw [Nat.mul_comm (headOf P g) P.total]
      omega
    have hsb : stageByte P mem0 (seqOf P g) (headOf P g) tt o =
        if betaIdx P g tt + (o - 4096) / 2 < P.heads * P.total then
          (mem0 ⟨.global, 0,
            P.logitsBase + 2 * (betaIdx P g tt + (o - 4096) / 2) + o % 2⟩).join
        else some ((Value.float .bf16 0).byteAt (o % 2)) := by
      simp only [stageByte, show ¬ o < 4096 by omega, h2, ↓reduceIte, hb]
    rw [hsb]
    by_cases hc : betaIdx P g tt + (o - 4096) / 2 < P.heads * P.total
    · rw [ite_eq_left hc] at hl ⊢
      exact copied_join hX hW hrec hn hl (logits_input hpre hc hk)
    · rw [ite_eq_right hc] at hl ⊢
      have hf := writeByte_filled hX hrec hn (x := (o - 4096) / 2) (y := 0) (k := o % 2)
        (by rw [hspec, tileLoad_logits]; exact (box_logit _ _ _).1 ▸ hx)
        (by rw [hspec, tileLoad_logits]; exact Nat.one_pos)
        (by rw [hspec, tileLoad_logits]; exact hk) hl
      rw [hf, hspec, tileLoad_logits]
      exact ⟨rfl, rfl⟩

/-- **The content of the three row arrays in a stage** (stage offsets 4224 to 16511). -/
theorem tile_rows (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hW : WriteFrame P X) (hg : g < L.threads) (htt : tt < tilesOf P g) {o : Nat}
    (h1 : 4224 ≤ o) (h2 : o < 16512) :
    TensorCopy.writeLoc (tileLoad P L g tt (17 + 16 * ((o - 4224) / 4096) +
          (o - 4224) % 4096 / 256))
        ((o - 4224) % 16 / 2) ((o - 4224) % 256 / 16) (o % 2) =
        some ⟨.shared, g / L.block, L.sharedBase + (32768 + 18048 * (tt % 3) + o)⟩ ∧
      ∀ (i : EvId) (rec : TensorCopy.Observation), X.tensor i = some rec →
        rec.spec = tileLoad P L g tt (17 + 16 * ((o - 4224) / 4096) +
          (o - 4224) % 4096 / 256) → rec.effects.notified = true →
        TensorCopy.writeByte rec ((o - 4224) % 16 / 2) ((o - 4224) % 256 / 16) (o % 2) =
            stageByte P mem0 (seqOf P g) (headOf P g) tt o ∧
          (stageByte P mem0 (seqOf P g) (headOf P g) tt o).isSome := by
  obtain ⟨hT, hs⟩ := tile_stored hpre hg htt
  have ha : (o - 4224) / 4096 < 3 := by omega
  have hj : (o - 4224) % 4096 / 256 < 16 := by omega
  have hx : (o - 4224) % 16 / 2 < 8 := by omega
  have hy : (o - 4224) % 256 / 16 < 16 := by omega
  have hk : o % 2 < 2 := by omega
  refine ⟨?_, fun i rec hrec hspec hn => ?_⟩
  · rw [tileLoad_write_rows P L g tt ha hj hx hy hk, hpre.sharedBase]
    congr 3
    omega
  · have hl := tileLoad_read_rows hpre hg htt ha hj hx hy hk
    rw [← hspec] at hl
    have hsb : stageByte P mem0 (seqOf P g) (headOf P g) tt o =
        (mem0 ⟨.global, 0, P.array (4096 * ((o - 4224) / 4096)) +
          4096 * P.slot (seqOf P g) (headOf P g) tt +
          256 * ((o - 4224) % 4096 % 256 / 16) + 16 * ((o - 4224) % 4096 / 256) +
          (o - 4224) % 4096 % 16⟩).join := by
      simp only [stageByte, show ¬ o < 4096 by omega, show ¬ o < 4160 by omega,
        show ¬ o < 4224 by omega, h2, ↓reduceIte]
    have ea : P.array (4096 * ((o - 4224) / 4096)) +
        4096 * P.slot (seqOf P g) (headOf P g) tt +
        256 * ((o - 4224) % 4096 % 256 / 16) + 16 * ((o - 4224) % 4096 / 256) +
        (o - 4224) % 4096 % 16 = P.array (4096 * ((o - 4224) / 4096)) +
        4096 * P.slot (seqOf P g) (headOf P g) tt +
        (256 * ((o - 4224) % 256 / 16) + 16 * ((o - 4224) % 4096 / 256) +
          2 * ((o - 4224) % 16 / 2) + o % 2) := by omega
    rw [hsb, ea]
    exact copied_join hX hW hrec hn hl (rows_input hpre hT hs ha (by omega))

/-- **The content of `g_total` in a stage** (stage offsets 16512 to 17023). -/
theorem tile_total (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hW : WriteFrame P X) (hg : g < L.threads) (htt : tt < tilesOf P g) {o : Nat}
    (h1 : 16512 ≤ o) (h2 : o < 17024) :
    TensorCopy.writeLoc (tileLoad P L g tt 65) ((o - 16512) / 4) 0 (o % 4) =
        some ⟨.shared, g / L.block, L.sharedBase + (32768 + 18048 * (tt % 3) + o)⟩ ∧
      ∀ (i : EvId) (rec : TensorCopy.Observation), X.tensor i = some rec →
        rec.spec = tileLoad P L g tt 65 → rec.effects.notified = true →
        TensorCopy.writeByte rec ((o - 16512) / 4) 0 (o % 4) =
            stageByte P mem0 (seqOf P g) (headOf P g) tt o ∧
          (stageByte P mem0 (seqOf P g) (headOf P g) tt o).isSome := by
  obtain ⟨hT, hs⟩ := tile_stored hpre hg htt
  have hx : (o - 16512) / 4 < 128 := by omega
  have hk : o % 4 < 4 := by omega
  refine ⟨?_, fun i rec hrec hspec hn => ?_⟩
  · rw [tileLoad_write_total P L g tt hx hk, hpre.sharedBase]
    congr 3
    omega
  · have hl := tileLoad_read_total hpre hg htt hx hk
    rw [← hspec] at hl
    have hsb : stageByte P mem0 (seqOf P g) (headOf P g) tt o =
        (mem0 ⟨.global, 0, P.array 12288 + 512 * P.slot (seqOf P g) (headOf P g) tt +
          (o - 16512)⟩).join := by
      simp only [stageByte, show ¬ o < 4096 by omega, show ¬ o < 4160 by omega,
        show ¬ o < 4224 by omega, show ¬ o < 16512 by omega, h2, ↓reduceIte]
    have ea : P.array 12288 + 512 * P.slot (seqOf P g) (headOf P g) tt + (o - 16512) =
        P.array 12288 + 512 * P.slot (seqOf P g) (headOf P g) tt +
        (4 * ((o - 16512) / 4) + o % 4) := by omega
    rw [hsb, ea]
    exact copied_join hX hW hrec hn hl (total_input hpre hT hs (by omega))

/-- **The content of the two square arrays in a stage** (stage offsets 17024 to 18047). -/
theorem tile_square (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hW : WriteFrame P X) (hg : g < L.threads) (htt : tt < tilesOf P g) {o : Nat}
    (h1 : 17024 ≤ o) (h2 : o < 18048) :
    TensorCopy.writeLoc (tileLoad P L g tt (66 + 2 * ((o - 17024) / 512) +
          (o - 17024) % 512 / 256))
        ((o - 17024) % 16 / 2) ((o - 17024) % 256 / 16) (o % 2) =
        some ⟨.shared, g / L.block, L.sharedBase + (32768 + 18048 * (tt % 3) + o)⟩ ∧
      ∀ (i : EvId) (rec : TensorCopy.Observation), X.tensor i = some rec →
        rec.spec = tileLoad P L g tt (66 + 2 * ((o - 17024) / 512) +
          (o - 17024) % 512 / 256) → rec.effects.notified = true →
        TensorCopy.writeByte rec ((o - 17024) % 16 / 2) ((o - 17024) % 256 / 16) (o % 2) =
            stageByte P mem0 (seqOf P g) (headOf P g) tt o ∧
          (stageByte P mem0 (seqOf P g) (headOf P g) tt o).isSome := by
  obtain ⟨hT, hs⟩ := tile_stored hpre hg htt
  have ha : (o - 17024) / 512 < 2 := by omega
  have hj : (o - 17024) % 512 / 256 < 2 := by omega
  have hx : (o - 17024) % 16 / 2 < 8 := by omega
  have hy : (o - 17024) % 256 / 16 < 16 := by omega
  have hk : o % 2 < 2 := by omega
  refine ⟨?_, fun i rec hrec hspec hn => ?_⟩
  · rw [tileLoad_write_square P L g tt ha hj hx hy hk, hpre.sharedBase]
    congr 3
    omega
  · have hl := tileLoad_read_square hpre hg htt ha hj hx hy hk
    rw [← hspec] at hl
    have hsb : stageByte P mem0 (seqOf P g) (headOf P g) tt o =
        (mem0 ⟨.global, 0, P.array (12800 + 512 * ((o - 17024) / 512)) +
          512 * P.slot (seqOf P g) (headOf P g) tt +
          32 * ((o - 17024) % 512 % 256 / 16) + 16 * ((o - 17024) % 512 / 256) +
          (o - 17024) % 512 % 16⟩).join := by
      simp only [stageByte, show ¬ o < 4096 by omega, show ¬ o < 4160 by omega,
        show ¬ o < 4224 by omega, show ¬ o < 16512 by omega, show ¬ o < 17024 by omega, h2,
        ↓reduceIte]
    have ea : P.array (12800 + 512 * ((o - 17024) / 512)) +
        512 * P.slot (seqOf P g) (headOf P g) tt +
        32 * ((o - 17024) % 512 % 256 / 16) + 16 * ((o - 17024) % 512 / 256) +
        (o - 17024) % 512 % 16 = P.array (12800 + 512 * ((o - 17024) / 512)) +
        512 * P.slot (seqOf P g) (headOf P g) tt +
        (32 * ((o - 17024) % 256 / 16) + 16 * ((o - 17024) % 512 / 256) +
          2 * ((o - 17024) % 16 / 2) + o % 2) := by omega
    rw [hsb, ea]
    exact copied_join hX hW hrec hn hl (square_input hpre hT hs ha (by omega))

/-! ### The slot that is written at a stage offset -/

/-- The column of the slot that is written at stage offset `o`. -/
def tileX (o : Nat) : Nat :=
  if o < 4096 then o % 16 / 2 else if o < 4224 then (o - 4096) / 2
  else if o < 16512 then (o - 4224) % 16 / 2 else if o < 17024 then (o - 16512) / 4
  else (o - 17024) % 16 / 2

/-- The row of the slot that is written at stage offset `o`. -/
def tileY (o : Nat) : Nat :=
  if o < 4096 then o % 256 / 16 else if o < 4224 then 0
  else if o < 16512 then (o - 4224) % 256 / 16 else if o < 17024 then 0
  else (o - 17024) % 256 / 16

/-- The byte of the slot that is written at stage offset `o`. -/
def tileK (o : Nat) : Nat := if 16512 ≤ o ∧ o < 17024 then o % 4 else o % 2

/-- The position of the load that writes a stage offset (`Producer.pieceOf`, the owner function
of the protocol layer) is one of the 70 positions. -/
theorem pieceOf_lt {o : Nat} (ho : o < 18048) : Producer.pieceOf o < 70 := by
  unfold Producer.pieceOf
  split_ifs <;> omega

/-- **What the 70 loads of tile `tt` leave at offset `o` of its input stage**, outside the
64-byte hole: the load at position `Producer.pieceOf o` has the slot `(tileX o, tileY o,
tileK o)` at window byte `32768 + 18048 (tt % 3) + o` of the block of thread `g`, and its
record, once notified, holds there the byte `Values.stageByte P mem0 seq head tt o`, which is
defined. -/
theorem tile_load_content (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hW : WriteFrame P X)
    (hg : g < L.threads) (htt : tt < tilesOf P g) {o : Nat} (ho : o < 18048)
    (hfree : o < 4160 ∨ 4224 ≤ o) :
    TensorCopy.writeLoc (tileLoad P L g tt (Producer.pieceOf o)) (tileX o) (tileY o)
        (tileK o) =
        some ⟨.shared, g / L.block, L.sharedBase + (32768 + 18048 * (tt % 3) + o)⟩ ∧
      ∀ (i : EvId) (rec : TensorCopy.Observation), X.tensor i = some rec →
        rec.spec = tileLoad P L g tt (Producer.pieceOf o) → rec.effects.notified = true →
        TensorCopy.writeByte rec (tileX o) (tileY o) (tileK o) =
            stageByte P mem0 (seqOf P g) (headOf P g) tt o ∧
          (stageByte P mem0 (seqOf P g) (headOf P g) tt o).isSome := by
  by_cases c1 : o < 4096
  · have ep : Producer.pieceOf o = o / 256 := by rw [Producer.pieceOf, ite_eq_left c1]
    have ex : tileX o = o % 16 / 2 := by rw [tileX, ite_eq_left c1]
    have ey : tileY o = o % 256 / 16 := by rw [tileY, ite_eq_left c1]
    have ek : tileK o = o % 2 := by
      unfold tileK
      split_ifs <;> omega
    rw [ep, ex, ey, ek]
    exact tile_values hpre hX hW hg tt c1
  by_cases c2 : o < 4160
  · have ep : Producer.pieceOf o = 16 := by
      unfold Producer.pieceOf
      split_ifs <;> omega
    have ex : tileX o = (o - 4096) / 2 := by
      unfold tileX
      split_ifs <;> omega
    have ey : tileY o = 0 := by
      unfold tileY
      split_ifs <;> omega
    have ek : tileK o = o % 2 := by
      unfold tileK
      split_ifs <;> omega
    rw [ep, ex, ey, ek]
    exact tile_logits hpre hX hW g tt (by omega) c2
  by_cases c3 : o < 16512
  · have ep : Producer.pieceOf o =
        17 + 16 * ((o - 4224) / 4096) + (o - 4224) % 4096 / 256 := by
      unfold Producer.pieceOf
      split_ifs <;> omega
    have ex : tileX o = (o - 4224) % 16 / 2 := by
      unfold tileX
      split_ifs <;> omega
    have ey : tileY o = (o - 4224) % 256 / 16 := by
      unfold tileY
      split_ifs <;> omega
    have ek : tileK o = o % 2 := by
      unfold tileK
      split_ifs <;> omega
    rw [ep, ex, ey, ek]
    exact tile_rows hpre hX hW hg htt (by omega) c3
  by_cases c4 : o < 17024
  · have ep : Producer.pieceOf o = 65 := by
      unfold Producer.pieceOf
      split_ifs <;> omega
    have ex : tileX o = (o - 16512) / 4 := by
      unfold tileX
      split_ifs <;> omega
    have ey : tileY o = 0 := by
      unfold tileY
      split_ifs <;> omega
    have ek : tileK o = o % 4 := by
      unfold tileK
      split_ifs <;> omega
    rw [ep, ex, ey, ek]
    exact tile_total hpre hX hW hg htt (by omega) c4
  · have ep : Producer.pieceOf o =
        66 + 2 * ((o - 17024) / 512) + (o - 17024) % 512 / 256 := by
      unfold Producer.pieceOf
      split_ifs <;> omega
    have ex : tileX o = (o - 17024) % 16 / 2 := by
      unfold tileX
      split_ifs <;> omega
    have ey : tileY o = (o - 17024) % 256 / 16 := by
      unfold tileY
      split_ifs <;> omega
    have ek : tileK o = o % 2 := by
      unfold tileK
      split_ifs <;> omega
    rw [ep, ex, ey, ek]
    exact tile_square hpre hX hW hg htt (by omega) ho

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
