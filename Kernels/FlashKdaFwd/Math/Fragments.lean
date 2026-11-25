-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Run
public import Lemmas.Matrix.Mma

@[expose] public section

/-!
# One tile of one compute warp, in the block structure of the compiled code

Real matrices only: no machine value and no register occurs here. This file states what the
matrix instructions of the tile loop (`csrc/smxx/fwd_kernel2.cuh`, lines 467 to 740; instructions
2135 to 2944 of the compiled kernel) compute, one multiply-accumulate at a time, and proves that
the result is `Recurrence.Tile.apply` for every value channel.

## Words and index conventions (each checked against the compiled code)

* A *tile* is 16 consecutive tokens; its *rows* are these tokens. A *key feature* is one of the
  128 coordinates of a key; a *value channel* is one of the 128 coordinates of a value.
* The *state* is a 128 × 128 array. Here it is always written `s key channel`: first index the
  key feature, second index the value channel. This is the orientation of the accumulator of the
  state update (the source's `state_regs[key block][value block]`). The shared buffer
  `state_acc` and the global state arrays store the transpose, `[value channel][key feature]`
  (`Spec.Params.initialLoc`); `Recurrence.Row 128`, the state of one channel, is the column
  `fun key => s key channel` (`column`).
* The tile arrays `k_decayed`, `q_decayed`, `k_restored` are `[row][key feature]`; `INV` and
  `Mqk` are `[row][row]`; `v` is `[row][value channel]`; `g_total` is `[key feature]`; `beta`
  is `[row]`.
* A *multiply-accumulate* is one `mma.sync.aligned.m16n8k16` instruction: with a 16 × 16 matrix
  `a`, a 16 × 8 matrix `b` and a 16 × 8 matrix `c` it produces `WarpMatrix.mmaReal a b c`, entry
  `(i, j)` being `c i j + ∑ k < 16, a i k * b k j`. One `gemm` of the source on a 16 × 16 block
  is two of them: value columns 0 to 7 and 8 to 15. Everything below is stated per *half*: the
  eight consecutive value channels `c, …, c + 7`. Warp `w` (0 to 3) owns the four halves
  `c = 32 w + 8 h`, `h < 4` (two value blocks of 16 channels).
* The state enters the tile twice: `copy` is the bfloat16 copy in `state_acc`, which is the B
  operand of the first phase; `carry` is the FP32 state in the lane's registers, which the last
  phase updates. Over the reals they are the same numbers (the hypothesis `hs` of the theorems),
  but they are separate arguments so that a later proof can say which register feeds which
  instruction.

## The phases (`Inputs` holds the arrays; `c` is the first channel of a half)

1. `project x.decayedKey x.copy c n` and `project x.decayedQuery x.copy c n`: the accumulators
   `u_acc` and `out_acc` after the first `n` key blocks. `project_succ` is one
   multiply-accumulate; `project_eq` is the partial sum.
2. `gate x i`: the gate strength of row `i`, written as the scalar instructions compute it.
3. `residual x c`: `u := (v - u) * beta`; `correction x c`: `U = INV · u`, one
   multiply-accumulate into a cleared accumulator.
4. `output x c`: `out += Mqk · U`, one multiply-accumulate onto the accumulator of phase 1.
5. (The store of `output` to the staging buffer moves no number.)
6. `update x c m`: `acc = k_restoredᵀ · U` for key block `m`; `nextState x c m`:
   `state := state * g_total + acc`, one fused multiply-add per entry.

`Mqk` enters as a full 16 × 16 matrix: the code multiplies all sixteen columns; that the upper
triangle is zero in the rows of real tokens is a fact about the prepared tile
(`Recurrence.Tile.Prepared.score`), not about this computation. Padding rows need no case here
either: the identities hold for all sixteen rows.

## Results

* `tile`: for a half `c` and a column `j`, `output x c t j` is the output of row `t` and
  `nextState x c m i j` is the new state entry of key `16 m + i`, both of
  `Tile.apply w (column x.carry (c + j)) (values x (c + j)) (strengths x)`.
* `outputs_eq`, `stateAfter_eq`: the same by absolute channel number.
* `carry_run`, `outputs_run`: chained over the tiles of a sequence, the carry that enters tile
  `b` is `Run.carry` and the outputs of tile `b` are those of `Tile.apply` on it.
-/

namespace PTX.Kernels.FlashKdaFwd.Math.Fragments
open Recurrence Finset Matrix
open PTX.WarpMatrix (mmaReal)
noncomputable section

/-- The real arrays one tile reads, with natural-number indices (rows `< 16`, key features and
value channels `< 128`; the values at other indices are never used). -/
structure Inputs where
  /-- `k_decayed[row][key feature]`. -/
  decayedKey : ℕ → ℕ → ℝ
  /-- `q_decayed[row][key feature]`. -/
  decayedQuery : ℕ → ℕ → ℝ
  /-- `k_restored[row][key feature]`. -/
  restoredKey : ℕ → ℕ → ℝ
  /-- `g_total[key feature]`. -/
  totalDecay : ℕ → ℝ
  /-- `INV[row][row]`. -/
  inverse : ℕ → ℕ → ℝ
  /-- `Mqk[row][row]`. -/
  score : ℕ → ℕ → ℝ
  /-- `v[row][value channel]`. -/
  value : ℕ → ℕ → ℝ
  /-- The gate logit `beta[row]`, before the gate function. -/
  logit : ℕ → ℝ
  /-- The bfloat16 copy of the state, `[key feature][value channel]` (`state_acc`). -/
  copy : ℕ → ℕ → ℝ
  /-- The FP32 state, `[key feature][value channel]` (the lanes' carry registers). -/
  carry : ℕ → ℕ → ℝ

/-! ## The operands of the multiply-accumulates -/

/-- The A operand of phase 1 for key block `m`: the 16 × 16 block of a tile array
`a[row][key feature]`, entry `(i, k)` being `a i (16 m + k)`. -/
def keyBlock (a : ℕ → ℕ → ℝ) (m i k : ℕ) : ℝ := a i (16 * m + k)

/-- The A operand of phase 6 for key block `m`: the transposed block of a tile array
`a[row][key feature]`, entry `(i, k)` being `a k (16 m + i)`: its rows are the 16 key features
of the block and its columns the 16 rows of the tile. The code loads it from the buffer of
`k_restored` with the transposing form of `ldmatrix`. -/
def keyBlockT (a : ℕ → ℕ → ℝ) (m i k : ℕ) : ℝ := a k (16 * m + i)

/-- The B operand of phase 1 for key block `m` and the half that starts at channel `c`: entry
`(k, j)` is `s (16 m + k) (c + j)`, the state entry of key feature `16 m + k` and value channel
`c + j`. -/
def stateBlock (s : ℕ → ℕ → ℝ) (c m k j : ℕ) : ℝ := s (16 * m + k) (c + j)

/-! ## Phase 1: `u = k_decayed · S` and `out = q_decayed · S` -/

/-- The accumulator of `a · s` for the half at channel `c` after the first `n` key blocks: it
starts cleared and each key block adds one multiply-accumulate. With `a := x.decayedKey` this is
the source's `u_acc`, with `a := x.decayedQuery` its `out_acc`. -/
def project (a s : ℕ → ℕ → ℝ) (c : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => mmaReal (keyBlock a n) (stateBlock s c n) (project a s c n)

/-- The cleared accumulator. -/
theorem project_zero (a s : ℕ → ℕ → ℝ) (c : ℕ) : project a s c 0 = fun _ _ => 0 := rfl

/-- **One multiply-accumulate of phase 1**: the accumulator after key block `n` is the
instruction's result on the block `n` of the tile array, the block `n` of the state copy and the
accumulator before. -/
theorem project_succ (a s : ℕ → ℕ → ℝ) (c n : ℕ) :
    project a s c (n + 1) = mmaReal (keyBlock a n) (stateBlock s c n) (project a s c n) :=
  rfl

/-- **The partial sum**: after `n` key blocks the accumulator holds the sum over the first
`16 n` key features. -/
theorem project_eq (a s : ℕ → ℕ → ℝ) (c n i j : ℕ) :
    project a s c n i j = ∑ k ∈ range (16 * n), a i k * s k (c + j) := by
  induction n with
  | zero => simp [project]
  | succ n ih =>
    change project a s c n i j + ∑ k ∈ range 16, a i (16 * n + k) * s (16 * n + k) (c + j) = _
    rw [ih, Nat.mul_succ, sum_range_add]

/-- After the eight key blocks the accumulator holds the sum over all 128 key features. -/
theorem project_full (a s : ℕ → ℕ → ℝ) (c i j : ℕ) :
    project a s c 8 i j = ∑ k ∈ range 128, a i k * s k (c + j) :=
  project_eq a s c 8 i j

/-! ## Phases 2 and 3: the gate, `u := (v - u) * beta`, `U = INV · u` -/

/-- The gate strength of row `i` in the steps of the code: the logit times the constant
`multiplier` (`mul.ftz.f32` by `0fBFB8AA3B`), the power of two (`ex2.approx`), plus one
(`add.ftz.f32` of `0f3F800000`), the reciprocal (`rcp.approx`). -/
def gate (x : Inputs) (i : ℕ) : ℝ := 1 / (Real.rpow 2 (x.logit i * (multiplier : ℝ)) + 1)

/-- The scalar steps compute the specification's gate function. -/
theorem gate_eq (x : Inputs) (i : ℕ) : gate x i = strength (x.logit i) := rfl

/-- The reciprocal is never taken at zero: `2 ^ y + 1` is positive. -/
theorem gate_pos (y : ℝ) : 0 < Real.rpow 2 y + 1 :=
  add_pos (Real.rpow_pos_of_pos (by norm_num) y) one_pos

/-- The reciprocal is never taken at zero. -/
theorem gate_ne_zero (y : ℝ) : Real.rpow 2 y + 1 ≠ 0 := (gate_pos y).ne'

/-- `u := (v - u) * beta` for row `i` and column `j` of the half at channel `c`, in the operand
order of the code: `sub.ftz.f32` computes `v - u`, `mul.ftz.f32` computes `beta * (v - u)`. -/
def residual (x : Inputs) (c i j : ℕ) : ℝ :=
  gate x i * (x.value i (c + j) - project x.decayedKey x.copy c 8 i j)

/-- `U = INV · u` for the half at channel `c`: one multiply-accumulate with the whole `INV` as
the A operand, the residual as the B operand and a cleared accumulator. -/
def correction (x : Inputs) (c : ℕ) : ℕ → ℕ → ℝ :=
  mmaReal x.inverse (residual x c) fun _ _ => 0

/-! ## Phase 4: `out += Mqk · U` -/

/-- The output of the half at channel `c`: one multiply-accumulate with the whole `Mqk` as the A
operand and the correction as the B operand, onto the accumulator `q_decayed · S` of phase 1. -/
def output (x : Inputs) (c : ℕ) : ℕ → ℕ → ℝ :=
  mmaReal x.score (correction x c) (project x.decayedQuery x.copy c 8)

/-! ## Phase 6: the state update -/

/-- `acc = k_restoredᵀ · U` for key block `m` and the half at channel `c`: one
multiply-accumulate into a cleared accumulator. Entry `(i, j)` belongs to key feature
`16 m + i` and value channel `c + j`. -/
def update (x : Inputs) (c m : ℕ) : ℕ → ℕ → ℝ :=
  mmaReal (keyBlockT x.restoredKey m) (correction x c) fun _ _ => 0

/-- The new FP32 state entry of key feature `16 m + i` and value channel `c + j`, in the operand
order of the code's `fma.rn.ftz.f32`: `carry * g_total + acc`. Its bfloat16 copy is what the
transposing `stmatrix` writes back to `state_acc`. -/
def nextState (x : Inputs) (c m i j : ℕ) : ℝ :=
  x.carry (16 * m + i) (c + j) * x.totalDecay (16 * m + i) + update x c m i j

/-! ## The tile is `Tile.apply` -/

/-- The arrays of `x` are those of the tile `w`, at the indices of the tile. -/
structure Inputs.Holds (x : Inputs) (w : Tile) : Prop where
  decayedKey : ∀ (t : Fin 16) (k : Fin 128), x.decayedKey t k = w.decayedKey t k
  decayedQuery : ∀ (t : Fin 16) (k : Fin 128), x.decayedQuery t k = w.decayedQuery t k
  restoredKey : ∀ (t : Fin 16) (k : Fin 128), x.restoredKey t k = w.restoredKey t k
  totalDecay : ∀ k : Fin 128, x.totalDecay k = w.totalDecay k
  inverse : ∀ t j : Fin 16, x.inverse t j = w.inverse t j
  score : ∀ t j : Fin 16, x.score t j = w.score t j

/-- The inputs whose tile arrays are those of `w` (zero outside the index ranges), with the
given values, gate logits and the two views of the state. -/
def Inputs.ofTile (w : Tile) (value : ℕ → ℕ → ℝ) (logit : ℕ → ℝ) (copy carry : ℕ → ℕ → ℝ) :
    Inputs where
  decayedKey t k := if h : t < 16 ∧ k < 128 then w.decayedKey ⟨t, h.1⟩ ⟨k, h.2⟩ else 0
  decayedQuery t k := if h : t < 16 ∧ k < 128 then w.decayedQuery ⟨t, h.1⟩ ⟨k, h.2⟩ else 0
  restoredKey t k := if h : t < 16 ∧ k < 128 then w.restoredKey ⟨t, h.1⟩ ⟨k, h.2⟩ else 0
  totalDecay k := if h : k < 128 then w.totalDecay ⟨k, h⟩ else 0
  inverse t j := if h : t < 16 ∧ j < 16 then w.inverse ⟨t, h.1⟩ ⟨j, h.2⟩ else 0
  score t j := if h : t < 16 ∧ j < 16 then w.score ⟨t, h.1⟩ ⟨j, h.2⟩ else 0
  value := value
  logit := logit
  copy := copy
  carry := carry

/-- `Inputs.ofTile w …` holds the arrays of `w`. -/
theorem Inputs.ofTile_holds (w : Tile) (value : ℕ → ℕ → ℝ) (logit : ℕ → ℝ)
    (copy carry : ℕ → ℕ → ℝ) : (Inputs.ofTile w value logit copy carry).Holds w := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp [Inputs.ofTile]

/-- The state of value channel `ch`, by key feature: a column of the state array. -/
def column (s : ℕ → ℕ → ℝ) (ch : ℕ) : Row 128 := fun k => s k ch

/-- The values of channel `ch` in the 16 rows of the tile. -/
def values (x : Inputs) (ch : ℕ) : Fin 16 → ℝ := fun t => x.value t ch

/-- The gate strengths of the 16 rows of the tile. -/
def strengths (x : Inputs) : Fin 16 → ℝ := fun t => strength (x.logit t)

private theorem sum16 (f : ℕ → ℝ) : ∑ k ∈ range 16, f k = ∑ k : Fin 16, f k :=
  (Fin.sum_univ_eq_sum_range f 16).symm

private theorem sum128 (f : ℕ → ℝ) : ∑ k ∈ range 128, f k = ∑ k : Fin 128, f k :=
  (Fin.sum_univ_eq_sum_range f 128).symm

variable {x : Inputs} {w : Tile} {c j : ℕ}

/-- The full accumulator of a tile array `a` whose rows agree with `b` is the inner product of
the state column with the row of `b`. -/
theorem project_dot {a : ℕ → ℕ → ℝ} {b : Fin 16 → Row 128}
    (hab : ∀ (t : Fin 16) (k : Fin 128), a t k = b t k)
    (hs : ∀ k : Fin 128, x.copy k (c + j) = x.carry k (c + j)) (t : Fin 16) :
    project a x.copy c 8 t j = dot (column x.carry (c + j)) (b t) := by
  rw [project_full, sum128]
  exact sum_congr rfl fun k _ => by rw [hab t k, hs k]; exact mul_comm ..

/-- The residual of row `t` is the right-hand side of the tile's linear system. -/
theorem residual_eq (h : x.Holds w) (hs : ∀ k : Fin 128, x.copy k (c + j) = x.carry k (c + j))
    (t : Fin 16) :
    residual x c t j =
      (values x (c + j) t - dot (column x.carry (c + j)) (w.decayedKey t)) * strengths x t := by
  rw [residual, project_dot h.decayedKey hs t, gate_eq]
  exact mul_comm ..

/-- The correction of row `t` is the row of `INV · ((v - k_decayed · s) * beta)`. -/
theorem correction_eq (h : x.Holds w)
    (hs : ∀ k : Fin 128, x.copy k (c + j) = x.carry k (c + j)) (t : Fin 16) :
    correction x c t j = (w.inverse *ᵥ fun t =>
      (values x (c + j) t - dot (column x.carry (c + j)) (w.decayedKey t)) * strengths x t) t := by
  change 0 + ∑ k ∈ range 16, x.inverse t k * residual x c k j = _
  rw [zero_add, sum16]
  change _ = ∑ k : Fin 16, w.inverse t k *
    ((values x (c + j) k - dot (column x.carry (c + j)) (w.decayedKey k)) * strengths x k)
  exact sum_congr rfl fun k _ => by rw [h.inverse t k, residual_eq h hs k]

/-- **The output of a tile.** Row `t`, column `j` of the half at channel `c` is the output of
row `t` that `Tile.apply` gives for value channel `c + j`. -/
theorem output_eq (h : x.Holds w) (hs : ∀ k : Fin 128, x.copy k (c + j) = x.carry k (c + j))
    (t : Fin 16) :
    output x c t j =
      (w.apply (column x.carry (c + j)) (values x (c + j)) (strengths x)).1 t := by
  change project x.decayedQuery x.copy c 8 t j +
    ∑ k ∈ range 16, x.score t k * correction x c k j = _
  rw [project_dot h.decayedQuery hs t, sum16]
  change _ = dot _ _ + ∑ k : Fin 16, w.score t k * _
  congr 1
  exact sum_congr rfl fun k _ => by rw [h.score t k, correction_eq h hs k]

/-- **The state after a tile.** Entry `(i, j)` of key block `m` of the half at channel `c` is
the new state entry of key feature `16 m + i` that `Tile.apply` gives for value channel
`c + j`. -/
theorem nextState_eq (h : x.Holds w) (hs : ∀ k : Fin 128, x.copy k (c + j) = x.carry k (c + j))
    {m i : ℕ} (hk : 16 * m + i < 128) :
    nextState x c m i j =
      (w.apply (column x.carry (c + j)) (values x (c + j)) (strengths x)).2 ⟨16 * m + i, hk⟩ := by
  change x.carry (16 * m + i) (c + j) * x.totalDecay (16 * m + i) +
    (0 + ∑ k ∈ range 16, x.restoredKey k (16 * m + i) * correction x c k j) = _
  rw [zero_add, sum16, h.totalDecay ⟨16 * m + i, hk⟩]
  change _ = x.carry (16 * m + i) (c + j) * _ + ∑ k : Fin 16, w.restoredKey k ⟨16 * m + i, hk⟩ * _
  congr 1
  exact sum_congr rfl fun k _ => by
    rw [h.restoredKey k ⟨16 * m + i, hk⟩, correction_eq h hs k]

/-- **One tile of one half, in the form the register induction uses.** With the arrays of the
tile `w`, and the bfloat16 copy equal to the FP32 carry in channel `c + j`:

* the accumulator of phase 4 holds, at `(t, j)`, the output of row `t`;
* after the fused multiply-add of key block `m`, the carry of entry `(i, j)` holds the new state
  entry of key feature `16 m + i`;

both of `Tile.apply w` on the state column, the values and the gate strengths of channel
`c + j`. -/
theorem tile (h : x.Holds w) (hs : ∀ k : Fin 128, x.copy k (c + j) = x.carry k (c + j)) :
    let y := w.apply (column x.carry (c + j)) (values x (c + j)) (strengths x)
    (∀ t : Fin 16, output x c t j = y.1 t) ∧
      ∀ m i, ∀ hk : 16 * m + i < 128, nextState x c m i j = y.2 ⟨16 * m + i, hk⟩ :=
  ⟨output_eq h hs, fun _ _ hk => nextState_eq h hs hk⟩

/-! ## By absolute channel number, and the chain of tiles -/

/-- The first channel of half `half` (0 or 1) of value block `block` (0 or 1) of warp `warp`
(0 to 3): the warp owns the value blocks `2 warp` and `2 warp + 1` of 16 channels each. -/
def halfBase (warp block half : ℕ) : ℕ := 16 * (2 * warp + block) + 8 * half

/-- Every channel is column `ch % 8` of one half of one warp. -/
theorem halfBase_channel (ch : ℕ) :
    halfBase (ch / 32) (ch % 32 / 16) (ch % 16 / 8) + ch % 8 = ch := by
  unfold halfBase
  omega

/-- The half that holds channel `ch` starts at channel `8 (ch / 8)`. -/
theorem halfBase_eq (ch : ℕ) :
    halfBase (ch / 32) (ch % 32 / 16) (ch % 16 / 8) = 8 * (ch / 8) := by
  unfold halfBase
  omega

/-- The output of row `t` and value channel `ch`, wherever the code holds it: column `ch % 8`
of the half that starts at channel `8 (ch / 8)`. -/
def outputs (x : Inputs) (t ch : ℕ) : ℝ := output x (8 * (ch / 8)) t (ch % 8)

/-- The state entry of key feature `k` and value channel `ch` after the tile, wherever the code
holds it: entry `(k % 16, ch % 8)` of key block `k / 16` of the half at channel `8 (ch / 8)`. -/
def stateAfter (x : Inputs) (k ch : ℕ) : ℝ :=
  nextState x (8 * (ch / 8)) (k / 16) (k % 16) (ch % 8)

/-- The output of row `t` and channel `ch` is the one `Tile.apply` gives for that channel. -/
theorem outputs_eq (h : x.Holds w) {ch : ℕ} (hs : ∀ k : Fin 128, x.copy k ch = x.carry k ch)
    (t : Fin 16) :
    outputs x t ch = (w.apply (column x.carry ch) (values x ch) (strengths x)).1 t := by
  have hc : 8 * (ch / 8) + ch % 8 = ch := by omega
  have := output_eq (c := 8 * (ch / 8)) (j := ch % 8) h (by rwa [hc]) t
  rwa [hc] at this

/-- The state entry after the tile is the one `Tile.apply` gives for its channel. -/
theorem stateAfter_eq (h : x.Holds w) {ch : ℕ} (hs : ∀ k : Fin 128, x.copy k ch = x.carry k ch)
    (k : Fin 128) :
    stateAfter x k ch = (w.apply (column x.carry ch) (values x ch) (strengths x)).2 k := by
  have hc : 8 * (ch / 8) + ch % 8 = ch := by omega
  have hk : 16 * (k.val / 16) + k.val % 16 = k.val := by omega
  have := nextState_eq (c := 8 * (ch / 8)) (j := ch % 8) (m := k.val / 16) (i := k.val % 16) h
    (by rwa [hc]) (by omega)
  rw [hc] at this
  rw [stateAfter, this]
  exact congrArg _ (Fin.ext hk)

/-- **The chain of tiles.** For one value channel `ch` and a sequence of `n` tiles: if the
arrays of tile `b < n` are those of `ws b`, its bfloat16 copy equals its carry, the carry of the
first tile is the row `s0` and the carry after tile `b` (the carry of `xs (b + 1)`; `xs n` only
carries the final state) is the state that tile left (`stateAfter`), then the carry that enters
tile `b ≤ n` is `Run.carry`, the chain the specification's theorems (`Run.carry_eq`,
`Run.output_eq`, `Run.carry_final`) are about. -/
theorem carry_run {xs : ℕ → Inputs} {ws : ℕ → Tile} {ch n : ℕ} {s0 : Row 128}
    (h : ∀ b < n, (xs b).Holds (ws b))
    (hs : ∀ b < n, ∀ k : Fin 128, (xs b).copy k ch = (xs b).carry k ch)
    (h0 : ∀ k : Fin 128, (xs 0).carry k ch = s0 k)
    (hnext : ∀ b < n, ∀ k : Fin 128, (xs (b + 1)).carry k ch = stateAfter (xs b) k ch)
    {b : ℕ} (hb : b ≤ n) :
    column (xs b).carry ch =
      Run.carry ws (fun b => values (xs b) ch) (fun b => strengths (xs b)) s0 b := by
  induction b with
  | zero => exact funext h0
  | succ b ih =>
    funext k
    change (xs (b + 1)).carry k ch = _
    rw [hnext b hb k, stateAfter_eq (h b hb) (hs b hb) k, ih (Nat.le_of_succ_le hb)]
    rfl

/-- The outputs of tile `b < n` in the chain: row `t` of channel `ch` is the output
`Tile.apply` gives on `Run.carry`, the left-hand side of `Run.tile_output` and
`Run.output_eq`. -/
theorem outputs_run {xs : ℕ → Inputs} {ws : ℕ → Tile} {ch n : ℕ} {s0 : Row 128}
    (h : ∀ b < n, (xs b).Holds (ws b))
    (hs : ∀ b < n, ∀ k : Fin 128, (xs b).copy k ch = (xs b).carry k ch)
    (h0 : ∀ k : Fin 128, (xs 0).carry k ch = s0 k)
    (hnext : ∀ b < n, ∀ k : Fin 128, (xs (b + 1)).carry k ch = stateAfter (xs b) k ch)
    {b : ℕ} (hb : b < n) (t : Fin 16) :
    outputs (xs b) t ch =
      ((ws b).apply (Run.carry ws (fun b => values (xs b) ch) (fun b => strengths (xs b)) s0 b)
        (values (xs b) ch) (strengths (xs b))).1 t := by
  rw [outputs_eq (h b hb) (hs b hb) t, carry_run h hs h0 hnext hb.le]

end
end PTX.Kernels.FlashKdaFwd.Math.Fragments
