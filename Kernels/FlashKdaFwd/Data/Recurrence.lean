-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The FlashKDA forward recurrence over the real numbers

Definitions only. This file states, with real numbers and finite sums, what the FlashKDA forward
"recurrence" kernel computes and what it expects in the workspace that the preparation kernel
writes before it. The kernel's specification (`Spec.lean`) is phrased with these definitions; the
proofs about them are under `Math/`.

## The recurrence (what the kernel computes)

For one sequence, one head and one value channel the state is a row `S : Row 128`, indexed by the
key feature. Token `t` carries a key row `k_t`, a query row `q_t`, a row of log-decays `g_t`, one
value `v_t` and one gate strength `β_t`. It changes the state by (`step`)

    S' = S * exp g_t,      S := S' + β_t * (v_t - ⟨S', k_t⟩) * k_t

and its output is `scale * ⟨S, q_t⟩` with the new `S`. `tokenState x S₀ t` is the state after the
first `t` tokens of the stream `x`.

## Tiles (how the kernel computes it)

The kernel handles a sequence in tiles of 16 consecutive tokens. A sequence of `len` tokens has
`tiles len` tiles; tile `b` starts at token `16 * b` and has `liveRows len b` real tokens (16,
except in the last tile). The rows of a tile beyond its real tokens are padding. The packed batch
stores its sequences back to back: sequence `i` starts at token `firstToken length i` and its
tiles start at workspace slot `firstTile length i`.

## The prepared tile (what the kernel reads from the workspace)

For every tile the preparation kernel (`_flash_kda_fwd_prepare`, `csrc/smxx/fwd_kernel1.cuh`)
stores six arrays (`Tile`). `Tile.Prepared` states what they must contain, in terms of the
token data of the 16 rows of the tile; see the comment there for the correspondence with the
source lines.
-/

namespace PTX.Kernels.FlashKdaFwd.Recurrence
noncomputable section
open Finset

variable {d : ℕ}

/-! ## The token recurrence -/

/-- A row of `d` real numbers. The state of one sequence, head and value channel is a
`Row 128` indexed by the key feature; keys, queries and log-decays of one token are rows too. -/
abbrev Row (d : ℕ) := Fin d → ℝ

/-- The inner product `⟨a, b⟩` of two rows. -/
def dot (a b : Row d) : ℝ := ∑ i, a i * b i

/-- One token applied to the state row `old`. Every entry first decays, `before i = old i *
decay i`. The row then moves along `key` by `strength * (value - ⟨before, key⟩)`: the gate
strength times the difference between the token's value and what the decayed state returns
for the token's key. -/
def step (old decay key : Row d) (value strength : ℝ) : Row d :=
  let before := fun i => old i * decay i
  let correction := strength * (value - dot before key)
  fun i => before i + correction * key i

/-- The state row after the first `t` tokens, from the state `initial`. Token `j` has the decay
row `decay j`, the key `key j`, the value `v j` and the gate strength `beta j`. -/
def sequential (initial : Row d) (decay key : ℕ → Row d) (v beta : ℕ → ℝ) : ℕ → Row d
  | 0 => initial
  | t + 1 => step (sequential initial decay key v beta t) (decay t) (key t) (v t) (beta t)

/-- The tokens of one sequence, one head and one value channel, by token index: the key and
query rows (after the normalization of the preparation stage), the value of this channel, the
gate strength (a number in `(0, 1)`, see `strength`), and the row of log-decays (the natural
logarithm of the factor by which each state entry decays at this token). -/
structure Tokens (d : ℕ) where
  key : ℕ → Row d
  query : ℕ → Row d
  value : ℕ → ℝ
  strength : ℕ → ℝ
  logDecay : ℕ → Row d

/-- The state row after the first `t` tokens of `x`, from the state `initial`: the recurrence
`sequential` with the decay factors `exp (x.logDecay t i)`. -/
def tokenState (x : Tokens d) (initial : Row d) : ℕ → Row d :=
  sequential initial (fun t i => Real.exp (x.logDecay t i)) x.key x.value x.strength

/-- The tokens of `x` from token `offset` on, renumbered from zero. -/
def suffix (x : Tokens d) (offset : ℕ) : Tokens d where
  key t := x.key (offset + t)
  query t := x.query (offset + t)
  logDecay t := x.logDecay (offset + t)
  value t := x.value (offset + t)
  strength t := x.strength (offset + t)

/-! ## The gate strength -/

/-- The binary32 constant `0xBFB8AA3B` (about `-1 / ln 2`) of the compiled gate, as an exact
rational number. The source writes `-x * 1.4426950408889634f` (`utils.cuh`,
`sigmoid_approx_f32`). -/
def multiplier : ℚ := -12102203 / 8388608

/-- The gate strength the kernel computes from the gate logit `x`:
`1 / (2 ^ (x * multiplier) + 1)`. This is close to, but not equal to, the logistic function
`1 / (1 + exp (-x))`, because `multiplier` is a rounded `-1 / ln 2`. -/
def strength (x : ℝ) : ℝ := 1 / ((2 : ℝ) ^ (x * (multiplier : ℝ)) + 1)

/-! ## Tiles of 16 tokens and the packed batch -/

/-- The number of 16-token tiles of a sequence of `len` tokens: `⌈len / 16⌉`. -/
def tiles (len : ℕ) : ℕ := (len + 15) / 16

/-- The first token of tile `blocks` in a sequence of `total` tokens, `16 * blocks`, capped at
the end of the sequence. -/
def cursor (total blocks : ℕ) : ℕ := min (16 * blocks) total

/-- The number of real tokens in tile `block` of a sequence of `total` tokens: 16, or what is
left of the sequence in its last tile (and `0` past the last tile). -/
def liveRows (total block : ℕ) : ℕ := min 16 (total - cursor total block)

/-- The global index of the first token of sequence `i` in the packed batch: the sum of the
lengths of the sequences before it. The host array `cu_seqlens` holds these numbers. -/
def firstToken (length : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ range i, length j

/-- The number of tiles of the sequences before sequence `i`: the kernel's `tile_base`
(`fwd_kernel2.cuh`, the loop over `i < seq_idx`). -/
def firstTile (length : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ range i, tiles (length j)

/-! ## The prepared tile -/

/-- A family of rows with the rows from `len` on replaced by zero rows. In a tile with `len`
real tokens the preparation kernel treats the key and the log-decay of the padding rows as zero
(`fwd_kernel1.cuh`: `g_val = 0.0f` for `row >= actual_len`, and the loop that stores `BF16(0)`
into `k_smem` for those rows). -/
def masked (len : ℕ) (x : ℕ → Row d) (t : ℕ) : Row d := if t < len then x t else fun _ => 0

/-- The decay accumulated by the first `t` tokens: entry `i` is `exp (Σ_{j<t} logDecay j i)`,
the product of the first `t` decay factors. `cum logDecay 0` is the row of ones. -/
def cum (logDecay : ℕ → Row d) (t : ℕ) : Row d :=
  fun i => Real.exp (∑ j ∈ range t, logDecay j i)

/-- Row `t` of `x` multiplied entry by entry by the decay accumulated through token `t`
(inclusive): `cumulative (t + 1) i * x t i`. -/
def weighted (cumulative : ℕ → Row d) (x : ℕ → Row d) (t : ℕ) : Row d :=
  fun i => cumulative (t + 1) i * x t i

/-- The key of token `t` divided entry by entry by the decay accumulated through token `t`
(inclusive): `key t i / cumulative (t + 1) i`. -/
def restored (cumulative key : ℕ → Row d) (t : ℕ) : Row d :=
  fun i => key t i / cumulative (t + 1) i

/-- The coupling of row `t` to an earlier row `j` of the same tile:
`beta t * ⟨restored key j, weighted key t⟩`. Only the entries with `j < t` are used. -/
def coefficient (cum key : ℕ → Row d) (beta : ℕ → ℝ) (t j : ℕ) : ℝ :=
  beta t * dot (restored cum key j) (weighted cum key t)

/-- The unit lower-triangular 16 × 16 matrix `I + L`, where `L` is the part of `a` strictly
below the diagonal: entry `(t, j)` is `a t j` for `j < t`, `1` for `j = t` and `0` for
`j > t`. -/
def unitLower (a : ℕ → ℕ → ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun t j => if j.val < t.val then a t j else if t = j then 1 else 0

/-- The six workspace arrays of one tile, as real numbers. Rows are the 16 tokens of the tile,
columns of the three row arrays and of `totalDecay` are the 128 key features. Source names
(`csrc/smxx/fwd_launch.cu`): `decayedKey` is `k_decayed`, `decayedQuery` is `q_decayed`,
`restoredKey` is `k_restored`, `totalDecay` is `g_total`, `inverse` is `INV` and `score` is
`Mqk`. -/
structure Tile where
  decayedKey : Fin 16 → Row 128
  decayedQuery : Fin 16 → Row 128
  restoredKey : Fin 16 → Row 128
  totalDecay : Row 128
  inverse : Matrix (Fin 16) (Fin 16) ℝ
  score : Matrix (Fin 16) (Fin 16) ℝ

/-- The decay accumulated inside a tile whose first `len` rows are real tokens of `x`: `cum`
of the log-decays with the padding rows counted as zero. So `tileCum x len (t + 1)` is the
decay through row `t`, and it stays constant over the padding rows. -/
def tileCum (x : Tokens d) (len : ℕ) : ℕ → Row d := cum (masked len x.logDecay)

/-- The keys of a tile whose first `len` rows are real tokens of `x`: the padding rows are
zero. -/
def tileKey (x : Tokens d) (len : ℕ) : ℕ → Row d := masked len x.key

/-- `w` is what the preparation kernel stores for a tile whose rows `t < len` are the tokens
`0, …, len - 1` of `x` (the caller passes the tokens of the tile, renumbered from zero) and
whose rows `t ≥ len` are padding. `scale` is the output scale. `x.value` does not occur.

With `c = tileCum x len` and `k = tileKey x len` (`fwd_kernel1.cuh`, "decay_apply" to "inv"):

* `decayedKey`, `restoredKey`, `totalDecay` are fixed in all 16 rows: `k_decayed = k * c`,
  `k_restored = (k / c) * c 16`, `g_total = c 16`. In padding rows the first two are zero.
* `inverse` is the inverse of the unit lower-triangular matrix `I + L` with
  `L t j = x.strength t * ⟨k j / c (j+1), k t * c (t+1)⟩` for `j < t` (the kernel's `L`, with
  the gate strength applied to row `t`). Padding rows of `L` are zero because their key is.
* `decayedQuery` and `score` are fixed in the rows of real tokens only:
  `q_decayed t = scale * q t * c (t+1)` and `Mqk t j = ⟨k j / c (j+1), q_decayed t⟩` for
  `j ≤ t`, `0` for `j > t`. The preparation kernel does not clear the query of a padding row,
  so the padding rows of these two arrays hold numbers that this contract leaves open; the
  outputs of the real tokens and the state do not depend on them. -/
structure Tile.Prepared (x : Tokens 128) (len : ℕ) (scale : ℝ) (w : Tile) : Prop where
  decayedKey : ∀ t : Fin 16, w.decayedKey t = weighted (tileCum x len) (tileKey x len) t
  restoredKey : ∀ (t : Fin 16) (i : Fin 128),
    w.restoredKey t i = restored (tileCum x len) (tileKey x len) t i * tileCum x len 16 i
  totalDecay : w.totalDecay = tileCum x len 16
  inverse : unitLower (coefficient (tileCum x len) (tileKey x len) x.strength) * w.inverse = 1
  decayedQuery : ∀ t : Fin 16, t.val < len → ∀ i : Fin 128,
    w.decayedQuery t i = scale * weighted (tileCum x len) x.query t i
  score : ∀ t : Fin 16, t.val < len → ∀ j : Fin 16,
    w.score t j =
      if j ≤ t then dot (restored (tileCum x len) (tileKey x len) j) (w.decayedQuery t) else 0

end
end PTX.Kernels.FlashKdaFwd.Recurrence
