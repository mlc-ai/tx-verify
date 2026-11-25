-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Fragments
public import Kernels.FlashKdaFwd.Spec

@[expose] public section

/-!
# The real arrays of a tile, from the launch

The value induction speaks of the real arrays of each tile as a family
`xs : ℕ → Math.Fragments.Inputs`. This file defines the family that the kernel's precondition
(`Pre P L mem0`) determines for the thread block of sequence `s` and head `h`:
`tileInputs P mem0 s h b` for tile `b`.

* The six workspace arrays are the numbers `P.tile s h b` (zero outside their index ranges).
* `value` and `logit` are what launch memory holds at the rows the tile's tensor loads read:
  row `t` of the tile is the global token `firstToken P.length s + 16 * b + t`, and its element
  is the number of the bfloat16 bit pattern stored there (`bf16Num`), or zero when the load is
  past the end of its array: for `v` (token-major) when the token is past the end of the packed
  batch (`P.total`); for `beta` (a flat `[H, T_total]` array) when the flat index
  `h * P.total + token` is past `P.heads * P.total`, so that a padding row past the end of the
  batch reads the first tokens of the next head. For the tokens of the sequence these are
  `P.value s h (16 * b + t)` and `P.betaLogit s h (16 * b + t)`; the padding rows of a partial
  tile hold the numbers of the tokens that follow the sequence.
* `copy` and `carry`, the two views of the state before the tile, are both the real state after
  the tokens before the tile (`tileState`: `P.state` after `min (16 * b) (P.length s)` tokens;
  the bound makes tile number `tiles (P.length s)` the final state).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX
open PTX.Kernels.FlashKdaFwd.Math.Fragments
open PTX.Kernels.FlashKdaFwd.Recurrence (firstToken)

noncomputable section

/-- The number of the finite bfloat16 bit pattern that launch memory holds at `l` (zero when
the two bytes there are no such pattern). -/
def bf16Num (m : Mem0) (l : Loc) : ℝ :=
  open Classical in if h : ∃ x : ℝ, bf16Bits m l x then h.choose else 0

/-- The state of sequence `s` and head `h` before tile `b`, as `[key feature][value channel]`
(zero outside the 128 × 128 entries). -/
def tileState (P : Params) (s h b : ℕ) (k ch : ℕ) : ℝ :=
  if hk : k < 128 ∧ ch < 128 then
    P.state s h ⟨ch, hk.2⟩ (min (16 * b) (P.length s)) ⟨k, hk.1⟩
  else 0

/-- **The real arrays of tile `b`** of sequence `s` and head `h`. -/
def tileInputs (P : Params) (mem0 : Mem0) (s h b : ℕ) : Inputs :=
  Inputs.ofTile (P.tile s h b)
    (fun t ch =>
      if hc : firstToken P.length s + 16 * b + t < P.total ∧ ch < 128 then
        bf16Num mem0 (P.valueLoc (firstToken P.length s + 16 * b + t) h ⟨ch, hc.2⟩)
      else 0)
    (fun t =>
      if h * P.total + (firstToken P.length s + 16 * b + t) < P.heads * P.total then
        bf16Num mem0 (P.logitLoc h (firstToken P.length s + 16 * b + t))
      else 0)
    (tileState P s h b) (tileState P s h b)

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
