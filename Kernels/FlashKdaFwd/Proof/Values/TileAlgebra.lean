-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Batches
public import Kernels.FlashKdaFwd.Proof.Values.Tables
public import Kernels.FlashKdaFwd.Proof.Values.TileInputs

@[expose] public section

/-!
# The real arrays of the tiles compute the specified result

Real numbers only: no machine state occurs here. `TileInputs.lean` defines, from the kernel's
precondition `Pre P L mem0` (the launch `L` and the memory `mem0` before it, described by the
parameters `P`), the real arrays `tileInputs P mem0 s h b` that tile `b` of sequence `s` and
head `h` reads. This file proves that these arrays are a chain of tiles whose outputs and final
state are the numbers the postcondition names.

Words. A *tile* is 16 consecutive tokens of one sequence, its *rows*. A sequence of
`P.length s` tokens has `tiles (P.length s)` tiles; row `t` of tile `b` is the token
`16 * b + t`. The row is *live* when that token exists (`16 * b + t < P.length s`) and a
*padding* row otherwise; `liveRows (P.length s) b` is the number of live rows of tile `b`. A
*key feature* is one of the 128 coordinates of a key and a *value channel* one of the 128
coordinates of a value; the state is a 128 × 128 array `[key feature][value channel]`.

Names of the specification (`Spec.lean`): `P.value`, `P.betaLogit` and `P.initial` are the
values, the gate logits and the initial state that the launch memory holds; `P.tile s h b` are
the numbers the workspace holds for tile `b`; `P.tokens s h v` is the token stream of value
channel `v`, `P.state s h v n` the state row of that channel after `n` tokens and
`P.output s h n v` the output of token `n`.

Names of `Math/Fragments.lean`: `Inputs` is the record of the real arrays of one tile, with the
fields `value` (`[row][value channel]`), `logit` (the gate logit of each row), `copy` and
`carry` (the two views of the state before the tile); `x.Holds w` says the six workspace arrays
of `x` are those of the tile `w`; `outputs x t ch` is the output the tile computes for row `t`
and channel `ch`, and `stateAfter x k ch` the state entry of key feature `k` and channel `ch`
that it leaves. `Recurrence.Tile.apply w` is the same computation for one channel: from the
state row, the values and the gate strengths of the 16 rows (`column`, `values` and
`strengths` of an `Inputs`) it gives the 16 outputs and the state row after the tile.
`Math.Run.carry` is the state row that enters each tile when `Tile.apply` is iterated from the
initial state.

## Results

* `bf16Num_eq`: `bf16Num m l`, the number of the bfloat16 bit pattern that `m` holds at `l`, is
  `x` when the precondition says the two bytes there are a pattern of `x` (`bf16Bits m l x`).
  The reason is `bf16Bits_unique`: two bytes hold one pattern.
* `tileInputs_holds`, `tileInputs_copy`: the workspace arrays are those of `P.tile s h b`, and
  the two views of the state are equal.
* `tileInputs_value`, `tileInputs_logit`: in a live row the value and the gate logit are the
  specification's `P.value` and `P.betaLogit` of the token.
* `tileInputs_first`, `tileInputs_last`: the state before tile `0` is the initial state
  `P.initial`, and the state before tile number `tiles (P.length s)`, which is no tile of the
  sequence, is the final state `P.state … (P.length s)`.
* `tileState_run`: the state before tile `b` (`tileState`, the specification's state after the
  tokens before the tile) is `Math.Run.carry` of the tiles `P.tile s h`. This is
  `Math.Run.carry_eq`, the theorem that a chain of prepared tiles follows the token-by-token
  recurrence; the field `prepared` of the precondition supplies its first hypothesis (the
  workspace numbers are what the preparation kernel computes from the tokens of the tile). Its
  other two hypotheses constrain the values and the gate strengths in the live rows only, so
  the numbers `tileInputs` has in the padding rows of a partial tile do not matter.
* `tileInputs_chain`: the family is a chain (`Chain` of `Tables.lean`): the state before tile
  `b + 1` is `stateAfter` of tile `b`.
* `tileInputs_output`: the output of a live row is the specification's `P.output`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX
open PTX.Kernels.FlashKdaFwd.Math.Fragments
open PTX.Kernels.FlashKdaFwd.Recurrence (tiles firstToken liveRows cursor strength)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {s h b t k ch : ℕ}

/-! ## The number of a stored bit pattern -/

/-- The two bytes at a location are the bfloat16 pattern of at most one number: byte 0 names the
16-bit integer it is a byte of, a pattern below `65536` is determined by that integer, and the
pattern determines the number. -/
theorem bf16Bits_unique {m : Mem0} {l : Loc} {x y : ℝ} (hx : bf16Bits m l x)
    (hy : bf16Bits m l y) : x = y := by
  obtain ⟨n, hn, q, hq, rfl, hb⟩ := hx
  obtain ⟨n', hn', q', hq', rfl, hb'⟩ := hy
  have h0 := (hb 0 (by norm_num)).symm.trans (hb' 0 (by norm_num))
  have hv : Value.bits 16 (BitVec.ofNat 64 n) = Value.bits 16 (BitVec.ofNat 64 n') :=
    (Prod.mk.inj (Option.some.inj (Option.some.inj h0))).1
  have hbv : BitVec.ofNat 64 n = BitVec.ofNat 64 n' := by injection hv
  have hnn : n = n' := by
    have e := congrArg BitVec.toNat hbv
    simp only [BitVec.toNat_ofNat] at e
    omega
  subst hnn
  rw [hq] at hq'
  rw [Option.some.inj hq']

/-- **The number of a stored pattern.** When the two bytes at `l` are the bfloat16 pattern of
`x`, the number `bf16Num m l` read off them is `x`. -/
theorem bf16Num_eq {m : Mem0} {l : Loc} {x : ℝ} (hx : bf16Bits m l x) : bf16Num m l = x := by
  have hex : ∃ y : ℝ, bf16Bits m l y := ⟨x, hx⟩
  rw [bf16Num, dite_eq_left hex]
  exact bf16Bits_unique hex.choose_spec hx

/-! ## The arrays of one tile -/

/-- The workspace arrays of `tileInputs P mem0 s h b` are those of the tile `P.tile s h b`. -/
theorem tileInputs_holds (P : Params) (mem0 : Mem0) (s h b : ℕ) :
    (tileInputs P mem0 s h b).Holds (P.tile s h b) :=
  Inputs.ofTile_holds ..

/-- The two views of the state before a tile are the same numbers. -/
theorem tileInputs_copy (P : Params) (mem0 : Mem0) (s h b : ℕ) :
    (tileInputs P mem0 s h b).copy = (tileInputs P mem0 s h b).carry :=
  rfl

/-- The state before tile `b`, at a key feature and a value channel below 128. -/
theorem tileState_eq (P : Params) (s h b : ℕ) (hk : k < 128) (hch : ch < 128) :
    tileState P s h b k ch = P.state s h ⟨ch, hch⟩ (min (16 * b) (P.length s)) ⟨k, hk⟩ :=
  dite_eq_left ⟨hk, hch⟩

/-- **The state before the first tile** is the initial state. -/
theorem tileInputs_first (P : Params) (mem0 : Mem0) (s h : ℕ) (hk : k < 128) (hch : ch < 128) :
    (tileInputs P mem0 s h 0).carry k ch = P.initial s h ⟨ch, hch⟩ ⟨k, hk⟩ := by
  change tileState P s h 0 k ch = _
  rw [tileState_eq P s h 0 hk hch, Nat.mul_zero, Nat.zero_min]
  rfl

/-- **The state after the last tile** (the carry of the family's entry number
`tiles (P.length s)`) is the state after all tokens of the sequence. -/
theorem tileInputs_last (P : Params) (mem0 : Mem0) (s h : ℕ) (hk : k < 128) (hch : ch < 128) :
    (tileInputs P mem0 s h (tiles (P.length s))).carry k ch =
      P.state s h ⟨ch, hch⟩ (P.length s) ⟨k, hk⟩ := by
  change tileState P s h (tiles (P.length s)) k ch = _
  rw [tileState_eq P s h _ hk hch, min_eq_right (by unfold tiles; omega)]

/-- A token of sequence `s` is a token of the packed batch. -/
theorem token_lt_total (hs : s < P.sequences) (ht : 16 * b + t < P.length s) :
    firstToken P.length s + 16 * b + t < P.total := by
  have e := Math.Batches.token_lt_end P.length hs ht
  change firstToken P.length s + 16 * b + t < firstToken P.length P.sequences
  omega

/-- **The values of a live row** are the specification's values of its token. -/
theorem tileInputs_value (hpre : Pre P L mem0) (hs : s < P.sequences) (hh : h < P.heads)
    (ht : 16 * b + t < P.length s) (hch : ch < 128) :
    (tileInputs P mem0 s h b).value t ch = P.value s h (16 * b + t) ⟨ch, hch⟩ := by
  change (if hc : firstToken P.length s + 16 * b + t < P.total ∧ ch < 128 then
    bf16Num mem0 (P.valueLoc (firstToken P.length s + 16 * b + t) h ⟨ch, hc.2⟩) else 0) = _
  rw [dite_eq_left ⟨token_lt_total hs ht, hch⟩]
  have e := hpre.values s hs h hh (16 * b + t) ht ⟨ch, hch⟩
  rw [← Nat.add_assoc] at e
  exact bf16Num_eq e

/-- **The gate logit of a live row** is the specification's gate logit of its token. -/
theorem tileInputs_logit (hpre : Pre P L mem0) (hs : s < P.sequences) (hh : h < P.heads)
    (ht : 16 * b + t < P.length s) :
    (tileInputs P mem0 s h b).logit t = P.betaLogit s h (16 * b + t) := by
  change (if h * P.total + (firstToken P.length s + 16 * b + t) < P.heads * P.total then
    bf16Num mem0 (P.logitLoc h (firstToken P.length s + 16 * b + t)) else 0) = _
  have hflat : h * P.total + (firstToken P.length s + 16 * b + t) < P.heads * P.total :=
    calc _ < h * P.total + P.total := by have := token_lt_total hs ht; omega
      _ = (h + 1) * P.total := (Nat.succ_mul _ _).symm
      _ ≤ P.heads * P.total := Nat.mul_le_mul_right _ hh
  rw [ite_eq_left hflat]
  have e := hpre.logits s hs h hh (16 * b + t) ht
  rw [← Nat.add_assoc] at e
  exact bf16Num_eq e

/-! ## The chain of tiles -/

/-- A row below the number of live rows of tile `b` is a token of the sequence. -/
theorem live_token {total : ℕ} (ht : t < liveRows total b) : 16 * b + t < total := by
  unfold liveRows cursor at ht
  omega

/-- In the live rows of every tile the values of channel `ch` are those of the token stream
`P.tokens s h ch`: the second hypothesis of the theorems of `Math/Run.lean`. -/
theorem tileInputs_values (hpre : Pre P L mem0) (hs : s < P.sequences) (hh : h < P.heads)
    (hch : ch < 128) (b : ℕ) (t : Fin 16) (ht : t.val < liveRows (P.length s) b) :
    values (tileInputs P mem0 s h b) ch t = (P.tokens s h ⟨ch, hch⟩).value (16 * b + t.val) :=
  tileInputs_value hpre hs hh (live_token ht) hch

/-- In the live rows of every tile the gate strengths are those of the token stream: the third
hypothesis of the theorems of `Math/Run.lean`. -/
theorem tileInputs_strengths (hpre : Pre P L mem0) (hs : s < P.sequences) (hh : h < P.heads)
    (v : Fin 128) (b : ℕ) (t : Fin 16) (ht : t.val < liveRows (P.length s) b) :
    strengths (tileInputs P mem0 s h b) t = (P.tokens s h v).strength (16 * b + t.val) :=
  congrArg strength (tileInputs_logit hpre hs hh (live_token ht))

/-- **The state before tile `b` is the carry of the chain of tiles.** For a value channel `ch`
and `b ≤ tiles (P.length s)`, the specification's state after the tokens before tile `b` is the
state `Math.Run.carry` that enters tile `b` when the tiles `P.tile s h` are applied in order to
the initial state, with the values and gate strengths of `tileInputs`. -/
theorem tileState_run (hpre : Pre P L mem0) (hs : s < P.sequences) (hh : h < P.heads)
    (hch : ch < 128) (hb : b ≤ tiles (P.length s)) :
    column (tileState P s h b) ch =
      Math.Run.carry (P.tile s h) (fun b => values (tileInputs P mem0 s h b) ch)
        (fun b => strengths (tileInputs P mem0 s h b)) (P.initial s h ⟨ch, hch⟩) b := by
  rw [Math.Run.carry_eq (fun b hb => hpre.prepared s hs h hh b hb ⟨ch, hch⟩)
    (tileInputs_values hpre hs hh hch) (tileInputs_strengths hpre hs hh ⟨ch, hch⟩) _ hb]
  funext k
  exact tileState_eq P s h b k.isLt hch

/-- **The tiles form a chain.** For every tile `b` of the sequence, the state before tile
`b + 1` is the state tile `b` leaves (`stateAfter`), at the 128 key features and the 128 value
channels. -/
theorem tileInputs_chain (hpre : Pre P L mem0) (hs : s < P.sequences) (hh : h < P.heads) :
    Chain (fun b => tileInputs P mem0 s h b) (tiles (P.length s)) := by
  intro b hb k ch hk hch
  have e : stateAfter (tileInputs P mem0 s h b) k ch = _ :=
    stateAfter_eq (tileInputs_holds P mem0 s h b) (ch := ch) (fun _ => rfl) ⟨k, hk⟩
  have h1 := congrFun (tileState_run (mem0 := mem0) hpre hs hh hch (Nat.succ_le_of_lt hb)) ⟨k, hk⟩
  have h0 := tileState_run (mem0 := mem0) hpre hs hh hch hb.le
  change column (tileState P s h (b + 1)) ch ⟨k, hk⟩ = stateAfter (tileInputs P mem0 s h b) k ch
  rw [e, h1]
  change ((P.tile s h b).apply (Math.Run.carry _ _ _ _ b) _ _).2 ⟨k, hk⟩ =
    ((P.tile s h b).apply (column (tileState P s h b) ch) _ _).2 ⟨k, hk⟩
  rw [h0]

/-- **The outputs of a tile.** For a live row `t` of tile `b` (a row `t < 16` whose token
`16 * b + t` is a token of the sequence) and a value channel `ch`, the output the tile computes
is the specification's output of that token. -/
theorem tileInputs_output (hpre : Pre P L mem0) (hs : s < P.sequences) (hh : h < P.heads)
    (ht : t < 16) (hlive : 16 * b + t < P.length s) (hch : ch < 128) :
    outputs (tileInputs P mem0 s h b) t ch = P.output s h (16 * b + t) ⟨ch, hch⟩ := by
  have hb : b < tiles (P.length s) := by unfold tiles; omega
  have e : outputs (tileInputs P mem0 s h b) t ch = _ :=
    outputs_eq (tileInputs_holds P mem0 s h b) (ch := ch) (fun _ => rfl) ⟨t, ht⟩
  rw [e]
  change ((P.tile s h b).apply (column (tileState P s h b) ch) _ _).1 ⟨t, ht⟩ = _
  rw [tileState_run (mem0 := mem0) hpre hs hh hch hb.le]
  exact Math.Run.tile_output (fun b hb => hpre.prepared s hs h hh b hb ⟨ch, hch⟩)
    (tileInputs_values hpre hs hh hch) (tileInputs_strengths hpre hs hh ⟨ch, hch⟩) _ ⟨t, ht⟩
    (by unfold liveRows cursor; change t < _; omega)

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
