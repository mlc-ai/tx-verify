-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Tile

@[expose] public section

/-!
Chaining tiles over one whole sequence, as the recurrence kernel does for one head and one value
channel. Tile `b` covers the tokens `16*b, …, 16*b + liveRows total b - 1`; the state row that
leaves tile `b` enters tile `b+1` (`carry`).

The theorems take any family of tiles that satisfy the specification's workspace contract
(`Recurrence.Tile.Prepared`, which leaves the unused rows of a partial tile unspecified) and any
per-tile values and strengths that agree with the token stream on the live rows. They conclude
that every live output and the final state are those of the token-by-token recurrence
`Recurrence.tokenState`:

* `carry_eq`: the state that enters tile `b`;
* `tile_output`, `output_eq`: the output of a live row, addressed by tile and row or by token;
* `carry_final`: the state after the last tile.
-/

namespace PTX.Kernels.FlashKdaFwd.Math.Run
open Recurrence Sequence Chunk Block Algorithm Workspace
noncomputable section

/-- The state row that enters tile `b` when the tiles `w 0, w 1, …` are applied in order to the
initial state `s0`, with the values `v b` and the strengths `beta b` in tile `b`. -/
def carry (w : ℕ → Tile) (v beta : ℕ → Full → ℝ) (s0 : Row 128) : ℕ → Row 128
  | 0 => s0
  | b+1 => ((w b).apply (carry w v beta s0 b) (v b) (beta b)).2

variable {x : Tokens 128} {total : ℕ} {scale : ℝ} {w : ℕ → Tile} {v beta : ℕ → Full → ℝ}

/-- A tile that exists starts at token `16*b`. -/
theorem cursor_of_lt {total b : ℕ} (h : b < tiles total) : cursor total b = 16*b := by
  unfold tiles at h
  unfold cursor
  omega

/-- The state that enters tile `b` is the state of the recurrence after the tokens before it. -/
theorem carry_eq
    (hw : ∀ b, b < tiles total → (w b).Prepared (suffix x (16*b)) (liveRows total b) scale)
    (hv : ∀ b (t : Full), t.val < liveRows total b → v b t = x.value (16*b + t.val))
    (hb : ∀ b (t : Full), t.val < liveRows total b → beta b t = x.strength (16*b + t.val))
    (s0 : Row 128) {b : ℕ} (h : b ≤ tiles total) :
    carry w v beta s0 b = tokenState x s0 (cursor total b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hlt : b < tiles total := h
    have tile := (hw b hlt).results_rows (carry w v beta s0 b) (live_le total b) (v b) (beta b)
      (hv b) (hb b)
    rw [carry, tile.2, ih hlt.le, cursor_of_lt hlt, state_shift, ← cursor_of_lt hlt, next_cursor]

/-- The output of live row `r` of tile `b` is the output of token `16*b + r`. -/
theorem tile_output
    (hw : ∀ b, b < tiles total → (w b).Prepared (suffix x (16*b)) (liveRows total b) scale)
    (hv : ∀ b (t : Full), t.val < liveRows total b → v b t = x.value (16*b + t.val))
    (hb : ∀ b (t : Full), t.val < liveRows total b → beta b t = x.strength (16*b + t.val))
    (s0 : Row 128) {b : ℕ} (r : Full) (hr : r.val < liveRows total b) :
    ((w b).apply (carry w v beta s0 b) (v b) (beta b)).1 r =
      scale * dot (tokenState x s0 (16*b + r.val + 1)) (x.query (16*b + r.val)) := by
  have hlt : b < tiles total := by
    unfold liveRows cursor at hr
    unfold tiles
    omega
  have tile := (hw b hlt).results_rows (carry w v beta s0 b) (live_le total b) (v b) (beta b)
    (hv b) (hb b)
  rw [tile.1 r hr, carry_eq hw hv hb s0 hlt.le, cursor_of_lt hlt, state_shift]
  rfl

/-- The output computed for token `t` is the output of the recurrence. -/
theorem output_eq
    (hw : ∀ b, b < tiles total → (w b).Prepared (suffix x (16*b)) (liveRows total b) scale)
    (hv : ∀ b (t : Full), t.val < liveRows total b → v b t = x.value (16*b + t.val))
    (hb : ∀ b (t : Full), t.val < liveRows total b → beta b t = x.strength (16*b + t.val))
    (s0 : Row 128) {t : ℕ} (ht : t < total) :
    ((w (t/16)).apply (carry w v beta s0 (t/16)) (v (t/16)) (beta (t/16))).1
        ⟨t % 16, Nat.mod_lt t (by decide)⟩ =
      scale * dot (tokenState x s0 (t+1)) (x.query t) := by
  have live : t % 16 < liveRows total (t/16) := by
    unfold liveRows cursor
    omega
  rw [tile_output hw hv hb s0 ⟨t % 16, Nat.mod_lt t (by decide)⟩ live]
  change _ * dot (tokenState x s0 (16*(t/16) + t%16 + 1)) (x.query (16*(t/16) + t%16)) = _
  rw [show 16*(t/16) + t%16 = t by omega]

/-- The state after the last tile is the state of the recurrence after all tokens. -/
theorem carry_final
    (hw : ∀ b, b < tiles total → (w b).Prepared (suffix x (16*b)) (liveRows total b) scale)
    (hv : ∀ b (t : Full), t.val < liveRows total b → v b t = x.value (16*b + t.val))
    (hb : ∀ b (t : Full), t.val < liveRows total b → beta b t = x.strength (16*b + t.val))
    (s0 : Row 128) :
    carry w v beta s0 (tiles total) = tokenState x s0 total := by
  rw [carry_eq hw hv hb s0 le_rfl]
  congr 1
  unfold cursor tiles
  omega

end
end PTX.Kernels.FlashKdaFwd.Math.Run
