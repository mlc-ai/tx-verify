-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Sequence

@[expose] public section

/-!
One tile (16 consecutive tokens of one sequence and head) in the matrix form the recurrence
kernel executes. The preparation kernel stores six coefficient arrays per tile
(`Recurrence.Tile`, defined with the specification in `Data/Recurrence.lean`); the recurrence
kernel combines them with the state row, the values and the gate strengths (`Tile.apply`).

* `tile_correct`, `padded_results`: with the exact coefficients (`coefficients`, which uses the
  block inverse algorithm `Block.blockInverse`) the result is the token-by-token recurrence,
  whatever the values and strengths of the unused rows are.
* `Workspace.Prepared`: a tile that agrees with `coefficients` except in the unused rows of the
  decayed query and of the score matrix, where the preparation kernel leaves arbitrary numbers.
* `Recurrence.Tile.Prepared.toMath`: the specification's contract `Recurrence.Tile.Prepared`
  (stated without the inverse algorithm) implies `Workspace.Prepared`.
* `Recurrence.Tile.Prepared.results`, `results_rows`: a tile that satisfies the specification's
  contract computes the live outputs and the exit state of the recurrence.
-/

namespace PTX.Kernels.FlashKdaFwd.Recurrence
open Matrix
noncomputable section

/-- What the recurrence kernel computes from one tile `w`, the state row `s` that enters the
tile, and the values `v` and gate strengths `beta` of the 16 rows: the corrections
`u = INV · ((v - k_decayed · s) * beta)`, the outputs `q_decayed · s + Mqk · u` and the state
row `s * g_total + k_restoredᵀ · u` that leaves the tile. -/
def Tile.apply (w : Tile) (s : Row 128) (v beta : Fin 16 → ℝ) : (Fin 16 → ℝ) × Row 128 :=
  let u := w.inverse *ᵥ (fun t => (v t - dot s (w.decayedKey t)) * beta t)
  (fun t => dot s (w.decayedQuery t) + (w.score *ᵥ u) t,
   fun k => s k * w.totalDecay k + ∑ j, w.restoredKey j k * u j)

end
end PTX.Kernels.FlashKdaFwd.Recurrence

namespace PTX.Kernels.FlashKdaFwd.Math.Workspace
open Recurrence Sequence Chunk Block Algorithm Matrix Finset
noncomputable section

def factors (cum key query : Nat → Row 128) (strength : Nat → ℝ) (scale : ℝ) : Tile :=
  let q := fun (t : Full) i => scale * weighted cum query t i
  { decayedKey t := weighted cum key t
    decayedQuery := q
    restoredKey t i := restored cum key t i * cum 16 i
    totalDecay := cum 16
    inverse := blockInverse (coefficient cum key strength)
    score t j := if j ≤ t then dot (restored cum key j) (q t) else 0 }

def coefficients (x : Tokens 128) (len : Nat) (scale : ℝ) : Tile :=
  let key := fun t => if t < len then x.key t else fun _ => 0
  let query := fun t => if t < len then x.query t else fun _ => 0
  let cum := Recurrence.cum fun t => if t < len then x.logDecay t else fun _ => 0
  factors cum key query x.strength scale

private theorem prefix_sum (t : Full) (f : Nat → ℝ) :
    (∑ j : Full, if j ≤ t then f j.val else 0) = ∑ j ∈ range (t.val+1), f j := by
  change (∑ j : Fin 16, if j.val ≤ t.val then f j.val else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ t.val then f j else 0) 16]
  calc
    _ = ∑ j ∈ range (t.val+1), (if j ≤ t.val then f j else 0) := by
      symm
      apply sum_subset (range_mono (by omega))
      intro i _ h
      simp [show ¬i ≤ t.val by simpa using h]
    _ = _ := sum_congr rfl fun j hj => ite_eq_left (by have := mem_range.mp hj; omega)

theorem factor_products (s : Row 128) (cum key query : Nat → Row 128)
    (v beta : Nat → ℝ) (scale : ℝ) :
    let u := corrections s cum key v beta
    ((factors cum key query beta scale).apply s (fun t => v t) (fun t => beta t)) =
      (fun t : Full => blockOutput s cum key query u scale t, exitState s cum key u) := by
  let w := factors cum key query beta scale
  let u := corrections s cum key v beta
  let q := fun (t : Full) i => scale * weighted cum query t i
  have rhs_eq : (fun t : Full => (v t - dot s (w.decayedKey t)) * beta t) =
      rhs s cum key v beta := by
    funext t
    exact mul_comm ..
  have u_eq : w.inverse *ᵥ rhs s cum key v beta = fun t : Full => u t := by
    funext t
    simp only [w, factors, u, corrections, t.isLt, dite_true]
  change w.apply s _ _ = _
  unfold Tile.apply
  rw [rhs_eq, u_eq]
  apply Prod.ext
  · funext t
    change dot s (q t) + ∑ j : Full,
        (if j ≤ t then dot (restored cum key j) (q t) else 0) * u j = _
    simp only [ite_mul, zero_mul]
    rw [prefix_sum t (fun j => dot (restored cum key j) (q t) * u j)]
    change dot s (q t) + _ = dot s (q t) + _
    congr 1
    exact sum_congr rfl fun _ _ => mul_comm ..
  · funext k
    change s k * cum 16 k + (∑ j : Full, (restored cum key j k * cum 16 k) * u j) = _
    rw [Fin.sum_univ_eq_sum_range (fun j => (restored cum key j k * cum 16 k) * u j) 16]
    rfl

theorem tile_correct (x : Tokens 128) (s : Row 128) {len : Nat} (hlen : len ≤ 16) (scale : ℝ) :
    let y := (coefficients x len scale).apply s (fun t => x.value t) (fun t => x.strength t)
    (∀ t : Full, t.val < len → y.1 t = scale * dot (tokenState x s (t.val+1)) (x.query t)) ∧
      y.2 = tokenState x s len := by
  let key := fun t => if t < len then x.key t else fun _ => 0
  let query := fun t => if t < len then x.query t else fun _ => 0
  let cum := Recurrence.cum fun t => if t < len then x.logDecay t else fun _ => 0
  let u := corrections s cum key x.value x.strength
  have h := forward_chunk hlen s x.logDecay x.key x.query x.value x.strength scale
  dsimp only [coefficients]
  rw [factor_products s cum key query x.value x.strength scale]
  refine ⟨?_,h.2⟩
  intro t ht
  change blockOutput s cum key query u scale t = _
  have cur : blockOutput s cum key query u scale t = blockOutput s cum key x.query u scale t := by
    simp only [blockOutput, weighted, query, ht, ↓reduceIte]
  exact cur.trans (h.1 _ ht)

def extend (x : Tokens 128) (len : Nat) (v beta : Nat → ℝ) : Tokens 128 :=
  { x with value := fun t => if t < len then x.value t else v t
           strength := fun t => if t < len then x.strength t else beta t }

theorem padding_coefficients (x : Tokens 128) (len : Nat) (v beta : Nat → ℝ) (scale : ℝ) :
    coefficients (extend x len v beta) len scale = coefficients x len scale := by
  let cum := Recurrence.cum fun t => if t < len then x.logDecay t else fun _ => 0
  let key := fun t => if t < len then x.key t else fun _ => 0
  have same : coefficient cum key (extend x len v beta).strength = coefficient cum key x.strength :=
    by
      funext t j
      by_cases h : t < len
      · simp [coefficient, extend, h]
      · simp [coefficient, key, weighted, extend, h, dot]
  dsimp only [coefficients, factors]
  congr 2

private theorem through_live (x : Tokens 128) (s : Row 128) (len : Nat) (v beta : Nat → ℝ)
    (t : Nat) (h : t ≤ len) : tokenState (extend x len v beta) s t = tokenState x s t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht : t < len := by omega
    change step (tokenState (extend x len v beta) s t) _ _ _ _ =
      step (tokenState x s t) _ _ _ _
    rw [ih ht.le]
    simp [extend, ht]

theorem padded_results (x : Tokens 128) (s : Row 128) {len : Nat} (hlen : len ≤ 16)
    (v beta : Nat → ℝ) (scale : ℝ) :
    let padded := extend x len v beta
    let y := (coefficients x len scale).apply s
      (fun t => padded.value t) (fun t => padded.strength t)
    (∀ t : Full, t.val < len → y.1 t = scale * dot (tokenState x s (t.val+1)) (x.query t)) ∧
      y.2 = tokenState x s len := by
  have h := tile_correct (extend x len v beta) s hlen scale
  rw [padding_coefficients] at h
  refine ⟨?_, h.2.trans (through_live x s len v beta len (by omega))⟩
  intro t ht
  rw [← through_live x s len v beta (t.val+1) (by omega)]
  exact h.1 t ht

/-- `w` is a prepared tile for `len` live rows: it agrees with `coefficients x len scale`
everywhere except that rows `t ≥ len` of `decayedQuery` and of `score` are arbitrary. The
preparation kernel zeroes only the key rows of a partial tile, so these two arrays hold
unspecified numbers in the unused rows. The specification's `Recurrence.Tile.Prepared` says the
same without naming the inverse algorithm (`Recurrence.Tile.Prepared.toMath`). -/
structure Prepared (x : Tokens 128) (len : ℕ) (scale : ℝ) (w : Tile) : Prop where
  decayedKey : w.decayedKey = (coefficients x len scale).decayedKey
  restoredKey : w.restoredKey = (coefficients x len scale).restoredKey
  totalDecay : w.totalDecay = (coefficients x len scale).totalDecay
  inverse : w.inverse = (coefficients x len scale).inverse
  decayedQuery : ∀ t : Full, t.val < len →
    w.decayedQuery t = (coefficients x len scale).decayedQuery t
  score : ∀ t : Full, t.val < len → ∀ j, w.score t j = (coefficients x len scale).score t j

/-- The exact coefficients are a prepared tile. -/
theorem Prepared.exact (x : Tokens 128) (len : ℕ) (scale : ℝ) :
    Prepared x len scale (coefficients x len scale) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The exit state does not read `decayedQuery` or `score`. -/
theorem Prepared.apply_snd {x : Tokens 128} {len : ℕ} {scale : ℝ} {w : Tile}
    (hw : Prepared x len scale w) (s : Row 128) (v beta : Full → ℝ) :
    (w.apply s v beta).2 = ((coefficients x len scale).apply s v beta).2 := by
  simp only [Tile.apply, hw.decayedKey, hw.restoredKey, hw.totalDecay, hw.inverse]

/-- The output of row `t` reads only row `t` of `decayedQuery` and of `score`. -/
theorem Prepared.apply_fst {x : Tokens 128} {len : ℕ} {scale : ℝ} {w : Tile}
    (hw : Prepared x len scale w) (s : Row 128) (v beta : Full → ℝ) (t : Full)
    (ht : t.val < len) :
    (w.apply s v beta).1 t = ((coefficients x len scale).apply s v beta).1 t := by
  simp only [Tile.apply, mulVec, dotProduct, hw.decayedKey, hw.inverse, hw.decayedQuery t ht,
    hw.score t ht]

/-- A prepared tile computes the live outputs and the exit state of the token-by-token
recurrence. Only the values and strengths of the live rows matter. -/
theorem Prepared.results {x : Tokens 128} {len : ℕ} {scale : ℝ} {w : Tile}
    (hw : Prepared x len scale w) (s : Row 128) (hlen : len ≤ 16) (v beta : ℕ → ℝ)
    (hv : ∀ t < len, v t = x.value t) (hb : ∀ t < len, beta t = x.strength t) :
    let y := w.apply s (fun t => v t) (fun t => beta t)
    (∀ t : Full, t.val < len → y.1 t = scale * dot (tokenState x s (t.val+1)) (x.query t)) ∧
      y.2 = tokenState x s len := by
  have h := padded_results x s hlen v beta scale
  have ev : (extend x len v beta).value = v := by
    funext t
    change (if t < len then x.value t else v t) = v t
    split
    · next ht => exact (hv t ht).symm
    · rfl
  have eb : (extend x len v beta).strength = beta := by
    funext t
    change (if t < len then x.strength t else beta t) = beta t
    split
    · next ht => exact (hb t ht).symm
    · rfl
  dsimp only at h ⊢
  rw [ev, eb] at h
  exact ⟨fun t ht => (hw.apply_fst s _ _ t ht).trans (h.1 t ht),
    (hw.apply_snd s _ _).trans h.2⟩

/-- `Prepared.results` for values and strengths given per row of the tile. -/
theorem Prepared.results_rows {x : Tokens 128} {len : ℕ} {scale : ℝ} {w : Tile}
    (hw : Prepared x len scale w) (s : Row 128) (hlen : len ≤ 16) (v beta : Full → ℝ)
    (hv : ∀ t : Full, t.val < len → v t = x.value t)
    (hb : ∀ t : Full, t.val < len → beta t = x.strength t) :
    let y := w.apply s v beta
    (∀ t : Full, t.val < len → y.1 t = scale * dot (tokenState x s (t.val+1)) (x.query t)) ∧
      y.2 = tokenState x s len :=
  hw.results s hlen (fun t => if h : t < 16 then v ⟨t, h⟩ else 0)
    (fun t => if h : t < 16 then beta ⟨t, h⟩ else 0)
    (fun t ht => by rw [dite_eq_left (by omega : t < 16)]; exact hv ⟨t, by omega⟩ ht)
    (fun t ht => by rw [dite_eq_left (by omega : t < 16)]; exact hb ⟨t, by omega⟩ ht)

end
end PTX.Kernels.FlashKdaFwd.Math.Workspace

namespace PTX.Kernels.FlashKdaFwd.Recurrence
open Math Math.Workspace Math.Block
noncomputable section

variable {x : Tokens 128} {len : ℕ} {scale : ℝ} {w : Tile}

/-- The specification's contract for a prepared tile implies the contract the proofs use: the
matrix it calls the inverse of `I + L` is the one the block inverse algorithm computes, and in
the live rows the masked query is the query. -/
theorem Tile.Prepared.toMath (hw : w.Prepared x len scale) :
    Workspace.Prepared x len scale w := by
  have hq : ∀ t : Fin 16, t.val < len →
      w.decayedQuery t = (coefficients x len scale).decayedQuery t := by
    intro t ht
    funext i
    rw [hw.decayedQuery t ht i]
    change scale * (tileCum x len (t.val + 1) i * x.query t i) =
      scale * (tileCum x len (t.val + 1) i * (if t.val < len then x.query t else fun _ => 0) i)
    rw [ite_eq_left ht]
  refine ⟨?_, ?_, ?_, ?_, hq, ?_⟩
  · funext t
    exact hw.decayedKey t
  · funext t i
    exact hw.restoredKey t i
  · exact hw.totalDecay
  · exact blockInverse_unique hw.inverse
  · intro t ht j
    rw [hw.score t ht j, hq t ht]
    rfl

/-- A tile that satisfies the specification's contract computes the live outputs and the exit
state of the token-by-token recurrence. Only the values and strengths of the live rows
matter. -/
theorem Tile.Prepared.results (hw : w.Prepared x len scale) (s : Row 128) (hlen : len ≤ 16)
    (v beta : ℕ → ℝ) (hv : ∀ t < len, v t = x.value t) (hb : ∀ t < len, beta t = x.strength t) :
    let y := w.apply s (fun t => v t) (fun t => beta t)
    (∀ t : Fin 16, t.val < len → y.1 t = scale * dot (tokenState x s (t.val+1)) (x.query t)) ∧
      y.2 = tokenState x s len :=
  hw.toMath.results s hlen v beta hv hb

/-- `Tile.Prepared.results` for values and strengths given per row of the tile. -/
theorem Tile.Prepared.results_rows (hw : w.Prepared x len scale) (s : Row 128) (hlen : len ≤ 16)
    (v beta : Fin 16 → ℝ) (hv : ∀ t : Fin 16, t.val < len → v t = x.value t)
    (hb : ∀ t : Fin 16, t.val < len → beta t = x.strength t) :
    let y := w.apply s v beta
    (∀ t : Fin 16, t.val < len → y.1 t = scale * dot (tokenState x s (t.val+1)) (x.query t)) ∧
      y.2 = tokenState x s len :=
  hw.toMath.results_rows s hlen v beta hv hb

end
end PTX.Kernels.FlashKdaFwd.Recurrence
