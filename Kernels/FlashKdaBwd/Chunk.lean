-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaBwd.Public
public import Kernels.FlashKdaBwd.FlaStages
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring

/-! # The chunked KDA graph differentiated by FLA
FLA solves the triangular system once and applies its inverse separately to weighted values
and weighted keys. It subtracts the second product applied to the incoming state. -/
@[expose] public section
namespace FlashKda.Backward.Fla
open Chunk Algorithm Sequence Inverse Matrix Finset
open scoped Matrix
noncomputable section
variable {d : ℕ}

def inverseTile (n : ℕ) (a : ℕ → ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => inverseEntry a i j

/-- The triangular solve is a finite polynomial in the lower-triangular entries. -/
theorem inverseEntry_diff {a : ℝ → ℕ → ℕ → ℝ} {t : ℝ}
    (ha : ∀ i j, DifferentiableAt ℝ (fun z => a z i j) t) (r c : ℕ) :
    DifferentiableAt ℝ (fun z => inverseEntry (a z) r c) t := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    simp_rw [entry_eq _ r c]
    exact (differentiableAt_const (delta r c)).sub (DifferentiableAt.fun_sum fun j hj =>
      (ha r j).mul (ih j (mem_range.mp hj)))

/-- Both solve identities used by the chunk backward hold for the actual triangular inverse
and its coordinatewise derivative along every differentiable path of coefficients. -/
theorem inverse_path (n : ℕ) {a : ℝ → ℕ → ℕ → ℝ} {t : ℝ}
    (ha : ∀ i j, DifferentiableAt ℝ (fun z => a z i j) t) :
    let sys := fun z => system n (a z)
    let inv := fun z => inverseTile n (a z)
    let ds := Matrix.of fun i j => deriv (fun z => sys z i j) t
    let di := Matrix.of fun i j => deriv (fun z => inv z i j) t
    inv t * sys t = 1 ∧ sys t * di + ds * inv t = 0 := by
  dsimp only
  have h z : system n (a z) * inverseTile n (a z) = 1 := diagonal_inverse n (a z)
  refine ⟨mul_eq_one_comm.mp (h t), ?_⟩
  ext i j
  have hs (k : Fin n) : DifferentiableAt ℝ (fun z => system n (a z) i k) t := by
    by_cases hk : k.val < i.val
    · simpa [system, hk] using ha i k
    · simp [system, hk]
  have hp := HasDerivAt.fun_sum (u := univ) (fun k _ =>
    (hs k).hasDerivAt.mul (inverseEntry_diff ha k j).hasDerivAt)
  have eqv : (fun z => ∑ k : Fin n, system n (a z) i k * inverseEntry (a z) k j) =
      fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    funext z
    exact congrArg (fun m : Matrix (Fin n) (Fin n) ℝ => m i j) (h z)
  have hz := hp.unique (eqv ▸ hasDerivAt_const t ((1 : Matrix (Fin n) (Fin n) ℝ) i j))
  simpa only [Matrix.add_apply, Matrix.mul_apply, of_apply, Matrix.zero_apply, inverseTile,
    sum_add_distrib, add_comm, Pi.mul_apply] using hz

def keyTile (n : ℕ) (x : Tokens d) : Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of fun t i => x.strength t * weighted (cum x.logDecay) x.key t i

def valueTile (n : ℕ) (x : Tokens d) (t : Fin n) := x.strength t * x.value t

/-- FLA's corrected value tensor: form the two products, then apply the incoming state. -/
def correction (n : ℕ) (x : Tokens d) (s : Row d) (t : ℕ) : ℝ :=
  let a := Block.coefficient (cum x.logDecay) x.key x.strength
  let inv := inverseTile n a
  let u := inv *ᵥ valueTile n x
  let w := inv * keyTile n x
  if h : t < n then (u - w *ᵥ s) ⟨t,h⟩ else 0

theorem correction_solves (n : ℕ) (x : Tokens d) (s : Row d) :
    Solves n s (cum x.logDecay) x.key x.value x.strength (correction n x s) := by
  let a := Block.coefficient (cum x.logDecay) x.key x.strength
  let c := correction n x s
  have hc : (fun j : Fin n => c j) = inverseTile n a *ᵥ
      (valueTile n x - keyTile n x *ᵥ s) := by
    rw [mulVec_sub, mulVec_mulVec]
    funext j
    simp [c, correction, a, j.isLt]
  have solved : system n a *ᵥ (fun j : Fin n => c j) = valueTile n x - keyTile n x *ᵥ s := by
    rw [hc, mulVec_mulVec, inverseTile, diagonal_inverse, one_mulVec]
  intro t ht
  have h := congrFun solved (⟨t,ht⟩ : Fin n)
  change (∑ j : Fin n, (if j.val < t then a t j else delta t j) * c j) =
    x.strength t * x.value t - ∑ i, (x.strength t * weighted (cum x.logDecay) x.key t i) * s i at h
  rw [Fin.sum_univ_eq_sum_range (fun j => (if j < t then a t j else delta t j) * c j) n,
    row_sum ht] at h
  change c t = _
  rw [eq_sub_of_add_eq h]
  simp only [a, Block.coefficient, mul_sub, mul_sum, Chunk.dot, mul_assoc]
  congr 1
  · congr 1
    apply sum_congr rfl
    intro i _
    ring
  · apply sum_congr rfl
    intro j _
    rw [sum_mul]
    apply sum_congr rfl
    intro i _
    dsimp only [c]
    ring

/-- Output and state contraction of a live chunk of arbitrary size. -/
def tile (n : ℕ) (x : Tokens d) (s : Row d) (sc : ℝ) : (ℕ → ℝ) × Row d :=
  let p := cum x.logDecay
  let f := correction n x s
  (blockOutput s p x.key x.query f sc, blockState s p x.key f n)

theorem tile_eq (n : ℕ) (x : Tokens d) (s : Row d) (sc : ℝ) :
    (∀ t < n, (tile n x s sc).1 t = sc * dot (tokenState x s (t+1)) (x.query t)) ∧
    (tile n x s sc).2 = tokenState x s n := by
  have start (i : Fin d) : cum x.logDecay 0 i = 1 := by simp [cum]
  have advance (t) (i : Fin d) :
      cum x.logDecay (t+1) i = cum x.logDecay t i * Real.exp (x.logDecay t i) := by
    simp [cum, sum_range_succ, Real.exp_add]
  have nz (t) (i : Fin d) : cum x.logDecay (t+1) i ≠ 0 := Real.exp_ne_zero _
  have h := correction_solves n x s
  exact ⟨fun _ ht => block_output_eq _ _ _ _ _ _ _ _ _ start advance nz h ht,
    block_state_eq _ _ _ _ _ _ _ start advance nz h n (le_refl _)⟩

/-- Chunk sizes are their live counts, so a final partial chunk has its actual length. -/
def chunkLoss (x : Tokens d) (sc : ℝ) (w : ℕ → ℝ) (b : Row d) :
    List ℕ → ℕ → Row d → ℝ
  | [], _, s => dot s b
  | n :: rest, off, s =>
    let z := tile n (suffix x off) s sc
    (∑ j ∈ range n, w (off+j) * z.1 j) + chunkLoss x sc w b rest (off+n) z.2

theorem chunkLoss_eq (x : Tokens d) (initial : Row d) (sc : ℝ) (w : ℕ → ℝ) (b : Row d)
    (sizes : List ℕ) (off : ℕ) :
    chunkLoss x sc w b sizes off (tokenState x initial off) =
      (∑ j ∈ range sizes.sum, w (off+j) *
        (sc * dot (tokenState x initial (off+j+1)) (x.query (off+j)))) +
      dot (tokenState x initial (off+sizes.sum)) b := by
  induction sizes generalizing off with
  | nil => simp [chunkLoss]
  | cons n rest ih =>
    have h := tile_eq n (suffix x off) (tokenState x initial off) sc
    have first : (∑ j ∈ range n, w (off+j) * (tile n (suffix x off)
        (tokenState x initial off) sc).1 j) = ∑ j ∈ range n, w (off+j) *
          (sc * dot (tokenState x initial (off+j+1)) (x.query (off+j))) := by
      apply sum_congr rfl
      intro j hj
      rw [h.1 j (mem_range.mp hj), state_shift]
      simp only [suffix, Nat.add_assoc]
    simp only [chunkLoss, h.2, first, state_shift, ih, List.sum_cons, sum_range_add, add_assoc]

/-- The raw gradient applies to FLA's real chunk graph for *any* partition, including
32- and 64-token tiles, short tails and the empty sequence. -/
theorem chunk_backward {v : ℕ} {x : ℝ → Inputs d v} {dx : Inputs d v} {u : ℝ}
    (w : Fin v → ℕ → ℝ) (sizes : List ℕ) (b : Fin v → Row d)
    (hx : ∀ j t, RawPath (fun z => (x z).raw j t) (dx.raw j t) u)
    (hs : ∀ j, RowPath (fun z => (x z).initial j) (dx.initial j) u) :
    HasDerivAt (fun z => ∑ j, chunkLoss ((x z).tokens j) (x z).scale (w j) (b j)
        sizes 0 ((x z).initial j))
      (∑ j, (rawBackward (x u) w sizes.sum b j).apply rawPair (dx.initial j) (dx.raw j)) u := by
  have eqv (z : ℝ) (j : Fin v) : chunkLoss ((x z).tokens j) (x z).scale (w j) (b j)
        sizes 0 ((x z).initial j) = loss ((x z).tokens j) ((x z).initial j)
          (x z).scale (w j) sizes.sum (b j) := by
    rw [loss_eq]
    simpa only [Nat.zero_add, tokenState, sequential] using
      chunkLoss_eq ((x z).tokens j) ((x z).initial j) (x z).scale (w j) (b j) sizes 0
  simp_rw [eqv]
  exact public_backward w sizes.sum b hx hs

end
end FlashKda.Backward.Fla
