-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Spec

@[expose] public section
namespace FlashKda.Packed.Workspace
open PTX Sequence Chunk Block Algorithm Batches Matrix Finset
noncomputable section

structure Tile where
  decayedKey : Full → Row 128
  decayedQuery : Full → Row 128
  restoredKey : Full → Row 128
  totalDecay : Row 128
  inverse : Matrix Full Full ℝ
  score : Matrix Full Full ℝ

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
  let cum := Algorithm.cum fun t => if t < len then x.logDecay t else fun _ => 0
  factors cum key query x.strength scale

def Tile.apply (w : Tile) (s : Row 128) (v beta : Full → ℝ) : (Full → ℝ) × Row 128 :=
  let u := w.inverse *ᵥ (fun t => (v t - dot s (w.decayedKey t)) * beta t)
  (fun t => dot s (w.decayedQuery t) + (w.score *ᵥ u) t,
   fun k => s k * w.totalDecay k + ∑ j, w.restoredKey j k * u j)

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
  let cum := Algorithm.cum fun t => if t < len then x.logDecay t else fun _ => 0
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
  let cum := Algorithm.cum fun t => if t < len then x.logDecay t else fun _ => 0
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

structure Bases where
  workspace : Nat
  values : Nat
  logits : Nat
  initialState : Nat
  sequenceOffsets : Nat

def total (p : Problem) := firstToken p.length p.sequences

def reserved (p : Problem) := tiles (total p) + p.sequences

def index (p : Problem) (seq head tile : Nat) := head * reserved p + firstTile p.length seq + tile

def field (p : Problem) (b : Bases) (fieldOffset width idx element : Nat) : Loc :=
  ⟨.global, 0, b.workspace + (p.heads * reserved p) * fieldOffset + idx * width + element⟩

def Recorded (p : Problem) (b : Bases) (m : Mem0) (seq head tile : Nat) (w : Tile) : Prop :=
  let atField := fun pre width off => field p b pre width (index p seq head tile) off
  (∀ t k, memFloat .bf16 m (atField 0 4096 (256*t.val+2*k.val)) = .ok (w.decayedKey t k)) ∧
  (∀ t k, memFloat .bf16 m (atField 4096 4096 (256*t.val+2*k.val)) = .ok (w.decayedQuery t k)) ∧
  (∀ t k, memFloat .bf16 m (atField 8192 4096 (256*t.val+2*k.val)) = .ok (w.restoredKey t k)) ∧
  (∀ k, memFloat .f32 m (atField 12288 512 (4*k.val)) = .ok (w.totalDecay k)) ∧
  (∀ t j, memFloat .bf16 m (atField 12800 512 (32*t.val+2*j.val)) = .ok (w.inverse t j)) ∧
  (∀ t j, memFloat .bf16 m (atField 13312 512 (32*t.val+2*j.val)) = .ok (w.score t j))

def PreparedMemory (p : Problem) (b : Bases) (m : Mem0) : Prop :=
  ∀ seq < p.sequences, ∀ head < p.heads, ∀ tile < tiles (p.length seq),
    let x := suffix (p.tokens seq head 0) (16*tile)
    Recorded p b m seq head tile (coefficients x (liveRows (p.length seq) tile) p.scale)

def Inputs (p : Problem) (b : Bases) (m : Mem0) : Prop :=
  PreparedMemory p b m ∧
  (∀ seq ≤ p.sequences, ∀ byte < 8, m ⟨.global, 0, b.sequenceOffsets + 8*seq + byte⟩ =
    some (some ((Value.bits 64 (BitVec.ofNat 64 (firstToken p.length seq))).byteAt byte))) ∧
  (∀ seq < p.sequences, ∀ h < p.heads, ∀ t < p.length seq, ∀ v : Fin 128,
    memFloat .bf16 m ⟨.global, 0, b.values +
      256*((firstToken p.length seq+t)*p.heads+h) + 2*v.val⟩ = .ok (p.value seq h t v)) ∧
  (∀ seq < p.sequences, ∀ h < p.heads, ∀ t < p.length seq,
    memFloat .bf16 m ⟨.global, 0, b.logits + 2*(h*total p+firstToken p.length seq+t)⟩ =
      .ok (p.betaLogit seq h t)) ∧
  ∀ seq < p.sequences, ∀ h < p.heads, ∀ v k : Fin 128,
    memFloat .f32 m ⟨.global, 0, b.initialState + 65536*(seq*p.heads+h) + 512*v.val + 4*k.val⟩ =
      .ok (p.initial seq h v k)

end
end FlashKda.Packed.Workspace
