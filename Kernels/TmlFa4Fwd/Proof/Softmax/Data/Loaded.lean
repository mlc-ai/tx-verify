-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Online
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Links

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
noncomputable section

def diagonal (m : BitVec 64) (k i : Nat) :=
  if i = 0 then mkeep0 k m else if i < 31 then !(mdrop k m i) else !(mdrop31 k m)

private theorem masked_score (m : BitVec 64) (k i : Nat) (x : EReal) :
    mre k m i x = if diagonal m k i then x else ⊥ := by
  unfold mre diagonal
  split
  · rfl
  · split
    · cases mdrop k m i <;> rfl
    · cases mdrop31 k m <;> rfl

/-- The bias half read for that score, after masking; ordinary rounds add zero. -/
def loadedBias (p : Params) (L : Launch) (g : Nat) (v : V) (r : Rd) (i : Nat) : Option ℝ :=
  let b := if bpf v i then some (v.br ⟨i/8%16, Nat.mod_lt _ (by decide)⟩ (i%8)) else none
  match r with
  | .first => if diagonal (mcnt p L g v) (i/32) (i%32) then b else none
  | .bias => b
  | .plain => some 0

def adjusted (p : Params) (s : ℝ) : Option ℝ → EReal
  | none => ⊥
  | some b => ((s + abiFloat p.invScaleBits * b : ℝ) : EReal)

theorem loaded_score (p L g v r i) :
    score p L g v r i = adjusted p (v.score i) (loadedBias p L g v r i) := by
  have bias (i : Nat) : bpeB p v i =
      adjusted p (v.score i) (loadedBias p L g v .bias i) := by
    simp only [bpeB, bpe, loadedBias]
    split
    · simp only [adjusted, bps, s14, abiFloat, mul_comm, add_comm]
    · rfl
  cases r
  · rw [score, masked_score, bias]
    unfold loadedBias
    split <;> rfl
  · exact bias i
  · simp only [score, loadedBias, adjusted, mul_zero, add_zero]

/-- The named row data for a prefix ending at round `n-1`. -/
def rowData (p : Params) (L : Launch) (g : Nat) (n : Nat) (v : Nat → V) (r : Nat → Rd) :
    Values.RowData where
  P u := P p L g (v u) (r u)
  c u := scale p (maximum p L g (v u) (r u))
  f u := factor p (v u) (r u)
  rs := sumAfter p L g (v (n-1)) (r (n-1))
  rm := (maximum p L g (v (n-1)) (r (n-1))).toReal

theorem last_scale (p L g n v r) :
    let D := rowData p L g n v r
    D.c (n-1) = (2 : ℝ) ^ (-(abiFloat p.scaleLog2Bits * D.rm)) := by
  simp only [rowData, scale, neg_mul, scl, abiFloat]

private theorem replace_weight {n : Nat} {a b P : Nat → Nat → ℝ} {c f : Nat → ℝ} {s : ℝ}
    (h : PTX.Numeric.OnlineFold.Fold n a P c f s) (eq : ∀ u < n, ∀ i < 128, a u i = b u i) :
    PTX.Numeric.OnlineFold.Fold n b P c f s := by
  refine ⟨h.pos, fun u hu i hi => (h.prob u hu i hi).trans (by rw [eq u hu i hi]),
    fun u hu => (h.factor u hu).imp_right (fun z t ht k hk => (eq t (by omega) k hk).symm.trans
      (z t ht k hk)), h.le, ?_⟩
  rw [h.sum]
  congr 1
  exact Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun i hi =>
    eq u (Finset.mem_range.mp hu) i (Finset.mem_range.mp hi)

/-- The tile-facing equation only requires agreement on the loaded operands of valid columns.
A masked column has no bias payload. -/
theorem tile_weight (p L g v r) (t : Values.Tile) (row u i : Nat) (s : ℝ)
    (hb : loadedBias p L g v r i =
      if t.key u i < p.keyCount t.batch row then
        some (Values.biasAt p t.batch t.head row (t.key u i))
      else none) (hs : v.score i = s) :
    weight p (score p L g v r i) = Values.weightOf p t row (fun _ _ => s) u i := by
  rw [loaded_score, hb, hs]
  unfold Values.weightOf
  split
  · simp only [adjusted, weight, EReal.coe_ne_bot, ite_false, EReal.toReal_coe, scl, abiFloat]
  · simp only [adjusted, weight, ite_true]

/-- The numeric conclusion of SoftLink for a tile whose bias loads and first-round mask agree
with its inputs. Only the tile's visited rounds and columns enter the comparison. -/
theorem tile_fold {p L m} (hp : Pre p L m) (g : Nat) (t : Values.Tile) (row : Nat) (hn : 0 < t.n)
    (bias : Nat → Bool) (input : Nat → V)
    (hb : ∀ u < t.n, ∀ i < 128,
      loadedBias p L g (roundState p L g bias input u) (roundAt bias u) i =
      if t.key u i < p.keyCount t.batch row then
        some (Values.biasAt p t.batch t.head row (t.key u i))
      else none) :
    let v := roundState p L g bias input
    let D := rowData p L g t.n v (roundAt bias)
    PTX.Numeric.OnlineFold.Fold t.n (Values.weightOf p t row (fun u => (v u).score))
      D.P D.c D.f D.rs ∧
      D.c (t.n-1) = (2 : ℝ) ^ (-(abiFloat p.scaleLog2Bits * D.rm)) := by
  refine ⟨replace_weight (online hp g t.n hn bias input) ?_, last_scale _ _ _ _ _ _⟩
  intro u hu i hi
  exact tile_weight p L g _ _ t row u i _ (hb u hu i hi) rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
