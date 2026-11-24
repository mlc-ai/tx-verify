-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.EnclosureGates
public import Core.Float.Format
import Mathlib.Tactic

/-! A numerical checker for raw public query, key, gate, strength, value and state inputs.
Both activation and propagation are independent of the GPU's internal workspace. -/
@[expose] public section
namespace FlashKda.Enclosure
open Finset

abbrev Rationals (d : Nat) := Vector ℚ d
abbrev Balls (d : Nat) := Vector Ball d
def realRow {d} (v : Rationals d) : Chunk.Row d := fun i => (v[i]:ℝ)

structure Raw (d : Nat) where
  query : Rationals d
  key : Rationals d
  gate : Rationals d
  logit : ℚ
  deriving Inhabited

structure Prepared (d : Nat) where
  query : Balls d
  key : Balls d
  decay : Balls d
  strength : Ball
  deriving Inhabited

def normalize {d} (bits : Nat) (v : Rationals d) : Option (Balls d) := do
  let a ← invRoot bits ((∑ i : Fin d, v[i]*v[i])+1/1000000)
  return Vector.ofFn fun i => grid bits (mul (point v[i]) a)

theorem normalize_ok {d bits} {v : Rationals d} {b : Balls d} (h : normalize bits v = some b)
    (i : Fin d) : Covers b[i] (Algorithm.normalize (realRow v) i) := by
  obtain ⟨a,root,result⟩ := Option.bind_eq_some_iff.mp h
  have eq : Vector.ofFn (fun i : Fin d => grid bits (mul (point v[i]) a)) = b :=
    Option.some.inj result
  subst b
  have r := grid_ok bits (mul_ok (point_ok v[i]) (inv_root_ok root))
  simpa [Algorithm.normalize,Chunk.dot,realRow,div_eq_mul_inv] using r

def gate (bits splits : Nat) (p : Ball) (floor bias input : ℚ) : Option Ball := do
  let strength ← logistic bits splits (mul p (point (input+bias)))
  expBall bits splits (mul (point floor) strength)

theorem gate_ok {bits splits} {p b : Ball} {parameter : ℝ} {floor bias input : ℚ}
    (hp : Covers p (Real.exp parameter)) (h : gate bits splits p floor bias input = some b) :
    Covers b (Real.exp ((floor:ℝ)*Algorithm.sigmoid (Real.exp parameter*((input:ℝ)+bias)))) := by
  unfold gate at h
  cases s : logistic bits splits (mul p (point (input+bias))) with
  | none => simp [s] at h
  | some a =>
    simp [s] at h
    have hs := logistic_ok (mul_ok hp (point_ok (input+bias))) s
    simpa using exp_ok (mul_ok (point_ok floor) hs) h

/-- Evaluate each coordinate once and propagate unsuccessful enclosures. -/
def gather {d : Nat} (f : Fin d → Option Ball) : Option (Balls d) :=
  let tab := Vector.ofFn f
  if ∀ i : Fin d, tab[i].isSome then some (tab.map (·.getD default)) else none

theorem gather_ok {d : Nat} {f : Fin d → Option Ball} {v : Balls d} (hv : gather f = some v)
    (i : Fin d) : f i = some v[i] := by
  dsimp only [gather] at hv
  split at hv
  · rename_i all
    cases hv
    have h := all i
    simp at h ⊢
    cases hf : f i <;> simp_all
  · contradiction

def prepare {d} (bits splits : Nat) (floor : ℚ) (p : Ball) (bias : Rationals d) (r : Raw d) :
    Option (Prepared d) := do
  let q ← normalize bits r.query
  let k ← normalize bits r.key
  let g ← gather fun i => gate bits splits p floor bias[i] r.gate[i]
  let s ← logistic bits splits (point r.logit)
  return ⟨q,k,g,s⟩

def Correct {d} (p : Prepared d) (r : Raw d) (floor parameter : ℚ) (bias : Rationals d) :=
  (∀ i, Covers p.query[i] (Algorithm.normalize (realRow r.query) i)) ∧
  (∀ i, Covers p.key[i] (Algorithm.normalize (realRow r.key) i)) ∧
  (∀ i, Covers p.decay[i]
    (Real.exp (Algorithm.logGate floor parameter (realRow bias) (realRow r.gate) i))) ∧
  Covers p.strength (Algorithm.sigmoid r.logit)

theorem prepare_ok {d bits splits} {floor parameter : ℚ} {p : Ball} {bias : Rationals d}
    {r : Raw d} {v : Prepared d} (hp : expAt bits splits parameter = some p)
    (hv : prepare bits splits floor p bias r = some v) : Correct v r floor parameter bias := by
  obtain ⟨q,hq,k,hk,g,hg,s,hs,out⟩ : ∃ q, normalize bits r.query = some q ∧
      ∃ k, normalize bits r.key = some k ∧ ∃ g,
      gather (fun i => gate bits splits p floor bias[i] r.gate[i]) = some g ∧
      ∃ s, logistic bits splits (point r.logit) = some s ∧ (⟨q,k,g,s⟩:Prepared d) = v := by
    simpa [prepare,Option.bind_eq_some_iff] using hv
  subst v
  exact ⟨normalize_ok hq,normalize_ok hk,
    fun i => gate_ok (exp_at_ok hp) (gather_ok hg i),logistic_ok (point_ok _) hs⟩

def stateStep {d} (bits : Nat) (p : Prepared d) (v : ℚ) (s : Balls d) : Balls d :=
  let before : Balls d := Vector.ofFn fun i => mul s[i] p.decay[i]
  let prediction := inner (d := d) (fun i => before[i]) (fun i => p.key[i])
  let correction := mul p.strength (sub (point v) prediction)
  Vector.ofFn fun i => grid bits (add before[i] (mul correction p.key[i]))

def read {d} (scale : ℚ) (p : Prepared d) (s : Balls d) : Ball :=
  mul (point scale) (inner (d := d) (fun i => s[i]) (fun i => p.query[i]))

theorem step_ok {d bits} {p : Prepared d} {r : Raw d} {floor param v : ℚ} {bias : Rationals d}
    (ok : Correct p r floor param bias) {s : Balls d} {x : Chunk.Row d}
    (prev : ∀ i, Covers s[i] (x i)) (i : Fin d) :
    Covers (stateStep bits p v s)[i] (Chunk.step x
      (fun j => Real.exp (Algorithm.logGate floor param (realRow bias) (realRow r.gate) j))
      (Algorithm.normalize (realRow r.key)) v (Algorithm.sigmoid r.logit) i) := by
  obtain ⟨_,hk,hg,hs⟩ := ok
  have before j := mul_ok (prev j) (hg j)
  have coeff := mul_ok hs (sub_ok (point_ok v) (inner_ok before hk))
  simpa [stateStep,Chunk.step] using grid_ok bits (add_ok (before i) (mul_ok coeff (hk i)))

theorem read_ok {d} {p : Prepared d} {r : Raw d} {floor param scale : ℚ} {bias : Rationals d}
    (ok : Correct p r floor param bias) {s : Balls d} {x : Chunk.Row d}
    (prev : ∀ i, Covers s[i] (x i)) :
    Covers (read scale p s) ((scale:ℝ)*Chunk.dot x (Algorithm.normalize (realRow r.query))) :=
  mul_ok (point_ok scale) (inner_ok prev ok.1)

end FlashKda.Enclosure
