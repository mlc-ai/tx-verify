-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutFloatItems
public import Lemmas.Flow.OutKinds

@[expose] public section

/-! # The value of `mul.f32x2` (no rounding modifier) on two float pairs

A value tool for the generated runs of `Tools/out_gen.py` whose items are `mul.f32x2` with
operands a packed pair (`mov.b64 %rd, {a, b}`) and a pair register (`fF mul2NL`):

* `OkF v x`: the register value `v` is a clean four-byte value that reads as the number `x`;
* `floatE_mul2N_fin`: the ideal outcome of `mul2NI` on two pairs of numbers is the pair of the
  exact products;
* `fF_mul2N_join`: the outcome function of the generated item on the packed pair of `a` and `b`
  and a pair register reading as `(s, s)` is the pair of the products by `s`;
* `mulFacts o x s n`: the facts of `n` registers from `o` holding the products `x j * s`. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- A clean four-byte value reading as the number `x`. -/
def OkF (v : Value) (x : ℝ) : Prop := Clean v ∧ valFloat .f32 v = .ok x

/-- **A packed product of numbers** (`mul.f32x2`, no rounding modifier) is the pair of the exact
products. -/
theorem floatE_mul2N_fin {va vb : Value} {x0 x1 y0 y1 : ℝ}
    (hx0 : valFloat .f32 (splitValue 64 va).1 = .ok x0)
    (hx1 : valFloat .f32 (splitValue 64 va).2 = .ok x1)
    (hy0 : valFloat .f32 (splitValue 64 vb).1 = .ok y0)
    (hy1 : valFloat .f32 (splitValue 64 vb).2 = .ok y1) :
    floatE mul2NI [va, vb] = .ok (.pair (.float .f32 (x0 * y0)) (.float .f32 (x1 * y1))) := by
  simp only [floatE, idealVal, pairRead_of hx0 hx1, pairRead_of hy0 hy1, bindRead, mulEReal_coe,
    erealValue_coe, pure, Except.pure]

/-- **The generated `mul.f32x2` item on a packed pair**: from two clean numbers `x0`, `x1` and a
pair register reading as `(s, s)`, the outcome is the pair of `x0 * s` and `x1 * s`. -/
theorem fF_mul2N_join {p q : Nat} (hpq : p ≠ q) {a b c : Value} {x0 x1 s : ℝ} (ha : OkF a x0)
    (hb : OkF b x1) (hc0 : valFloat .f32 (splitValue 64 c).1 = .ok s)
    (hc1 : valFloat .f32 (splitValue 64 c).2 = .ok s) :
    fF mul2NL [.reg p, .reg q] [joinValue a b, c] =
      .ok (.pair (.float .f32 (x0 * s)) (.float .f32 (x1 * s))) := by
  have hj := split_join_clean ha.1 hb.1
  have hq : lk [p, q] [joinValue a b, c] q = c := by
    have e : (q == p) = false := beq_false_of_ne (Ne.symm hpq)
    simp [lk, List.lookup, e]
  have hp : lk [p, q] [joinValue a b, c] p = joinValue a b := by
    simp [lk]
  simp only [fF, regsOf, regOf, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, fOpnd, hp, hq, mul2NL]
  exact floatE_mul2N_fin (by rw [hj]; exact ha.2) (by rw [hj]; exact hb.2) hc0 hc1

/-- The facts of `n` registers from `o`, register `o + j` holding the number `x j * s`. -/
def mulFacts (o : Nat) (x : Nat → ℝ) (s : ℝ) (n : Nat) : List (Nat × Value) :=
  (List.range n).map fun j => (o + j, .float .f32 (x j * s))

end
end PTX.Flow
