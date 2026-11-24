-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.FirstStores
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Fold
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow
noncomputable section
set_option maxRecDepth 100000

def stripe {α : Type} (add : α → α → α) (w : Nat → α) (a : Nat) : Nat → α
  | 0 => w a
  | n+1 => add (stripe add w a n) (w (a+4*(n+1)))

def reduce {α : Type} (add : α → α → α) (w : Nat → α) : α :=
  let lane a := stripe add w a 15
  add (add (lane 0) (lane 1)) (add (lane 2) (lane 3))

def plusV (a b : Value) := okVal (.bits 64 0) (add2E a b)
def plusR (a b : ℝ × ℝ) := (a.1+b.1, a.2+b.2)
def pairV (a : ℝ × ℝ) := Value.pair (.float .f32 a.1) (.float .f32 a.2)
def horizontal (v : Value) := okVal (.bits 32 0)
  (floatE (addI false) [(splitValue 64 v).1, (splitValue 64 v).2])

private theorem generated_sum (W : Nat → Value) :
    Gen.rsum1_v5005 W = horizontal (reduce plusV
      (fun j => joinValue (W (1231+2*j)) (W (1232+2*j)))) := by kernel_rfl

private theorem plus_eq (x y : ℝ × ℝ) : plusV (pairV x) (pairV y) = pairV (plusR x y) := by
  unfold plusV
  rw [@add2E_fin (pairV x) (pairV y) x.1 x.2 y.1 y.2 rfl rfl rfl rfl]
  rfl

theorem horizontal_eq (x : ℝ × ℝ) : horizontal (pairV x) = .float .f32 (x.1+x.2) := by
  unfold horizontal
  rw [@floatE_add_fin false _ _ x.1 x.2 rfl rfl]
  rfl

private theorem stripe_eq (W : Nat → Value) (w : Nat → ℝ × ℝ)
    (h : ∀ j < 64, W j = pairV (w j)) (a n : Nat) (hn : a+4*n < 64) :
    stripe plusV W a n = pairV (stripe plusR w a n) := by
  induction n with
  | zero => exact h a (by omega)
  | succ n ih => rw [stripe, ih (by omega), h _ (by omega), plus_eq, stripe]

private theorem reduce_eq (W : Nat → Value) (w : Nat → ℝ × ℝ)
    (h : ∀ j < 64, W j = pairV (w j)) : reduce plusV W = pairV (reduce plusR w) := by
  unfold reduce
  simp only [stripe_eq W w h _ 15 (by decide : 0+4*15 < 64),
    stripe_eq W w h _ 15 (by decide : 1+4*15 < 64), stripe_eq W w h _ 15 (by decide : 2+4*15 < 64),
    stripe_eq W w h _ 15 (by decide : 3+4*15 < 64), plus_eq]

private theorem reduce_total (w : Nat → ℝ) :
    let r := reduce plusR (fun j => (w (2*j), w (2*j+1)))
    r.1+r.2 = rowSumT 0 w := by
  dsimp only [reduce, stripe, plusR, rowSumT]
  simp only [Nat.reduceMul, Nat.reduceAdd, zero_add]

theorem first_sum {p L m} (hp : Pre p L m) (g : Nat) (v : V) :
    rs1 p L g v = ∑ i ∈ Finset.range 128, P p L g v .first i := by
  let w := P p L g v .first
  let W := lookupD (expoE p L g v)
  have h (j : Nat) (hj : j < 64) : joinValue (W (1231+2*j)) (W (1232+2*j)) =
      pairV (w (2*j), w (2*j+1)) := by
    have e := first_weights hp g v hj
    have e0 := congrArg Prod.fst e
    have e1 := congrArg Prod.snd e
    dsimp only [Prod.fst, Prod.snd] at e0 e1
    change joinValue (lookupD _ _) (lookupD _ _) = _
    rw [show 1232+2*j = 1231+2*j+1 by omega, e0, e1]
    rfl
  change valR (Gen.rsum1_v5005 W) = _
  rw [generated_sum, reduce_eq _ _ h, horizontal_eq]
  change (reduce plusR _).1 + (reduce plusR _).2 = _
  rw [reduce_total w, rowSumT_eq, zero_add]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
