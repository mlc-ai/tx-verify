-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Exponent
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Kinds
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPw1
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

theorem atColumn {α : Type} {f g : Nat → α} {n i : Nat} (hi : i < n)
    (h : (List.range n).map f = (List.range n).map g) : f i = g i :=
  List.map_inj_left.mp h i (List.mem_range.mpr hi)

private def firstPair (W : Nat → Value) (j : Nat) : Value × Value :=
  let a := W (elemRegs.getD (2*j) 0)
  let b := W (elemRegs.getD (2*j+1) 0)
  let z := offset (W 3685) (W 1230)
  let xy := okVal (.bits 64 0) (fma2E (joinValue a b) (joinValue (W 7132) (W 7132))
    (joinValue z z))
  (okVal (.bits 32 0) (ex2E true (splitValue 64 xy).1),
   okVal (.bits 32 0) (ex2E true (splitValue 64 xy).2))

private theorem first_regs (W : Nat → Value) {j : Nat} (hj : j < 64) :
    (lookupD (Gen.expo1_facts14 W) (1231+2*j), lookupD (Gen.expo1_facts14 W) (1231+2*j+1)) =
      firstPair W j :=
  atColumn (f := fun j => (lookupD (Gen.expo1_facts14 W) (1231+2*j),
    lookupD (Gen.expo1_facts14 W) (1231+2*j+1))) (g := firstPair W) hj (by kernel_rfl)

private theorem first_input (p L g v) {i : Nat} (hi : i < 128) :
    vExpo1 p L g v (elemRegs.getD i 0) = elemVal (mcnt p L g v) (bpf v) (bps p v) i := by
  let sample (m n : Value) (v : Nat → Value) (after : List (Nat × Value)) (i : Nat) :=
    (((3685,m) :: (7256,n) :: (List.range 128).map (fun j => (elemRegs.getD j 0,v j)) ++
      after).lookup (elemRegs.getD i 0)).getD (.pred false)
  have lookup_input (m n : Value) (v : Nat → Value) (after : List (Nat × Value)) :
      sample m n v after i = v i := atColumn hi (f := sample m n v after) (g := v) (by kernel_rfl)
  exact lookup_input _ _ _ _

def P (p L g v r i) := probability p (maximum p L g v r) (score p L g v r i)

private theorem first_pair_eval (p : Params) (M x y : EReal) (W : Nat → Value) (j : Nat)
    (hm : Reads (W 3685) M.toReal) (hn : Reads (W 1230) (-(scl p : ℝ)))
    (hs : Reads (W 7132) (scl p : ℝ)) (hp : 0 < (scl p : ℝ))
    (ha : Reads (W (elemRegs.getD (2*j) 0)) x)
    (hb : Reads (W (elemRegs.getD (2*j+1) 0)) y) (hx : x < ⊤) (hy : y < ⊤) :
    firstPair W j = (.float .f32 (probability p M x), .float .f32 (probability p M y)) := by
  dsimp only [firstPair]
  rw [offset_val hm hn, shifted_pair (reads_join ha hb) hs (reads_float (M.toReal * -(scl p : ℝ)))
    hp hx hy]
  exact congrArg₂ Prod.mk (hw_exp p M x) (hw_exp p M y)

private theorem neg_register (p L g v) : Reads (vExpo1 p L g v 1230) (-(scl p : ℝ)) := by
  rw [vExpo1_1230, show negS p = .float .f32 (-(scl p : ℝ)) from
    congrArg (Value.float .f32) (Rat.cast_neg _)]
  exact reads_float _

private theorem scale_register {p L m} (hp : Pre p L m) (g v) :
    Reads (vExpo1 p L g v 7132) (scl p : ℝ) := by
  rw [show vExpo1 p L g v 7132 = .bits 32 (Epilogue.paramW p.scaleLog2Bits) from by kernel_rfl]
  exact (reads_scale hp).1

private theorem head_max (x : EReal) (xs ys : List (Nat × Value)) (h : x < ⊤) :
    Reads (((((3685, selMax x) :: xs) ++ ys).lookup 3685).getD (.pred false)) x.toReal :=
  reads_sel h

private theorem max_register (p L g v) :
    Reads (vExpo1 p L g v 3685) (foldF p L g v).toReal :=
  head_max (foldF p L g v) _ _ (foldF_lt_top p L g v)

private theorem elem_register (p L g v) {i : Nat} (hi : i < 128) :
    Reads (vExpo1 p L g v (elemRegs.getD i 0)) (score p L g v .first i) := by
  rw [first_input p L g v hi]
  exact reads_first p L g v i

private theorem score_first_lt_top (p L g v i) : score p L g v .first i < ⊤ :=
  mre_lt_top (bpe_lt_top (bpf v) (bps p v) i)

theorem first_weights {p L m} (hp : Pre p L m) (g : Nat) (v : V) {j : Nat} (hj : j < 64) :
    (lookupD (expoE p L g v) (1231+2*j), lookupD (expoE p L g v) (1231+2*j+1)) =
      (.float .f32 (P p L g v .first (2*j)), .float .f32 (P p L g v .first (2*j+1))) := by
  unfold expoE P
  simp only [maximum]
  exact (first_regs (vExpo1 p L g v) hj).trans
    (first_pair_eval p (foldF p L g v) (score p L g v .first (2*j))
      (score p L g v .first (2*j+1)) (vExpo1 p L g v) j (max_register p L g v)
      (neg_register p L g v) (scale_register hp g v) (reads_scale hp).2
      (elem_register p L g v (by omega)) (elem_register p L g v (by omega))
      (score_first_lt_top p L g v _) (score_first_lt_top p L g v _))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
