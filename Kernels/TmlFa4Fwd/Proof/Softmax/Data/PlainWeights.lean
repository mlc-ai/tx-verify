-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.BiasWeights
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Assumption
noncomputable section
set_option maxRecDepth 100000

def plainHooks (facts : List (Nat × Value)) (x y : Nat) (extra : List (Nat × Value)) :=
  let a := swOut (lookupD facts) x (x+1) y (y+3) ++ extra ++ facts
  swOut (lookupD a) (x+2) (x+3) (y+6) (y+9) ++ a

/-- The plain exponent run with its start register file abstracted. -/
def plainOut (W : Nat → Value) :=
  let s1 := plainHooks (Gen.expoP0_facts7 W) 5564 5128 cuteConsts
  let s3 := plainHooks (Gen.expoP1_facts1 (lookupD s1)) 5580 5140 []
  let s5 := plainHooks (Gen.expoP2_facts2 (lookupD s3)) 5596 5152 []
  let s7 := plainHooks (Gen.expoP3_facts1 (lookupD s5)) 5612 5164 []
  Gen.expoP4_facts3 (lookupD s7)

def plainSoft (i : Nat) := decide (44 ≤ i ∧ i < 96 ∧ 12 ≤ i%16)

def plainReg (i : Nat) :=
  if plainSoft i then 5128 + 3*(4*(i/16-2) + i%16-12)
  else 1493+i-4*min 4 (i/16-2)

private def source (j : Nat) := if j < 4 then 8690-j else 7427+j

private def fmaPair (W : Nat → Value) (j : Nat) :=
  let z := offset (W 5514) (W 1230)
  splitValue 64 (okVal (.bits 64 0) (fma2E (W (source j)) (W 8692) (joinValue z z)))

private def lane (W : Nat → Value) (i : Nat) :=
  let xy := fmaPair W (i/2)
  expLane (plainSoft i) (if i%2 = 0 then xy.1 else xy.2)

private theorem routing (W : Nat → Value) {i : Nat} (hi : i < 128) :
    lookupD (plainOut W) (plainReg i) = lane W i :=
  atColumn hi (f := fun i => lookupD (plainOut W) (plainReg i)) (g := lane W) (by kernel_rfl)

private theorem source_eq (p : Params) (v : V) {j : Nat} (hj : j < 64) :
    vExpoP p v (source j) =
      .pair (.float .f32 (v.score (2*j))) (.float .f32 (v.score (2*j+1))) := by
  unfold vExpoP source
  split <;> split_ifs <;> first | omega | congr 3 <;> omega

private theorem submax (p : Params) (v : V) : maxP p v = .float .f32 (maxR p v) := by
  unfold maxP maxR
  cases v.mf
  · rfl
  · simp only []; split <;> rfl

private theorem fmaPair_eq {p L m} (hp : Pre p L m) (v : V) {j : Nat} (hj : j < 64) :
    fmaPair (vExpoP p v) j =
      (shifted p (maxR p v) (v.score (2*j)), shifted p (maxR p v) (v.score (2*j+1))) := by
  let s := Value.bits 32 (Epilogue.paramW p.scaleLog2Bits)
  have sc : vExpoP p v 8692 = joinValue s s := rfl
  have hm : Reads (vExpoP p v 5514) ((maxR p v : EReal).toReal) := by
    change Reads (maxP p v) _
    rw [submax, EReal.toReal_coe]
    exact reads_float _
  have hn : Reads (vExpoP p v 1230) (-(scl p : ℝ)) := by
    change Reads (negS p) _
    rw [show negS p = .float .f32 (-(scl p : ℝ)) from
      congrArg (Value.float .f32) (Rat.cast_neg _)]
    exact reads_float _
  have hab := pairRead_of_reads (v := Value.pair (.float .f32 (v.score (2*j)))
    (.float .f32 (v.score (2*j+1)))) (readEReal_float (v.score (2*j)))
      (readEReal_float (v.score (2*j+1)))
  dsimp only [fmaPair]
  rw [offset_val hm hn, source_eq p v hj, sc, shifted_pair hab (reads_scale hp).1
    (reads_float ((maxR p v : EReal).toReal * -(scl p : ℝ))) (reads_scale hp).2
    (EReal.coe_lt_top _) (EReal.coe_lt_top _)]
  rfl

theorem plain_weight {p L m} (hp : Pre p L m) (g : Nat) (v : V) {i : Nat} (hi : i < 128) :
    lookupD (expoPE p v) (plainReg i) = .float .f32 (P p L g v .plain i) := by
  change lookupD (plainOut (vExpoP p v)) (plainReg i) = _
  rw [routing _ hi, lane, fmaPair_eq hp v (by omega)]
  split
  · rw [show 2*(i/2) = i by omega]
    exact expLane_shift p (maxR p v) (v.score i) (plainSoft i)
  · rw [show 2*(i/2)+1 = i by omega]
    exact expLane_shift p (maxR p v) (v.score i) (plainSoft i)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
