-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
import Kernels.TmlFa4Fwd.Proof.Softmax.Align
import Lemmas.Flow.TcAddr
import Lemmas.Flow.Arith32WordW
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow.Arith32

private theorem row_bits (x y : BitVec 64) (b : Bool) :
    or32 (andi y 127) (shl (or32 (shl x 1) (sel b (i32 1) (i32 0))) 7) =
    add32 (add32 (shl x 8) (sel b (i32 128) (i32 0))) (andi y 127) := by
  have e1 : (i32 1).toNat = 1 := by decide
  have e7 : (i32 7).toNat = 7 := by decide
  have e8 : (i32 8).toNat = 8 := by decide
  have w1 : i32 1 = 1#64 := by decide
  have w0 : i32 0 = 0#64 := by decide
  have w128 : i32 128 = 128#64 := by decide
  have w127 : i32 127 = 127#64 := by decide
  unfold or32 andi shl add32 sel r32
  rw [e1, e7, e8, w0, w1, w128, w127]
  simp only [show ¬ (1 ≥ 32) by decide, show ¬ (7 ≥ 32) by decide, show ¬ (8 ≥ 32) by decide,
    ite_false, PTX.Flow.tb32]
  have add_or := fun (a b : BitVec 64) (h : a &&& b = 0#64) => BitVec.add_eq_or_of_and_eq_zero a b h
  have bits : ∀ a b : BitVec 64, (∀ i : Fin 64, a.getLsbD i = b.getLsbD i) → a = b :=
    fun a b h => BitVec.eq_of_getLsbD_eq fun i hi => h ⟨i, hi⟩
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    rw [add_or ((x &&& 4294967295#64) <<< 8 &&& 4294967295#64 &&& 4294967295#64) _
        (bits _ _ fun i => by fin_cases i <;> simp),
      add_or _ (_ &&& _) (bits _ _ fun i => by fin_cases i <;> simp)]
    exact bits _ _ fun i => by fin_cases i <;> simp

/-- The lane's low seven bits and its warp-group bit form the row within the 256-row tile. -/
theorem mask_row {p L m g v t} (hp : Pre p L m) (hw : g%L.block/32 < 8)
    (hr : shl (rowOff p L g v.sc) 8 = W (256*t)) (ht : 256*t+256<2^32) :
    or32 (andi (tidW L g) 127) (r1808 p L g v) =
      W (256*t+128*(g%L.block/32/4)+g%L.block%128) := by
  have stage : ∀ w : Fin 8, sel (Epilogue.scmpi .gt .s (BitVec.ofNat 64 w.val) 3)
      (i32 128) (i32 0) = W (128*(w.val/4)) := by decide
  rw [r1808,row_bits,hr,stage ⟨_,hw⟩,tidW_eq hp]
  have hl : g%L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  have low := andi_W_low (a := g%L.block) (k := 7) (by omega) (by decide)
  change andi (W (g%L.block)) 127 = W (g%L.block%128) at low
  rw [low,add32_W (by omega),add32_W (by omega)]

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
