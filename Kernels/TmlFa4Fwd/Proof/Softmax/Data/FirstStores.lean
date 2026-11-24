-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.FirstWeights
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Pack
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- Source register of a word in the four first-round stores, in PTX operand order. -/
def firstStoreReg (i : Nat) : Nat :=
  [3879, 3895, 3911, 3928].getD (i/16) 0 + 2*(7 - i%16/2) + i%2

private def word (W fallback : Nat → Value) (i : Nat) : Value :=
  let e := Gen.expo1_facts14 W
  let r := firstStoreReg i
  ((e ++ halvesP1 e).lookup r).getD (fallback r)

private theorem words (W fallback : Nat → Value) {j : Nat} (hj : j < 32) :
    (word W fallback (2*j), word W fallback (2*j+1)) =
    packFour (fun i => lookupD (Gen.expo1_facts14 W) (1231+i)) j :=
  atColumn hj (f := fun j => (word W fallback (2*j), word W fallback (2*j+1)))
    (g := packFour (fun i => lookupD (Gen.expo1_facts14 W) (1231+i))) (by kernel_rfl)

theorem first_weight {p L m} (hp : Pre p L m) (g : Nat) (v : V) (i : Nat) (hi : i < 128) :
    lookupD (expoE p L g v) (1231+i) = .float .f32 (P p L g v .first i) := by
  have h := first_weights hp g v (j := i/2) (by omega)
  by_cases he : i % 2 = 0
  · have e : 2*(i/2) = i := by omega
    exact e ▸ congrArg Prod.fst h
  · have e : 2*(i/2)+1 = i := by omega
    have heq := congrArg Prod.snd h
    dsimp only [Prod.snd] at heq
    rwa [Nat.add_assoc, e] at heq

/-- The four successive P stores read pairs of adjacent, increasing probability columns. -/
theorem first_store {p L m} (hp : Pre p L m) (g : Nat) (v : V) (q : Fin 4)
    (k : Fin 4) (acc : List Value) (i : Nat) (hi : i < 64) :
    Values.Bf16Pair (valueOfD p L g ⟨.pst .first q, v, k, acc⟩ (firstStoreReg i))
      (P p L g v .first (2*i)) (P p L g v .first (2*i+1)) := by
  let d : D := ⟨.pst .first q, v, k, acc⟩
  let w := P p L g v .first
  let W := vExpo1 p L g v
  let fall := valueOf p L g d
  have hj : i/2 < 32 := by omega
  have h := (words W fall hj).trans
    (packFour_eq (W := fun i => lookupD (expoE p L g v) (1231+i)) (w := w)
      (i/2) (first_weight hp g v) hj)
  change Values.Bf16Pair (word W fall i) (w (2*i)) (w (2*i+1))
  by_cases he : i%2 = 0
  · have e : word W fall i = packed (w (2*i)) (w (2*i+1)) := by
      have t := congrArg Prod.fst h
      dsimp only [Prod.fst] at t
      simpa only [show 2*(i/2) = i by omega, show 4*(i/2) = 2*i by omega] using t
    rw [e]; exact packed_bytes _ _
  · have e : word W fall i = packed (w (2*i)) (w (2*i+1)) := by
      have t := congrArg Prod.snd h
      dsimp only [Prod.snd] at t
      simpa only [show 2*(i/2)+1 = i by omega, show 4*(i/2)+2 = 2*i by omega,
        show 4*(i/2)+3 = 2*i+1 by omega] using t
    rw [e]; exact packed_bytes _ _

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
