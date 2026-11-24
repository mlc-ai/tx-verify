-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.BiasWeights
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.StoreWords
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow
noncomputable section
set_option maxRecDepth 100000

def biasStoreReg (i : Nat) := [5048, 5064, 5080, 5099].getD (i/16) 0 + i%16

private def word (E after : List (Nat × Value)) (fallback : Nat → Value) (i : Nat) :=
  let r := biasStoreReg i
  ((E ++ halvesB E ++ after).lookup r).getD (fallback r)

private theorem words (soft : Bool) (W fallback : Nat → Value) (after : List (Nat × Value))
    {j : Nat} (hj : j < 32) :
    let E := biasOut soft W
    (word E after fallback (2*j), word E after fallback (2*j+1)) =
      packFour (column (biasLanes (lookupD E))) j := by
  apply atColumn (f := fun j => (word (biasOut soft W) after fallback (2*j),
    word (biasOut soft W) after fallback (2*j+1)))
    (g := packFour (column (biasLanes (lookupD (biasOut soft W))))) hj
  cases soft <;> kernel_rfl

theorem bias_store {p L m} (hp : Pre p L m) (g : Nat) (v : V) (q : Fin 4)
    (k : Fin 4) (acc : List Value) (i : Nat) (hi : i < 64) :
    Values.Bf16Pair (valueOfD p L g ⟨.pst .bias q, v, k, acc⟩ (biasStoreReg i))
      (P p L g v .bias (2*i)) (P p L g v .bias (2*i+1)) := by
  let d : D := ⟨.pst .bias q, v, k, acc⟩
  let W := vExpoB p L g v
  let sw := Epilogue.scmp .lt .u v.bt (r301 p L g v)
  let E := tailB p L g v
  let after := valuesRun p v ++ valuesBiasM p v
  have e : pBData p L g v = E ++ halvesB E ++ after := by
    simp only [pBData, E, after, List.append_assoc]
  change Values.Bf16Pair (((pBData p L g v).lookup (biasStoreReg i)).getD
    (valueOf p L g d (biasStoreReg i))) _ _
  rw [e]
  exact store_of_quads (column (biasLanes (lookupD E))) (word E after (valueOf p L g d))
    (P p L g v .bias) (column_eq (fun _ => bias_weights hp g v))
    (fun _ => words sw W _ after) hi

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
