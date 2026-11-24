-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.PlainWeights
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.StoreWords
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow
noncomputable section
set_option maxRecDepth 100000

def plainStoreReg (i : Nat) :=
  let q := i/16
  let j := i%16/2
  let slot := if q = 1 ∨ q = 2 then [7,6,5,1,4,3,2,0].getD j 0 else 7-j
  [5733,5749,5765,5782].getD q 0 + 2*slot + i%2

private def word (E : List (Nat × Value)) (fallback : Nat → Value) (i : Nat) :=
  let r := plainStoreReg i
  let halves := unpackSpecP.flatMap fun (lo, hi, w) =>
    [(lo, (splitValue 64 (lookupD E w)).1), (hi, (splitValue 64 (lookupD E w)).2)]
  ((E ++ halves).lookup r).getD (fallback r)

private theorem words (W fallback : Nat → Value) {j : Nat} (hj : j < 32) :
    let E := plainOut W
    (word E fallback (2*j), word E fallback (2*j+1)) =
      packFour (fun i => lookupD E (plainReg i)) j :=
  atColumn hj (f := fun j => (word (plainOut W) fallback (2*j), word (plainOut W) fallback (2*j+1)))
    (g := packFour (fun i => lookupD (plainOut W) (plainReg i))) (by kernel_rfl)

theorem plain_store {p L m} (hp : Pre p L m) (g : Nat) (v : V) (q : Fin 4)
    (k : Fin 4) (acc : List Value) (i : Nat) (hi : i < 64) :
    Values.Bf16Pair (valueOfD p L g ⟨.pst .plain q, v, k, acc⟩ (plainStoreReg i))
      (P p L g v .plain (2*i)) (P p L g v .plain (2*i+1)) :=
  store_of_quads (fun i => lookupD (expoPE p v) (plainReg i))
    (word (expoPE p v) (valueOf p L g ⟨.pst .plain q,v,k,acc⟩)) (P p L g v .plain)
    (fun _ => plain_weight hp g v) (fun _ => words (vExpoP p v) _) hi

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
