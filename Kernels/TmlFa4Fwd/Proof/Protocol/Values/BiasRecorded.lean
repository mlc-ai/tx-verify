-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasOperand
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasChunk

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

private theorem same_credit {X : Execution} {g i pc id} {a : Fin 4 → Acc}
    {bs : Fin 4 → List (Option Byte)}
    (he : ∀ j : Fin 4, X.get (g,i+j.val) = some ⟨pc,.rd (a j) (bs j)⟩) (j : Fin 4) :
    barOrd X g (i+j.val) id = barOrd X g i id := by
  have step (x : Fin 4) :
      barOrd X g (i+x.val+1) id = barOrd X g (i+x.val) id := by
    obtain ⟨hlt,eq⟩ := List.getElem?_eq_some_iff.mp (he x)
    unfold barOrd
    rw [List.take_succ_eq_append_getElem hlt,eq,List.countP_append]
    rfl
  fin_cases j
  · rfl
  · exact step 0
  · exact (step 1).trans (step 0)
  · exact (step 2).trans ((step 1).trans (step 0))

/-- At the completion of a vector bias load, all eight recorded operands match the
tile, after the causal mask of the first round is applied. -/
theorem soft_bias_recorded {p L m X g i v b c tl} {a : Fin 4 → Acc}
    {bs : Fin 4 → List (Option Byte)} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g<8) (hs : softState p L X g i = some ⟨.bld b c,v,0,[]⟩)
    (he : ∀ j : Fin 4, X.get (g,i+j.val) = some ⟨(Site.bld b c).pc,.rd (a j) (bs j)⟩)
    (tile : tileOf p L (g/L.block) = some tl)
    (valid : tl.Valid p (Prologue.warpIndex L g/4) (rowIx L g))
    (prev : ∀ j < i+4, ∀ ad xs sh, X.TLd (g,j) ad xs sh → F32s xs) :
    let u := barOrd X g i (stageId (Prologue.warpIndex L g/4))
    let row := tl.rowOf (Prologue.warpIndex L g/4) (rowIx L g)
    u<tl.n → ∃ d, softState p L X g (i+4) = some d ∧ ∀ (j : Fin 4) (z : Fin 2),
      let col := 8*c.val+(2*j.val+z.val)
      let key := tl.key u col
      (if u=0 ∧ p.keyCount tl.batch row ≤ key then none else Data.loadedBias p L g d.v .bias col)
        = if key<p.keyCount tl.batch row then some (biasAt p tl.batch tl.head row key)
          else none := by
  intro u row hu
  have word (j : Fin 4) := soft_bias_operand hp hX hf hw b c (he j) tile valid
    (fun i' hi' => prev i' (by have := j.isLt; omega)) (by rw [same_credit he]; exact hu)
  choose w decoded ok operand using word
  obtain ⟨d,next,mids,halves⟩ := soft_bias_chunk hp hs he w (fun j => ⟨decoded j,ok j⟩)
  refine ⟨d,next,?_⟩
  intro j z col key
  obtain ⟨acc,atWord⟩ := mids j
  have addr := soft_bias_word_addr hp hX hf hw atWord (he j)
  have val := operand j z
  simp only [same_credit he,addr,Nat.add_assoc] at val
  rw [show col = 8*c.val+(2*j.val+z.val) from rfl,halves]
  exact val

end PTX.Kernels.TmlFa4Fwd.Proof.Values
