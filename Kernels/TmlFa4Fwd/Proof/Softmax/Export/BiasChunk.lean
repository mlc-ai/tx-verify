-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.RoundStep
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasDecoded
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasWindow
import Kernels.TmlFa4Fwd.Proof.Common.DataSound

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

/-- The word at the address of a bias read is the current substep of the data state. -/
theorem soft_bias_word_addr {p L m X g i v b c k acc a bs} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
    (hw : Prologue.warpIndex L g<8) (hs : softState p L X g i = some ⟨.bld b c,v,k,acc⟩)
    (he : X.get (g,i) = some ⟨(Site.bld b c).pc,.rd a bs⟩) : a.loc.addr/4%4=k.val := by
  obtain ⟨j,_,_,_,hc,addr,_⟩ := soft_bias_window_state hp hX hf hw b c he
  unfold softState at hs
  split at hs
  · rename_i d n hd
    cases Option.some.inj hs
    have eq := (control_of_data hp hd).symm.trans hc
    cases eq
    exact addr.symm
  · cases hs

/-- Four read events of a vector bias load fill its eight columns in low-half-first order. -/
theorem soft_bias_chunk {p L m X g i v b c} {a : Fin 4 → Acc} {bs : Fin 4 → List (Option Byte)}
    (hp : Pre p L m) (hs : softState p L X g i = some ⟨.bld b c,v,0,[]⟩)
    (he : ∀ j : Fin 4, X.get (g,i+j.val) = some ⟨(Site.bld b c).pc,.rd (a j) (bs j)⟩)
    (w : Fin 4 → Value) (decoded : ∀ j, rebuild 3 (bs j) = .ok (w j) ∧ biasOk (w j)=true) :
    ∃ d, softState p L X g (i+4) = some d ∧
      (∀ j : Fin 4, ∃ acc, softState p L X g (i+j.val) = some ⟨.bld b c,v,j,acc⟩) ∧
      ∀ (j : Fin 4) (h : Fin 2),
      Data.loadedBias p L g d.v .bias (8*c.val+(2*j.val+h.val)) =
        if h=0 then (maskedPair .bf16 (w j)).1 else (maskedPair .bf16 (w j)).2 := by
  let vals := [w 0,w 1,w 2,w 3]
  have step (j : Fin 4) (acc : List Value)
      (state : softState p L X g (i+j.val) = some ⟨.bld b c,v,j,acc⟩) :
      softState p L X g (i+j.val+1) = some (if j.val<3 then
        ⟨.bld b c,v,j+1,acc++[w j]⟩ else D.mk' (if c.val=15 then .fence b else .bld b (c+1))
          (recordBias v c (acc++[w j]))) := by
    apply softState_step hp (he j) state
    simp only [succ,(decoded j).1,(decoded j).2,ite_true]
    split <;> rfl
  have s1 := step 0 [] hs
  have s2 := step 1 [w 0] s1
  have s3 := step 2 [w 0,w 1] s2
  have s4 := step 3 [w 0,w 1,w 2] s3
  refine ⟨_,s4,?_,?_⟩
  · intro j
    fin_cases j
    · exact ⟨_,hs⟩
    · exact ⟨_,s1⟩
    · exact ⟨_,s2⟩
    · exact ⟨_,s3⟩
  intro j h
  change Data.loadedBias p L g (recordBias v c vals) .bias _ = _
  rw [Data.bias_load p L g v c vals (by have := j.isLt; have := h.isLt; omega)]
  fin_cases j <;> fin_cases h <;> rfl

end PTX.Kernels.TmlFa4Fwd.Proof.Values
