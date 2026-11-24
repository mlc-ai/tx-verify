-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StoreVals
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.SmWarp.DataFiring
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow Softmax

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Every observed pack agrees with the row, including in an unfinished round. -/
theorem pStored_of_loads (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hb : SmWarp.BiasReadHandoff p L X) (hw : Prologue.warpIndex L g < 8)
    (hld : ∀ i a xs, X.TLd (g,i) a xs .s32x32b → F32s xs) :
    PStored L X g (softRow p L X g).P := by
  intro i a j u vals hst hj hcredit
  obtain ⟨pc,he⟩ := hst
  obtain ⟨r,q,v,k,acc,n,hs⟩ := store_state hp hX hf hw hb he (by
    intro l _ ad xs sh hl
    obtain rfl := (soft_ld hp hX hf hw hl).1
    exact hld _ _ _ hl)
  obtain ⟨t,o,hat,hfi⟩ := SmWarp.data_firing hp hX he hs
  obtain ⟨_,hlen,q',hcol,_,_,hcnt⟩ := soft_st hp hX hf hw (show X.TSt _ _ _ _ from ⟨pc,he⟩)
  let col := (tcDataCell32 L g a j).column - (128*(Prologue.warpIndex L g/4)+64)
  have hc : col = 16*q'.val+j := by
    change a % 65536 + j - _ = _
    omega
  have hn : nthEv X Tm.isTcSt g (4*u+q'.val) = i := by
    have cnt : Tm.stN X g i = 4*u+q'.val := by omega
    rw [← cnt]
    exact nthEv_eq he rfl
  have state : packState p L X g u q'.val = some ⟨.pst r q,v,k,acc⟩ := by
    simp only [packState, hn, softState, hs]
  have hh : (2*col)/32 = q'.val ∧ (2*col+1)/32 = q'.val := by omega
  change Bf16Pair _ ((softRow p L X g).P u (2*col)) ((softRow p L X g).P u (2*col+1))
  simp only [softRow, hh.1, hh.2, state]
  exact Data.stored_cell hp g v r q k acc hw hat hfi rfl j hj

end PTX.Kernels.TmlFa4Fwd.Proof.Values
