-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatVals
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.PStored
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g i : Nat} {a : Acc}
  {bs : List Byte}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow p L X)
  (hw : Prologue.warpIndex L g < 8)
include hp hX hf hw

/-- The store clause of SoftLink holds on every consistent prefix. -/
theorem soft_pStored (S : Nat → Nat → ℝ)
    (hS : ∀ {i a j u : Nat} {vals : List Value}, X.TLd (g,i) a vals .s32x32b → j < vals.length →
      Tm.sPolls L X g (Prologue.warpIndex L g / 4) i = u+1 →
      vals[j]? = some (.float .f32 (S u
        ((tcDataCell32 L g a j).column - 128*(Prologue.warpIndex L g/4))))) :
    PStored L X g (softRow p L X g).P := by
  apply pStored_of_loads hp hX hf
    (biasReadHandoff hp hX hf (inputsUnwritten hp (Top.noInputWrite hp hX hf))
      (biasWrites hp hX hf)) hw
  intro k ad xs hl w hm
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hm
  obtain ⟨-, -, -, hu, -⟩ := Softmax.soft_ld hp hX hf hw hl
  have eq := hS hl hj hu.symm
  exact ⟨_, Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans eq)⟩

theorem soft_factor_write (pl : Bool) (he : X.get (g,i) = some ⟨(Softmax.Site.stat pl).pc,.wr a bs⟩)
    (hl : LoadsBefore L X (g,i)) :
    ∃ u w, Tm.sPolls L X g (Prologue.warpIndex L g / 4) i = u+1 ∧
      bs = w.toBytes ∧ Softmax.Data.Reads w ((softRow p L X g).f u) :=
  factor_write_of_bias hp hX hf hw
    (biasReadHandoff hp hX hf (inputsUnwritten hp (Top.noInputWrite hp hX hf))
      (biasWrites hp hX hf))
    pl he hl

theorem soft_final_write (j : Fin 2)
    (he : X.get (g,i) = some ⟨(Softmax.Site.fin j).pc,.wr a bs⟩) (hl : LoadsBefore L X (g,i)) :
    bs = (if j = 0 then Value.float .f32 (softRow p L X g).rs
      else if softMaxFinite p L X g then Value.float .f32 (softRow p L X g).rm
      else Softmax.ninf32).toBytes :=
  final_write_of_bias hp hX hf hw
    (biasReadHandoff hp hX hf (inputsUnwritten hp (Top.noInputWrite hp hX hf))
      (biasWrites hp hX hf))
    j he hl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
