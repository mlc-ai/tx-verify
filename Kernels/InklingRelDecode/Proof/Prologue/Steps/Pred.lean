-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Election
import Lemmas.Flow.RegBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

/-- The predicate written immediately after a full-mask election is the conjunction
of eligibility and winning. The leader register is already outside the frame. -/
theorem and_vote {L g pc dst elig p} {ok win : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none,.int ⟨.and,.pred,false,[some dst],[.reg elig,.reg p]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false)
    (eligible : (elig,.pred ok) ∈ F) (fresh : dst ∉ F.map Prod.fst) :
    SegU kernel Assumptions.all L g pc ((p,.pred win)::F)
      (pc+1) ((dst,.pred (ok && win))::F) := by
  apply Lib.scalarStepU hc rfl rfl hs
  · intro t u h he
    obtain ⟨pred,old⟩ := h
    have hv := holds_mem old eligible
    simp only [execInt,DType.width,ite_true,readPred,readReg,pred,hv,bind,Except.bind,
      pure,Except.pure] at he
    exact (Except.ok.inj he).symm
  · intro R h
    exact ⟨Function.update_self ..,holds_update h.2
      (fun q hq eq => fresh (eq ▸ List.mem_map_of_mem hq))⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
