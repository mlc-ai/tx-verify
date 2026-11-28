-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalWrites
import Kernels.InklingRelDecode.Proof.Lib.OutputRange

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noAssumptionUb (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (placed : Protocol.Shared.OutputPlaced Q X) :
    ¬ (∃ a ∈ Assumptions.all, a.ub L m X) := by
  have hin : ¬ Assumptions.inputReadOnly.ub L m X := by
    rintro ⟨P,ref,a,l,other,intent,cover,gl,_,hit⟩
    obtain ⟨o,lse,ob,lb⟩ := Lib.out_pinned hp other
    obtain ⟨na,nb⟩ := other.outputsApart _ hit
    rw [o,ob] at na
    rw [lse,lb] at nb
    exact (Protocol.Shared.output_intent hp hX placed intent cover gl).elim na nb
  rintro ⟨a, ha, hu⟩
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact (show False from hu)
    | exact hin hu

end PTX.Kernels.InklingRelDecode.Proof.Top
