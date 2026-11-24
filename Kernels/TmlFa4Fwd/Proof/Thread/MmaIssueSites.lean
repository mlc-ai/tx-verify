-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvIssue
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Flow.NotTcMma
import Lemmas.Flow.OpPcsFast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private def mmaIssueSites : List Nat :=
  (List.finRange 4).flatMap fun bank =>
    (List.finRange 8).flatMap fun frag => [qkPc bank + frag.val,pvPc bank frag]

set_option maxRecDepth 100000 in
private theorem mmaIssueCode : OpPcsFast kernel.code tcMmaOp mmaIssueSites = true := by
  kernel_rfl

/-- Every actual MMA issue belongs to one of the decoded QK or PV banks. -/
theorem mmaIssueBank {l : Launch} {m : Mem0} {X : Execution} {A : List Assumption}
    (hX : Consistent l kernel A m X) {i : EvId} {pc d : Nat}
    {spec : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (he : X.get i = some ⟨pc,.tc (.mma d spec accum mask)⟩) :
    ∃ bank : Fin 4, ∃ frag : Fin 8, pc = qkPc bank + frag.val ∨ pc = pvPc bank frag := by
  rcases get_source hX he with ⟨_,hf⟩ | ⟨_,_,_,_,hCode,hFires⟩
  · cases hf
  have hSite := OpPcsFast.mem mmaIssueCode hCode (fires_tcMma_op hFires rfl)
  obtain ⟨bank,_,hb⟩ := List.mem_flatMap.mp hSite
  obtain ⟨frag,_,hf⟩ := List.mem_flatMap.mp hb
  exact ⟨bank,frag,by simpa using hf⟩

/-- The single-visit schedule leaves only the two initial QK banks and the two tail PV banks. -/
theorem singleVisitMmaIssueBank {l : Launch} {m : Mem0} {X : Execution} {A : List Assumption}
    (hX : Consistent l kernel A m X) {i : EvId} {pc d : Nat}
    {spec : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (he : X.get i = some ⟨pc,.tc (.mma d spec accum mask)⟩)
    (hVisit : pc < 2279 ∨ 2534 ≤ pc) :
    (∃ stage : Fin 2, ∃ frag : Fin 8,
      pc = qkPc ⟨stage.val,by have := stage.isLt; omega⟩ + frag.val) ∨
    (∃ stage : Fin 2, ∃ frag : Fin 8,
      pc = pvPc ⟨2 + stage.val,by have := stage.isLt; omega⟩ frag) := by
  obtain ⟨bank,frag,hQk | hPv⟩ := mmaIssueBank hX he
  · have hBank : bank.val < 2 := by
      subst pc
      fin_cases bank <;> fin_cases frag <;> simp [qkPc] at hVisit ⊢
    exact .inl ⟨⟨bank.val,hBank⟩,frag,hQk⟩
  · have hBank : 2 ≤ bank.val := by
      subst pc
      fin_cases bank <;> fin_cases frag <;> simp [pvPc,pvSite] at hVisit ⊢
    have hBound : bank.val - 2 < 2 := by
      have := bank.isLt
      omega
    have hEq : (⟨2 + (bank.val - 2),by have := bank.isLt; omega⟩ : Fin 4) = bank :=
      Fin.ext (show 2 + (bank.val - 2) = bank.val by omega)
    exact .inr ⟨⟨bank.val - 2,hBound⟩,frag,hEq.symm ▸ hPv⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
