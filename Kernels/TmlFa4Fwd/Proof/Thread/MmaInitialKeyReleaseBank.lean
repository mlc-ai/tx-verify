-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseUse
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
import Kernels.TmlFa4Fwd.Proof.MmaFirstQueryOperand

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (emptyObject)

/-- The actual first key release follows every fragment of both initial K
banks, with the ordinal-zero key descriptor decoded at each fragment. -/
theorem EmptyReleaseAt.firstKeyBank {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner g position : Nat} {slot : Fin 3}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) g position)
    (hForm : release.form = .firstKey) (stage : Fin 2) (step : Fin 8) :
    ∃ i d op accum mask, QkInstruction X (g,i) (initialQkBlock stage) step d op accum mask ∧
      TraceBefore X (g,release.matched.wait) (g,i) ∧ TraceBefore X (g,i) (g,release.index) ∧
      ∀ byte,
        op.byteLoc .b byte = (qkOperands l g (initialQkBlock stage) step 0).byteLoc .b byte := by
  have hIssue : ReleaseIssue X g release.index .firstKey release.spec := hForm ▸ release.issue
  obtain ⟨start,hBank⟩ := initialQueryOperandsBeforeFirstKeyRelease hp hX hIssue stage
  obtain ⟨d,op,accum,mask,hBefore,hGet,hQ⟩ := hBank step
  let i := start+step.val
  have hMma : QkInstruction X (g,i) (initialQkBlock stage) step d op accum mask :=
    QkInstruction.of_decoded hGet
  have hB := hMma.initialKeyOperand hp hX stage
  have hMatched := release.firstKeyAcquireDecoded hForm
  have hBand : (slotWait 0).pc + 3 ≤ qkPc (initialQkBlock stage)+step.val ∧
      qkPc (initialQkBlock stage)+step.val ≤ (slotElect 0).pc := by
    fin_cases stage <;> fin_cases step <;> decide
  obtain ⟨wait,hLt,loc,parity,acq,scope,hPoll,_⟩ :=
    pendingReadyOrdinal hp hX 0 hGet hBand
  have hSame : wait = release.matched.wait :=
    firstKeyAcquireUnique hp hX (release.issue.issuerWarp hp hX) hPoll hMatched
  refine ⟨i,d,op,accum,mask,hMma,⟨rfl,hSame ▸ hLt,len_of_get hGet⟩,
    ⟨rfl,hBefore,len_of_get hIssue⟩,?_⟩
  intro byte
  simp only [TcMma.OperandSpec.byteLoc,qkOperands,hQ.descriptor,hQ.ctaLow,hQ.ctaHigh,
    hB,reduceCtorEq,false_and,↓reduceIte]
  rfl

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
