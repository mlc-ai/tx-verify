-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
import all Kernels.TmlFa4Fwd.Proof.CorrectionOutputSignal
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue

/-- An active correction lane publishes each output stage before its recorded exit. -/
theorem correctionReadyOfActiveExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat}
    (hWarpLo : 8 ≤ warpIndex l g) (hWarpHi : warpIndex l g < 12)
    (hWork : g/l.block < tilePrefix p p.batch * p.heads)
    (hExit : Exited X g) (stage : Fin 2) : ∃ pos, CorrectionReady X (g,pos) stage := by
  obtain ⟨j,⟨pc,kind⟩,he,hKind⟩ := hExit
  change kind = .exit at hKind
  subst kind
  obtain rfl := actualExitPc hX he
  let site := Correction.outputFencePc stage + 2
  have hAudit : beforeSiteChecked site := by
    fin_cases stage <;> unfold site beforeSiteChecked <;> decide +kernel
  have hMin : 7955 ≤ site := by fin_cases stage <;> decide
  have hMax : site < 9205 := by fin_cases stage <;> decide
  obtain ⟨e,hMem,s,t,hS,hStep⟩ := requiredCorrectionEventOfActiveTail hp hX hWarpLo hWarpHi
    hWork hAudit hMin he hMax
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source hStep
  rw [hS,Correction.readyCode stage] at hCode
  obtain rfl := Option.some.inj hCode
  obtain ⟨_,loc,tx,n,rel,scope,hKind,_,_⟩ := fires_arrive_state hFire
  obtain ⟨j,hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hPc := (estep_source_pc hStep).trans hS
  have hEvent : e = ⟨site,.arrive loc tx n rel scope⟩ := by
    rcases e with ⟨ePc,eKind⟩
    exact congrArg₂ Event.mk hPc hKind
  exact ⟨j,(CorrectionReady.ofActualArrival hp hX stage (hEvent ▸ hGet)).1⟩

end PTX.Kernels.TmlFa4Fwd.Thread
