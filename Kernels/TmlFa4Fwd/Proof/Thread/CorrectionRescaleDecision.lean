-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleBranch
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Lemmas.Execution.EventFrameSource
import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.EventFrame
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

private def rescaleBallotOp (stage : Fin 2) : Op :=
  .warp ⟨.vote .ballot false, some (.int .b 32), [some (rescaleVoteReg stage)],
    [.reg (rescalePredReg stage)], some (.imm (-1))⟩

private theorem rescaleBallotCode (stage : Fin 2) :
    kernel.code[statsPc stage .alpha + 2]? = some ⟨none, rescaleBallotOp stage⟩ := by
  fin_cases stage
  · exact Flow.code_8009
  · exact Flow.code_8228

/-- A returning ballot is the actual decoded full-mask vote, followed by its exact branch.
The event and branch both preserve the loop counter. -/
theorem correctionRescaleActualBranch {l : Launch} {g : Nat} {s t : TState}
    {e : Event} {counter : Value} (stage : Fin 2)
    (hPc : s.pc = statsPc stage .alpha + 2) (hs : s.sub = 0) (hAcc : s.acc = [])
    (hCounter : s.regs 7278 = some counter)
    (he : EStep kernel Assumptions.all l g s e (some t)) :
    ∃ bit word u, e = ⟨statsPc stage .alpha + 2, .vote (2^32-1) bit word⟩ ∧
      At u (if word = 0 then rescaleSkipPc stage else rescaleLoadPc stage 0)
        [(7278,counter)] ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hFault : s.fault = none := by
    cases hf : s.fault
    · rfl
    · obtain ⟨tm, ht, hf'⟩ := he
      simp only [out, hf, Out.ev.injEq] at ht
      subst tm
      cases hf'.2
  obtain ⟨i, hCode, _, hFire⟩ := estep_event_source he
  rw [hPc,rescaleBallotCode] at hCode
  obtain rfl := Option.some.inj hCode
  change Fires s.pc (voteTmpl l g s (rescaleVoteReg stage)
    (rescalePredReg stage) false (.imm (-1))) e (some t) at hFire
  have hFresh : 7278 ≠ rescaleVoteReg stage := by fin_cases stage <;> decide
  have hFresh' : 7278 ≠ maskZeroReg stage := by fin_cases stage <;> decide
  unfold voteTmpl at hFire
  split at hFire
  · split_ifs at hFire with hFull
    · obtain ⟨word,hEv,hu⟩ := hFire
      obtain rfl := Option.some.inj hu
      have hAt : At (next (setReg s (rescaleVoteReg stage) (b32 word.toNat)))
          (statsPc stage .alpha + 3) [(7278,counter)] := by
        refine ⟨by simp [next,setReg,hPc,Nat.add_assoc],hs,hAcc,hFault,?_⟩
        simp [next,setReg,hFresh,hCounter]
      obtain ⟨u,hOut,hSteps⟩ := rescaleDecisionSteps stage word hAt
        (by simp [next,setReg,b32]) (by simp [hFresh'])
      exact ⟨_,word,u,by simpa only [hPc,hFull.1] using hEv,hOut,hSteps⟩
    · cases hFire.2
  all_goals cases hFire.2

/-- A correction ballot instruction is unguarded and cannot be traversed locally. -/
theorem correctionRescaleBallotNoTau {l : Launch} {g : Nat} {s u : TState}
    (stage : Fin 2) (hPc : s.pc = statsPc stage .alpha + 2) :
    ¬ Tau kernel Assumptions.all l g s u := by
  intro ht
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; fin_cases stage <;> decide
  obtain ⟨i,hc,_,hExec⟩ := correctionTauFrame hOff ht
  rw [hPc,rescaleBallotCode] at hc
  obtain rfl := Option.some.inj hc
  rcases hExec with ⟨_,hGuard⟩ | ⟨_,hLocal,_⟩
  · cases hGuard
  · cases hLocal

end
end PTX.Kernels.TmlFa4Fwd.Thread
