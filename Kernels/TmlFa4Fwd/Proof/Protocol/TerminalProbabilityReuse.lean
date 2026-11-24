-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityParity
public import Kernels.TmlFa4Fwd.Proof.Protocol.SoftmaxProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarRingRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.AsyncCopy Thread.Scores
open PTX.MBarrier hiding okPolls

/-- A terminal correction credit has a prior successful joint probability poll, at least
as recent as the generation of its last required score commit. -/
theorem terminalCorrectionProbabilityGuard {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g score : EvId} {cta atCredit : Nat} {stage : Fin 2} {r : Record Ref}
    (hr : (X.objects (probabilityObject l cta stage 0))[atCredit]? = some r)
    (hId : r.id = .thread g) (hCredit : ProbabilityCredit l X g cta stage 0)
    (hTerminal : TerminalProbabilityCredit l X g cta stage)
    {s : TcCommit.Spec} {rank : Fin 16} (hScore : ScoreCommit l X score cta stage s rank)
    (hLo : probabilityOrdinal l X cta stage 0 g - 1 ≤ scoreCommitOrdinal l X cta stage score) :
    let loc := probabilityObject l cta stage 0
    ∃ k w st, k < atCredit ∧ (X.objects loc)[k]? = some w ∧ w.reply.waited = some true ∧
      stateBefore (X.objects loc) k = some st ∧ probabilityOrdinal l X cta stage 0 g ≤
        st.phase := by
  let loc := probabilityObject l cta stage 0
  let log := X.objects loc
  have hClean : ∀ r ∈ log, (∃ p ok, r.action = .pollParity p ok) → r.fault = none :=
    fun _ hr hs => actualInitOrPollClean hp hX hr (.inr hs)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨out,spec,hOut,hOwner,hDep⟩ := terminalCreditDependsOnMmaOutput hp hX hTerminal
  obtain ⟨k,e,q,acq,scope,hGet,hKind,hBudget,hResume⟩ :=
    terminalOutputProbabilityAfterScore hp hX hOut hOwner hScore
  obtain ⟨source,kind⟩ := e
  change kind = _ at hKind
  subst kind
  let n := okPolls loc ((X.tr out.1).take k)
  have hNth := MbarRing.Poll.nth_eq hGet
  have hLt : n < okPolls loc (X.tr out.1) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  obtain ⟨i,w,_,hW,hWId,_,hOk,_,hCount⟩ := MbarRing.Poll.record hX hClean hLt
  rw [hNth] at hWId
  have hSel := objectThreadSelected_iff.mpr ⟨_,hWId⟩
  have hChecked := X.objects_checked hX loc
  have hAlt := probabilitySelectedAlternates hp hX (g := out.1) (cta := cta) stage 0
  obtain ⟨st,hState,hLower,_⟩ := hChecked.selected_poll_phase_ge hNo
    (objectThreadSelected out.1) (by decide) hAlt hW hSel hOk
  have hPath := (Relation.TransGen.single (DepStep.of_resumes l hResume)).trans hDep
  rw [← hWId, ← hId] at hPath
  have hNot := MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hPath
  have hBefore : i < atCredit := by
    rcases Nat.lt_trichotomy i atCredit with h | rfl | h
    · exact h
    · obtain rfl := Option.some.inj (hW.symm.trans hr)
      obtain ⟨ref,source,parity,acq,scope,hRef,hWait⟩ := hX.wait_of_record hr hOk
      have hSame := Ref.thread.inj (hRef.symm.trans hId)
      rw [hSame] at hWait
      obtain ⟨_,hGet⟩ := hCredit
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hGet.symm.trans hWait)))
    · exact (hNot ⟨atCredit,i,r,w,hr,rfl,hW,rfl,h⟩).elim
  change _ ≤ n at hBudget
  exact ⟨i,w,st,hBefore,hW,hOk,hState,by omega⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
