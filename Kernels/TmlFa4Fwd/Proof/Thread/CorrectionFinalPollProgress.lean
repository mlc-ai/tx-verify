-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizePoll
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import all Kernels.TmlFa4Fwd.Proof.CorrectionFinalizePoll
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.PollProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue

/-- A reached finalization poll returns once the requested object's actual phase
is ready at each possible stopped frontier. -/
theorem finalizePollOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (stage : Fin 2) (free : Bool)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (finalizePollPc stage free) F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ finalizePollPred stage free)
    (hBase : (finalizePollBase stage free,b32 (finalizePollLoc l g stage free).addr) ∈ F)
    (hPhase : (finalizePollPhase free,b32 free.toNat) ∈ F)
    (hReady : ∀ {t u}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u →
      At u (finalizePollPc stage free) F →
      let log := X.objects (finalizePollLoc l g stage free)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ free.toNat%2) :
    ∃ j, X.get (g,j) = some ⟨finalizePollPc stage free,
        .wait (finalizePollLoc l g stage free) free.toNat true true .cta⟩ ∧
      ∃ nextC : OpeningTripCursor l X g (finalizePollPc stage free+3) F, nextC.pos = j+1 := by
  let pc := finalizePollPc stage free
  let loc := finalizePollLoc l g stage free
  let result := finalizePollPred stage free
  let resume := fun t ok => next (setReg t result (.pred ok))
  have hLo : 8473 ≤ pc := by dsimp only [pc,finalizePollPc]; omega
  have hAddr : loc.addr < 2^32 := by
    have := hp.shared.2.1
    have := stage.isLt
    cases free <;> simp only [loc,finalizePollLoc,Bool.false_eq_true,reduceIte] <;> omega
  have hAlign : loc.addr%8 = 0 := by
    have := hp.shared.1
    cases free <;> simp only [loc,finalizePollLoc,Bool.false_eq_true,reduceIte] <;> omega
  have hParity : free.toNat < 2 := by cases free <;> decide
  obtain ⟨hCode,hBranch,hRetryCode⟩ := finalizePollCode stage free
  have hOut (t : TState) (ht : At t pc F) : t.pc = pc ∧
      out kernel Assumptions.all l g t = .ev (.wait loc free.toNat (resume t) true .cta) := by
    refine ⟨ht.1,?_⟩
    have hSite : t.pc = finalizePollPc stage free := ht.1
    rw [afterPollCore hSite hLo hCode rfl,
      out_event ht.2.2.2.1 (hSite.symm ▸ hCode) rfl rfl]
    change Out.ev (tmaTmpl l g t (.mbarWait result (finalizePollBase stage free)
      0 (.reg (finalizePollPhase free)) true .cta)) = _
    have hLoc : mbarLoc l g t (finalizePollBase stage free) 0 = .ok loc :=
      Flow.mbarLoc_b32 (holds_mem ht.2.2.2.2 hBase) hAddr hAlign
    have hBits := readBits_b32 (L := l) (g := g)
      (holds_mem ht.2.2.2.2 hPhase) (by omega : free.toNat < 2^32)
    simp [tmaTmpl,hLoc,hBits,toNat_ofNat_lt (show free.toNat < 2^64 by omega),hParity,
      bind,Except.bind,pure,Except.pure,ofExec,resume]
  have hRetry (t : TState) (ht : At t pc F) :
      ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) (resume t false) u ∧
        At u pc F :=
    afterCorrectionPoll hLo false hBranch hRetryCode (ht.set hFresh)
  obtain ⟨n,t,ht,he,hPast,hRest,_⟩ :=
    Step.retrying_poll_of_maximal hMax Assumptions.wfStep hg hOut hRetry hReady
      c.positive c.bounded c.released c.checkpoint c.recorded c.remaining c.localSteps
  obtain ⟨v,hLocal,hv⟩ := afterCorrectionPoll hLo true hBranch hRetryCode (ht.set hFresh)
  exact ⟨c.pos+n,he,⟨c.pos+n+1,resume t true,v,c.ending,Nat.succ_pos _,len_of_get he,
    releasedIfLast he (by simp [Kind.resume]),hv,hPast,hRest,hLocal⟩,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Correction
