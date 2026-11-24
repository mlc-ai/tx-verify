-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalIssueProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.Thread.IdleParticipantExit
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.IdleParticipantExit
import Lemmas.Step.PollProgress
import Lemmas.Step.BarArrival

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.MBarrier Prologue Correction Thread

/-- The terminal statistics object's physical phase permits this lane's acquire. -/
def TerminalCreditAvailable (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (parity : Nat) : Prop :=
  let log := X.objects (statsCreditLoc l (g/l.block) stage)
  ∃ state, stateBefore log log.length = some state ∧ state.phase % 2 ≠ parity % 2

/-- The register frame used by the terminal statistics acquire. -/
def terminalPollFacts (l : Launch) (g : Nat) (warp : Fin 8)
    (parity : Nat) : List (Nat × Value) :=
  (5864,b32 (waitLoc l g (stageOf warp) 9).addr) :: (7258,b32 parity) :: idleCarry l warp

private theorem pollReturning {l : Launch} {g parity : Nat} {warp : Fin 8}
    (ok : Bool) {u : TState} (hAt : At u 7738 (terminalPollFacts l g warp parity)) :
    ∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all l g)
      (next (setReg u 9887 (.pred ok))) w ∧
      At w (if ok then 7741 else 7738) (terminalPollFacts l g warp parity) := by
  have hFrame := hAt.set (v := .pred ok)
    (show ∀ item ∈ terminalPollFacts l g warp parity, item.1 ≠ 9887 from by
      simp [terminalPollFacts,idleCarry])
  obtain ⟨v,hLocal,hAt'⟩ := waitBranch 9 ok (hFrame.mono hFrame.2.2.2.2.2)
    hFrame.2.2.2.2.1
  exact ⟨v,run_rtg hLocal,hAt'⟩

/-- The active lane acquires the released statistics credit and makes its real
arrival at the final allocation barrier. -/
theorem finalAllocationArrivalOfTerminalCredit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (warp : Fin 8) {parity : Nat} (hPar : parity < 2)
    (c : OpeningTripCursor l X g 7738 (terminalPollFacts l g warp parity))
    (hReady : TerminalCreditAvailable l X g (stageOf warp) parity) :
    ∃ j t, FinalAllocationArrival X (g,j) .arrive ∧
      At t 7742 (idleCarry l warp) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) c.ending := by
  let pred := fun u : TState => At u 7738 (terminalPollFacts l g warp parity)
  let resume := fun u ok => next (setReg u 9887 (.pred ok))
  let loc := waitLoc l g (stageOf warp) 9
  have hOut (u : TState) (hu : pred u) : u.pc = 7738 ∧
      out kernel Assumptions.all l g u = .ev (.wait loc parity (resume u) true .cta) :=
    ⟨hu.1,waitTemplate hp (stageOf warp) 9 g u parity hu.1 hu.2.2.2.1 hPar
      hu.2.2.2.2.1 hu.2.2.2.2.2.1⟩
  have hRetry (u : TState) (hu : pred u) :
      ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l g) (resume u false) v ∧
        pred v := pollReturning false hu
  have hLoc : loc = statsCreditLoc l (g/l.block) (stageOf warp) := rfl
  obtain ⟨n,u,hu,he,hPast,hTail,_⟩ := Step.retrying_poll_of_maximal hMax
    Assumptions.wfStep hg hOut hRetry (fun _ _ _ => hLoc.symm ▸ hReady)
    c.positive c.bounded c.released c.checkpoint c.recorded c.remaining c.localSteps
  obtain ⟨w,hLocal,hW⟩ := pollReturning true hu
  let j := c.pos+n
  let t := resume u true
  have hArrive : out kernel Assumptions.all l g w = .ev (.bar 2 (next w) (some 416) .arrive) := by
    rw [out_event hW.2.2.2.1 (by rw [hW.1]; exact Flow.code_7741) rfl rfl]
    simp [eventTmpl,barTmpl,readBits,pure,Except.pure,hp.block,
      show (truncBits 32 2#64).toNat = 2 by decide,
      show (truncBits 32 416#64).toNat = 416 by decide]
  have hMore : j+1 < (X.tr g).length := by
    by_contra! hLe
    have hEq : j+1 = (X.tr g).length := Nat.le_antisymm (len_of_get he) hLe
    have hStarted : X.tr g ≠ [] := by
      intro hNil
      rw [hNil,List.length_nil] at hEq
      omega
    have hFull : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
      rwa [← List.take_of_length_le hLe]
    have hRel : Step.Released l X g := releasedIfLast he (by simp [Kind.resume]) hEq
    exact hMax.not_grows (Step.barArrival_counted_extension hMax.1 hg (.inl hStarted) hRel
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl)) hFull hLocal ⟨_,hArrive,rfl,rfl⟩)
  have hn : Next kernel Assumptions.all l g t w (.bar 2 (next w) (some 416) .arrive) :=
    ⟨hLocal,hArrive⟩
  obtain ⟨_,_,hGet,⟨rfl,hRet⟩,hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) hTail
    (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  have hPre : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1+1)) (some (next w)) := by
    rw [List.take_succ_eq_append_getElem hMore,(List.getElem?_eq_some_iff.mp hGet).2]
    exact hPast.snoc hLocal ⟨_,hArrive,rfl,rfl⟩
  exact ⟨j+1,next w,FinalAllocationArrival.of_decoded (by decide) (hW.1 ▸ hGet),
    hW.next.mono hW.2.2.2.2.2.2,hPre,hRest⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
