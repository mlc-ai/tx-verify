-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpDecisionProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRescaleVisit
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalReadProgress
import all Kernels.TmlFa4Fwd.Proof.CorrectionStatsSync
import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Thread.Correction

/-- The actual statistics join and its continuation for either stage of
any rescale iteration. The producer may still owe this generation a publication. -/
structure RescaleWaitReached (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (F : List (Nat × Value)) where
  index : Nat
  state : TState
  ending : Option TState
  joined : X.get (g,index) = some ⟨statsBarrierPc stage true,.bar (statsBarrierId l g stage)
    (some 64) .sync⟩
  ready : At state (statsPc stage .alpha) F
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take (index+1)) (some state)
  remaining : Run kernel Assumptions.all l g state ((X.tr g).drop (index+1)) ending

theorem rescaleWaitReachedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (stage : Fin 2) {F : List (Nat × Value)} (f : RescaleVisitFrame l g stage F)
    (c : OpeningTripCursor l X g (statsBarrierPc stage true) F) :
    ∃ d : RescaleWaitReached l X g stage F, d.index = c.pos := by
  have hCode := statsBarrierCode stage true
  have hModel : out kernel Assumptions.all l g c.ready = out kernel [] l g c.ready := by
    apply Assumptions.out_all_eq_nil _ _ _ (c.checkpoint.1.symm ▸ hCode) rfl
    all_goals rw [c.checkpoint.1]; fin_cases stage <;> decide
  have hOut := statsSyncOut hp stage c.checkpoint hCode hModel
    (holds_mem c.checkpoint.2.2.2.2 f.rendezvous)
  obtain ⟨he,hs,hr⟩ := statsSyncOfCursor hMax hg c hOut
  rw [c.checkpoint.1] at he
  refine ⟨⟨c.pos,next c.ready,c.ending,he,?_,hs,hr⟩,rfl⟩
  have site : statsBarrierPc stage true+1 = statsPc stage .alpha := by fin_cases stage <;> rfl
  exact ⟨c.checkpoint.next.1.trans site,c.checkpoint.next.2⟩

/-- The released join reads a finite coefficient and reaches its matching
ballot with the input frame and tensor ordinal preserved. -/
theorem RescaleWaitReached.ballotLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} {F : List (Nat × Value)}
    (f : RescaleVisitFrame l g stage F) (c : RescaleWaitReached l X g stage F)
    (hRelease : c.index+1 = (X.tr g).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Y.MemWrites = X.MemWrites ∧ Step.Released l Y g) :
    ∃ d : RescaleBallotLane l X g stage (((X.tr g).take c.index).countP isFullWarpVote),
      d.frame = F ∧ d.cursor.pos = c.index+2 ∧
        ((X.tr g).take d.cursor.pos).countP isTcColl = ((X.tr g).take c.index).countP isTcColl ∧
        ∃ bytes, X.get (g,c.index+1) = some ⟨statsPc stage .alpha,
          .rd {loc := statsLoc l g stage .alpha,size := 4} bytes⟩ := by
  obtain ⟨Y,hY,hTrace,hRel⟩ : ∃ Y, Maximal l kernel Assumptions.all m Y ∧
      Y.tr = X.tr ∧ (c.index+1 = (Y.tr g).length → Step.Released l Y g) := by
    by_cases h : c.index+1 = (X.tr g).length
    · obtain ⟨Y,hY,ht,_,hr⟩ := hRelease h
      exact ⟨Y,hY,ht,fun _ => hr⟩
    · exact ⟨X,hMax,rfl,fun e => (h e).elim⟩
  let cur : OpeningTripCursor l Y g (statsPc stage .alpha) F :=
    ⟨c.index+1,c.state,c.state,c.ending,Nat.succ_pos _,by rw [hTrace]; exact len_of_get c.joined,
      hRel,c.ready,by simpa only [hTrace] using c.recorded,
      by simpa only [hTrace] using c.remaining,.refl⟩
  have hCuQ := ((hFrame Y hY.1).metadataProtected hp).1
  have hSync := guardedOfTmaSafe hY.1 (Safety.noTmaUnsafe hp hY.1 hCuQ)
  obtain ⟨bytes,hr,hs,ht⟩ := statsReadRecorded hp hY hSync hg stage .alpha cur f.statistics
  have read : X.get (g,c.index+1) = some ⟨statsPc stage .alpha,
      .rd {loc := statsLoc l g stage .alpha,size := 4} bytes⟩ := by
    simpa only [cur,Execution.get,hTrace,c.ready.1] using hr
  have hStores := Protocol.Statistics.rescaleStoreValuesOfOutputFootprint hp hMax.1 hFrame
  obtain ⟨word,alpha,hBytes,hValue⟩ := Protocol.Statistics.rescaleStatisticsFiniteOfStores hp
    hMax.1 ((hFrame X hMax.1).metadataProtected hp).1 hStores _ stage _ bytes read
  let s := next (setReg c.state (statsReg stage .alpha) word)
  have hActual : afterLoad c.state [statsReg stage .alpha] bytes = s := by
    rw [afterLoad_ok c.ready.2.1 c.ready.2.2.1 hBytes]
    simp [s,next,setReg,c.ready.2.1,c.ready.2.2.1]
  let d : OpeningTripCursor l X g (statsPc stage .alpha+1) ((statsReg stage .alpha,word)::F) :=
    ⟨c.index+2,s,s,c.ending,Nat.succ_pos _,len_of_get read,
      releasedIfLast read (by simp [Kind.resume]),c.ready.set (fun rv hm => (f.control rv hm).1),
      by simpa only [cur,hTrace,hActual] using hs,by simpa only [cur,hTrace,hActual] using ht,.refl⟩
  have vote : ((X.tr g).take d.pos).countP isFullWarpVote =
      ((X.tr g).take c.index).countP isFullWarpVote := by
    rw [show d.pos = c.index+2 from rfl,countP_take_succ_false read rfl,
      countP_take_succ_false c.joined rfl]
  refine ⟨⟨F,word,alpha,hValue,d,vote,fun rv hm => (f.control rv hm).2⟩,rfl,rfl,?_,bytes,read⟩
  exact (countP_take_succ_false (p := isTcColl) read rfl).trans
    (countP_take_succ_false c.joined rfl)

end PTX.Kernels.TmlFa4Fwd.Correction
