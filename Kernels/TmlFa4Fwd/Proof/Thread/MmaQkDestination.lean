-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.InitialScoreBroadcast
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.QkIssueFlags
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Flow.Final
import Lemmas.Flow.Next

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

private def scoreGate (stage : Fin 2) : Nat := 2153+62*stage.val

private def scoreCopySite : Fin 4 → Nat
  | 0 => 2154
  | 1 => 2216
  | 2 => 2364
  | _ => 2465

private def SawScoreGate (X : Execution) (g pos : Nat) (stage : Fin 2) (s : TState) : Prop :=
  scoreGate stage+1 ≤ s.pc → s.pc ≤ 2647 → ∃ j inst lead, j < pos ∧
    X.Elect (g,j) (scoreGate stage) (2^32-1) inst lead

set_option maxRecDepth 100000 in
private theorem scoreGateAudit (stage : Fin 2) : MmaLiveRegAudit (scoreGate stage+1) 2647 1062 := by
  fin_cases stage <;> kernel_rfl

private theorem scoreGateCode (stage : Fin 2) :
    kernel.code[scoreGate stage]? = some ⟨none,.warp
      ⟨.elect,none,[none,
        some (qkGuard (initialQkBlock stage))],[],some (.imm (-1))⟩⟩ := by
  fin_cases stage
  · exact Flow.code_2153
  · exact Flow.code_2215

private theorem scoreGateStep {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g pos : Nat}
    {s u : TState} {ev : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hs : SawScoreGate X g pos stage s) (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,pos) = some e) :
    SawScoreGate X g (pos+ev.toList.length) stage u := by
  intro hLow hHigh
  by_cases hGate : s.pc = scoreGate stage
  · have hc := scoreGateCode stage
    rw [← hGate] at hc
    rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
    · unfold Tau at ht
      rw [out_eq_core (by omega) hHi] at ht
      exact (tau_core_not_event hc rfl ht).elim
    · obtain ⟨ins,hCode,_,hf⟩ := estep_event_source he
      obtain rfl := Option.some.inj (hCode.symm.trans hc)
      obtain ⟨mk,inst,lead,rfl,_⟩ := fires_elect hf
      have hSeen := hActual _ rfl
      rw [hGate] at hSeen
      have hE : X.Elect (g,pos) (scoreGate stage) mk inst lead := hSeen
      exact ⟨pos,inst,lead,Nat.lt_succ_self _,actualFullElectionMask hX hE ▸ hE⟩
  · obtain ⟨hOldLo,hOldHi⟩ := mmaRoleLiveSource (scoreGateAudit stage) hLo hHi
      (Nat.succ_ne_succ_iff.mpr hGate) hw hLow hHigh
    obtain ⟨j,inst,lead,hj,hE⟩ := hs hOldLo hOldHi
    exact ⟨j,inst,lead,by omega,hE⟩

private theorem scoreGateBeforeIssue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g index : Nat}
    {e : Event} (he : X.get (g,index) = some e) (hWarp : warpIndex l g = 12)
    (stage : Fin 2) (hLow : scoreGate stage+1 ≤ e.pc) (hHigh : e.pc ≤ 2647) :
    ∃ j inst lead, j < index ∧ X.Elect (g,j) (scoreGate stage) (2^32-1) inst lead := by
  have hBound : 1907 < scoreGate stage := by fin_cases stage <;> decide
  obtain ⟨t,o,hFrame,hStep⟩ := mmaRoleReplayOfEvent hp hX he hWarp (by omega) (by omega)
    (fun pos s => SawScoreGate X g pos stage s)
    (by
      intro s hs hlo hhi
      rw [hs] at hlo
      omega)
    (by
      intro s u ev pos hLo hHi _ hs hw hActual
      exact scoreGateStep hX stage hLo hHi hs hw hActual)
  have hPc := estep_source_pc hStep
  exact hFrame (hPc ▸ hLow) (hPc ▸ hHigh)

set_option maxRecDepth 100000 in
private theorem scoreReplyFloor (stage : Fin 2) :
    (kernel.code.drop (scoreGate stage)).all (fun i => staysPastEvent (scoreGate stage) i.op) =
      true := by fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem scoreReplySegments (stage : Fin 2) :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (scoreGate stage ≤ seg.stop)
      | none => false) = true := by fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem scoreReplyAudit (stage : Fin 2) :
    MmaLiveRegAudit (scoreGate stage) 2647 (scoreBroadcastRegister stage) := by
  fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem scoreDstAudit (b : Fin 4) :
    MmaLiveRegAudit (scoreCopySite b+1) (qkPc b+7) (qkDestination b) := by
  fin_cases b <;> kernel_rfl

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem scoreCopyLocal (l : Launch) (g : Nat) (b : Fin 4) :
    Seg kernel [] l g 1 (scoreCopySite b)
      [(scoreBroadcastRegister (qkStage b),b32 (scoreColumn (qkStage b)))]
      (scoreCopySite b+1) [(qkDestination b,b32 (scoreColumn (qkStage b)))] := by
  fin_cases b <;> intro t ht <;> seg_fp ht using rfl

/-- The actual initial broadcast fixes the QK output column in both initial and repeated banks. -/
theorem QkInstruction.scoreDestination {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {b : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hi : QkInstruction X i b step d op accum mask) :
    d = scoreColumn (qkStage b) := by
  obtain ⟨g,index⟩ := i
  let stage := qkStage b
  let dest := qkPc b+step.val
  let target : Event := ⟨dest,.tc (.mma d op accum mask)⟩
  have he : X.get (g,index) = some target := hi.decoded
  have hBounds : scoreGate stage+1 ≤ dest ∧ dest ≤ 2647 ∧ dest ∉ registerHintSites := by
    fin_cases b <;> fin_cases step <;> decide
  have hGateRange : 1907 ≤ scoreGate stage ∧ scoreGate stage < 2768 ∧
      scoreGate stage < scoreCopySite b := by fin_cases b <;> decide
  have hWarp := mmaRoleEventWarp hp hX he (by change 1907 < dest; omega)
    (by change dest < 2768; omega) hBounds.2.2
  obtain ⟨gate,inst,lead,hEarly,hGate⟩ :=
    scoreGateBeforeIssue hp hX he hWarp stage hBounds.1 hBounds.2.1
  obtain ⟨send,valid,hSend,hNext⟩ := initialScoreBroadcastOfElection hp hX stage hGate
  obtain ⟨s,visits,hIndex,hs,hw,_,_,_⟩ := mmaRoleWalkOfDemand hp hX hSend hWarp
    (.inl (by change 1907 < 2152+62*stage.val; omega))
  have hAt : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  let broadcast : Event := ⟨2152+62*stage.val,.shfl .idx (b32 (scoreColumn stage))
    0 31 (b32 (scoreColumn stage)) valid⟩
  have hLookup : ((X.tr g).drop 6)[send-6]? = some broadcast := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hIndex]
    exact hSend
  have hLength : send-6+1 < ((X.tr g).drop 6).length := by
    rw [List.length_drop]
    omega
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨by rw [hs.2.1]; decide,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  obtain ⟨t,u,post,hSendStep,hUShape,hUWalk⟩ := pvRoleAfterEvent hw (by rw [hs.1]; decide)
    hShape hLookup hLength (by change 2152+62*stage.val < 2768; omega)
  obtain ⟨hU,hReply⟩ := initialScoreBroadcastFrame stage valid hSendStep
  change u.pc = scoreGate stage at hU
  have hSuffix : ((X.tr g).drop 6).drop (send-6+1) = (X.tr g).drop (send+1) := by
    rw [List.drop_drop,show 6+(send-6+1) = send+1 by omega]
  rw [hSuffix] at hUWalk
  let word := b32 (scoreColumn stage)
  let reply := MmaLiveReg (scoreGate stage) 2647 (scoreBroadcastRegister stage) word
  let stored := MmaLiveReg (scoreCopySite b+1) (qkPc b+7) (qkDestination b) word
  let Inv := fun (_ : Nat) (s : TState) => scoreGate stage ≤ s.pc ∧ reply s ∧ stored s
  obtain ⟨w,o,hFrame,hFire⟩ := mmaRoleReplayAt Inv
    (by
      intro s u ev pos hlo hhi hLive hs hw hActual
      obtain ⟨hFloor,hReply,hStored⟩ := hs
      refine ⟨eventTailStepOfAudit (scoreReplyFloor stage) (scoreReplySegments stage) hFloor hw,
        mmaRoleLiveRegStep (scoreReplyAudit stage) hlo hhi (by omega) hReply hw,?_⟩
      by_cases hCopy : s.pc = scoreCopySite b
      · have hAt : At s (scoreCopySite b) [(scoreBroadcastRegister stage,word)] :=
          ⟨hCopy,hLive.1.2.2 (by rw [hCopy]; fin_cases b <;> decide),hLive.1.2.1,
            mmaRoleReturningNormal (by omega) hhi hw,⟨hReply hFloor (by
              rw [hCopy]
              fin_cases b <;> decide),trivial⟩⟩
        have hLocal := mmaRoleLocalStepAt (by fin_cases b <;> decide)
          (by fin_cases b <;> decide) (scoreCopyLocal l g b) hAt hw
        exact fun _ _ => hLocal.2.2.2.2.2.1
      · exact mmaRoleLiveRegStep (scoreDstAudit b) hlo hhi
          (Nat.succ_ne_succ_iff.mpr hCopy) hStored hw)
    ⟨hU.symm ▸ hGateRange.1,hU.symm ▸ hGateRange.2.1⟩ hUShape
    ⟨hU.ge,fun _ _ => hReply,fun h _ => by omega⟩ hUWalk (by omega) he (by
      change dest < 2768
      omega)
  have hW : w.pc = dest := (estep_source_pc hFire).symm
  have hDst : scoreCopySite b+1 ≤ dest ∧ dest ≤ qkPc b+7 := by
    fin_cases b <;> fin_cases step <;> decide
  have hReg := hFrame.2.2 (hW.symm ▸ hDst.1) (hW.symm ▸ hDst.2)
  cases o with
  | none =>
    obtain ⟨tm,_,hf⟩ := hFire
    rcases fires_none_ends hf with ⟨f,hf⟩ | hf <;> contradiction
  | some v =>
    have hCol : scoreColumn stage < 2^32 := by fin_cases b <;> decide
    change d = scoreColumn stage
    refine (qkStepFields b step (dst := some (scoreColumn stage)) ?_ hFire).1
      (scoreColumn stage) (by simp)
    intro col hc
    have hEq : scoreColumn stage = col := by simpa using hc
    subst col
    exact ⟨hReg,hCol⟩

/-- Every actual QK fragment names the score tile of its phase in its issuing CTA. -/
theorem QkInstruction.scoreCell {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {b : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hi : QkInstruction X i b step d op accum mask)
    (row col : Fin 128) : TcMma.resultCell op d row.val col.val =
      some ⟨i.1/l.block,row.val,scoreColumn (qkStage b)+col.val⟩ := by
  have hQuery := hi.queryOperand hp hX
  rw [hi.scoreDestination hp hX,qkResultCell hQuery.descriptor,hQuery.ctaLow]

end PTX.Kernels.TmlFa4Fwd.Thread
