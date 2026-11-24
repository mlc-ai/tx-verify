-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOutputReadyTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingAcquire
import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Thread.Correction (FirstOutputAcquire StageZeroStagingWrites)

noncomputable section

private abbrev beforeFirstReady (pos : Nat) : Prop :=
  7755 ≤ pos ∧ pos ≤ 8760 ∨ 9201 ≤ pos ∧ pos ≤ 9205

private def firstReadyCode (pos : Nat) (ins : Instr) : Bool :=
  if beforeFirstReady pos then
    (ins.op.isLocal || Epilogue.ordinaryEvent ins.op) &&
      match ins.op with
      | .bra dest _ => decide (beforeFirstReady dest)
      | .brx .. => false
      | _ => true
  else true

set_option maxRecDepth 100000 in
private theorem firstReadyControl :
    (((kernel.code.drop 7755).take (9205-7755)).zipIdx 7755).all
      (fun (i,pos) => firstReadyCode pos i) = true := by kernel_rfl

private theorem firstReadyCodeAt {s : TState} {ins : Instr}
    (hBand : beforeFirstReady s.pc) (hHi : s.pc < 9205)
    (hGet : kernel.code[s.pc]? = some ins) :
    (ins.op.isLocal || Epilogue.ordinaryEvent ins.op) = true ∧
      (match ins.op with
        | .bra dest _ => decide (beforeFirstReady dest)
        | .brx .. => false
        | _ => true) = true := by
  have hLo : 7755 ≤ s.pc := by rcases hBand with h | h <;> omega
  have hMem : (ins,s.pc) ∈ ((kernel.code.drop 7755).take (9205-7755)).zipIdx 7755 := by
    apply List.mem_of_getElem? (i := s.pc-7755)
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hGet]
    rfl
  exact Bool.and_eq_true_iff.mp (by
    simpa only [firstReadyCode,hBand,↓reduceIte] using
      List.all_eq_true.mp firstReadyControl _ hMem)

private theorem firstReadyStays {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hBand : beforeFirstReady s.pc) (hNot : s.pc ≠ 8760) (hHi : s.pc < 9205)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    beforeFirstReady u.pc := by
  have hSucc (h : u.pc = s.pc+1) : beforeFirstReady u.pc := by
    rcases hBand with hBand | hBand
    · exact .inl ⟨by omega,by omega⟩
    · exact .inr ⟨by omega,by omega⟩
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false]
      rcases hBand with hb | hb <;> omega
    obtain ⟨ins,hCode,_,hLocal⟩ := correctionTauFrame hOff hTau
    rcases hLocal with ⟨rfl,_⟩ | ⟨_,_,hFrame⟩
    · exact hSucc rfl
    have hAudit := (firstReadyCodeAt hBand hHi hCode).2
    have hNext := hFrame.pc
    cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hNext
    case bra dest uni => simpa [hOp,hNext] using hAudit
    case brx => simp [hOp] at hAudit
    all_goals exact hSucc hNext
  · obtain ⟨ins,hCode,hNotLocal,hFires⟩ := estep_event_source hEvent
    have hAudit := (firstReadyCodeAt hBand hHi hCode).1
    simp only [hNotLocal,Bool.false_or] at hAudit
    rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hAudit) hFires with h | h
    · exact h.symm ▸ hBand
    · exact hSucc h

private theorem readyZeroNotSilent {l : Launch} {g : Nat} {s u : TState}
    (hPc : s.pc = 8760) (h : Tau kernel Assumptions.all l g s u) : False := by
  cases hf : s.fault
  · exact not_tau_of_stops ⟨_,out_event hf (hPc.symm ▸ Flow.code_8760) rfl rfl⟩ h
  · simp only [Tau,out,hf,reduceCtorEq] at h

private theorem firstReadyObserved {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hBand : beforeFirstReady s.pc) {index : Nat} {target : Event}
    (hGet : es[index]? = some target) (hTarget : 8760 < target.pc ∧ target.pc < 9201) :
    ∃ j < index, ∃ loc tx n rel scope,
      es[j]? = some ⟨8760,.arrive loc tx n rel scope⟩ := by
  have hImpossible {t : TState} (hBand : beforeFirstReady t.pc) (hEq : t.pc = target.pc) :
      False := by rcases hBand with h | h <;> omega
  induction hw generalizing index with
  | stop => simp at hGet
  | @last t e he =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hGet
      exact (hImpossible hBand ((estep_source_pc he).symm.trans (congrArg Event.pc hGet))).elim
    | succ index => simp at hGet
  | @tau t u events visits ht hw ih =>
    have hHi : t.pc < 9205 := by
      by_contra! h
      have hT := correctionReturnTail (by rcases hBand with h | h <;> omega : t.pc = 9205)
        (.tau ht hw) (List.mem_of_getElem? hGet)
      omega
    have hNo : t.pc ≠ 8760 := fun h => readyZeroNotSilent h ht
    exact ih (firstReadyStays hBand hNo hHi (.inl ⟨rfl,ht⟩)) hGet
  | @ev t u e events visits he hw ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hGet
      exact (hImpossible hBand ((estep_source_pc he).symm.trans (congrArg Event.pc hGet))).elim
    | succ index =>
      have hTail : events[index]? = some target := hGet
      by_cases hPc : t.pc = 8760
      · obtain ⟨ins,hCode,_,hFires⟩ := estep_event_source he
        rw [hPc,Flow.code_8760] at hCode
        obtain rfl := Option.some.inj hCode
        obtain ⟨_,loc,tx,n,rel,scope,hKind,_,_⟩ := fires_arrive_state hFires
        refine ⟨0,Nat.zero_lt_succ index,loc,tx,n,rel,scope,?_⟩
        have hEventPc := (estep_source_pc he).trans hPc
        cases e
        simp_all
      · have hHi : t.pc < 9205 := by
          by_contra! h
          have hT := correctionReturnTail (by rcases hBand with h | h <;> omega : t.pc = 9205)
            (.ev he hw) (List.mem_cons_of_mem e (List.mem_of_getElem? hTail))
          omega
        obtain ⟨j,hj,loc,tx,n,rel,scope,hReady⟩ :=
          ih (firstReadyStays hBand hPc hHi (.inr ⟨e,rfl,he⟩)) hTail
        exact ⟨j+1,by omega,loc,tx,n,rel,scope,hReady⟩

/-- An actual second-stage staging write follows its lane's first-stage ready publication. -/
theorem StageStagingWrite.firstReadyBeforeSecond {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {bytes : List Byte} (h : StageStagingWrite X writer 1 a bytes) :
    ∃ ready, CorrectionReady X ready 0 ∧ TraceBefore X ready writer := by
  obtain ⟨g,index⟩ := writer
  obtain ⟨box,chunk,hStore⟩ := h.decoded
  let target : Event := ⟨outputStorePc 1 box chunk,.wr a bytes⟩
  have hGet : X.get (g,index) = some target := hStore
  have hRange : 8760 < target.pc ∧ target.pc < 9201 := by
    change 8760 < outputStorePc 1 box chunk ∧ outputStorePc 1 box chunk < 9201
    fin_cases box <;> fin_cases chunk <;> decide
  have hHint : target.pc ∉ registerHintSites := by
    simp only [registerHintSites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX hGet (by omega) hHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  obtain ⟨s,_,_,hAt,_,_,_,_,_,_,hRun,hIndex⟩ :=
    correctionEntryBeforeEvent hp hX (event_thread_lt hX hGet) hWarp.1 hWarp.2 hGet
      (.inl (by omega))
  obtain ⟨_,hw⟩ := Mma.walkFromRun hRun
  have hTail : ((X.tr g).drop 9)[index-9]? = some target := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  obtain ⟨j,hBefore,loc,tx,n,rel,scope,hReady⟩ :=
    firstReadyObserved hw (by rw [hAt.1]; decide) hTail hRange
  rw [List.getElem?_drop] at hReady
  have hRaw : X.get (g,9+j) = some ⟨outputFencePc 0+2,.arrive loc tx n rel scope⟩ :=
    hReady
  exact ⟨(g,9+j),(CorrectionReady.ofActualArrival hp hX 0 hRaw).1,
    ⟨rfl,by omega,(List.getElem?_eq_some_iff.mp hGet).1⟩⟩

/-- Later stage-one staging runs after the stage-zero output acquire and its shared proxy fence. -/
theorem StageStagingWrite.firstAcquireFenceBeforeSecond {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {bytes : List Byte} (h : StageStagingWrite X writer 1 a bytes) :
    ∃ wait fence, FirstOutputAcquire l X wait ∧
      X.IsProxyFence fence (.async (some (.shared .cta))) none ∧
      TraceBefore X wait fence ∧ TraceBefore X fence writer := by
  obtain ⟨⟨g,j⟩,hReady,hLater⟩ := h.firstReadyBeforeSecond hp hX
  obtain ⟨prev,fence,_,_,hStage,hWriteBefore,hFenceBefore,hFence⟩ :=
    hReady.finalWriteAndFence hp hX
  obtain ⟨box,chunk,hGet⟩ := hStage.decoded
  obtain ⟨wait,hWait,hOrder⟩ :=
    (StageZeroStagingWrites.of_event box chunk hGet).firstAcquire hp hX
  exact ⟨wait,(g,fence),hWait,hFence,
    ⟨hOrder.1.trans hWriteBefore.1,hOrder.2.1.trans hWriteBefore.2.1,hWriteBefore.2.2⟩,
    hFenceBefore.trans hLater⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
