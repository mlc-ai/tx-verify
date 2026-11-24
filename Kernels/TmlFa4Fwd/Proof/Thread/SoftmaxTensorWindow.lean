-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionInitialTensorCoverage
public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstRound
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.Final
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part104

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open _root_.PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

private def softWindow : Softmax.Round → ScoreWindow
  | .first => .firstRoundCounters
  | .biased => .biasedBody
  | .unbiased => .plainBody

private def startPc (round : Softmax.Round) : Nat := (windowSite (softWindow round)).head
private def finishPc (round : Softmax.Round) : Nat := (windowSite (softWindow round)).stop

private def eventToken (e : Event) : Option (Nat × Fin 4) :=
  (correctionTensorOperation e.kind).map (e.pc, ·)

private def instructionTokens (pc : Nat) : Op → List (Nat × Fin 4)
  | .tcLd .. => if Assumptions.all.any (·.tcLdWait pc) then [(pc,0),(pc,1)] else [(pc,0)]
  | .tcSt .. => if Assumptions.all.any (·.tcStWaitLd pc) then [(pc,1),(pc,2)] else [(pc,2)]
  | .tcWaitSt => [(pc,3)]
  | _ => []

private def tokenSlice (hi pc : Nat) : List (Nat × Fin 4) :=
  (((kernel.code.drop pc).take (hi-pc)).zipIdx pc).flatMap
    (fun (ins,site) => instructionTokens site ins.op)

private def pendingTokens (hi : Nat) (s : TState) : List (Nat × Fin 4) :=
  if s.pc < hi then
    let head := ((kernel.code[s.pc]?).map (fun i => instructionTokens s.pc i.op)).getD []
    (head.drop (if head.length = 2 ∧ s.sub ≠ 0 then 1 else 0)) ++ tokenSlice hi (s.pc+1)
  else []

/-- The Tensor Memory positions and operations of one softmax visit. In the two biased
visits the load waits occur at the probability stores. -/
@[no_expose] def softmaxVisitTokens (round : Softmax.Round) : List (Nat × Fin 4) :=
  let ld : List (Nat × Fin 4) := (List.finRange 4).flatMap fun q =>
    if round = .unbiased then [(scorePc round q,0),(scorePc round q,1)] else [(scorePc round q,0)]
  let store (q : Fin 4) : List (Nat × Fin 4) :=
    if round ≠ .unbiased ∧ q = 0 then [(probabilityPc round q,1),(probabilityPc round q,2)]
    else [(probabilityPc round q,2)]
  ld ++ store 0 ++ store 1 ++ store 2 ++ [(probabilityWaitPc round false,3)] ++
    store 3 ++ [(probabilityWaitPc round true,3)]

set_option maxRecDepth 100000 in
private theorem softmaxVisitTokenTable (round : Softmax.Round) :
    tokenSlice (finishPc round) (startPc round) = softmaxVisitTokens round := by
  cases round <;> decide +kernel

private theorem tokenSliceNext {hi pc : Nat} (hs : pc < hi) {i : Instr}
    (hc : kernel.code[pc]? = some i) :
    tokenSlice hi pc = instructionTokens pc i.op ++ tokenSlice hi (pc+1) := by
  obtain ⟨hLen,hI⟩ := List.getElem?_eq_some_iff.mp hc
  have hDrop := List.drop_eq_getElem_cons hLen
  rw [hI] at hDrop
  unfold tokenSlice
  rw [show hi-pc = hi-(pc+1)+1 by omega,hDrop,List.take_succ_cons,List.zipIdx_cons,
    List.flatMap_cons]

private theorem pendingOfClear {hi : Nat} {s : TState} (hs : s.sub = 0) :
    pendingTokens hi s = tokenSlice hi s.pc := by
  by_cases hh : s.pc < hi
  · unfold pendingTokens
    rw [ite_eq_left hh]
    cases hc : kernel.code[s.pc]? with
    | some i => simp [hs,tokenSliceNext hh hc]
    | none =>
      have hLen := List.getElem?_eq_none_iff.mp hc
      simp [tokenSlice,List.drop_eq_nil_of_le hLen,
        List.drop_eq_nil_of_le (show kernel.code.length ≤ s.pc+1 by omega)]
  · have hh' : hi-s.pc = 0 := by omega
    simp [pendingTokens,hh,tokenSlice,hh']

private def supportedTokenOp (i : Instr) : Bool :=
  match i.op with
  | .tcLd _ _ .s32x32b none | .tcSt _ _ .s32x32b | .tcWaitSt => i.guard.isNone
  | op => !tcDataOp op && (op.isLocal ||
      (scoreEventOp op && !(scoreEventWrites op).contains 0 && Epilogue.ordinaryEvent op))

private def tokenJump (lo hi pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra target _ => decide (lo ≤ target ∧ target ≤ hi ∧ tokenSlice hi pc = tokenSlice hi target)
  | .brx .. => false
  | _ => true

private def tokenWindowChecked (round : Softmax.Round) : Prop :=
  let lo := startPc round
  let hi := finishPc round
  (((kernel.code.drop lo).take (hi-lo)).zipIdx lo).all
    (fun (ins,pc) => supportedTokenOp ins && tokenJump lo hi pc ins.op) = true

set_option maxRecDepth 100000 in
private theorem firstTokenWindowChecked : tokenWindowChecked .first := by
  unfold tokenWindowChecked
  decide +kernel

set_option maxRecDepth 100000 in
private theorem biasedTokenWindowChecked : tokenWindowChecked .biased := by
  unfold tokenWindowChecked
  decide +kernel

set_option maxRecDepth 100000 in
private theorem plainTokenWindowChecked : tokenWindowChecked .unbiased := by
  unfold tokenWindowChecked
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tokenWindowAudit (round : Softmax.Round) {pc : Nat} {i : Instr}
    (hLo : startPc round ≤ pc) (hHi : pc < finishPc round)
    (hc : kernel.code[pc]? = some i) :
    (supportedTokenOp i && tokenJump (startPc round) (finishPc round) pc i.op) = true := by
  let lo := startPc round
  let hi := finishPc round
  let code := ((kernel.code.drop lo).take (hi-lo)).zipIdx lo
  have hAll : tokenWindowChecked round := by
    cases round
    · exact firstTokenWindowChecked
    · exact biasedTokenWindowChecked
    · exact plainTokenWindowChecked
  have hp : lo ≤ pc := hLo
  have hq : pc < hi := hHi
  have hm : code[pc-lo]? = some (i,pc) := by
    dsimp only [code]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hp,hc]
    rfl
  exact List.all_eq_true.mp hAll (i,pc) (List.mem_of_getElem? hm)

private theorem noInstructionTokens {pc : Nat} {o : Op} (h : tcDataOp o = false) :
    instructionTokens pc o = [] := by cases o <;> simp_all [instructionTokens,tcDataOp]

private theorem tokensAtOrdinary {hi : Nat} {s : TState} {i : Instr}
    (hHi : s.pc < hi) (hc : kernel.code[s.pc]? = some i) (h : tcDataOp i.op = false) :
    pendingTokens hi s = tokenSlice hi (s.pc+1) ∧ tokenSlice hi s.pc = pendingTokens hi s := by
  simp [pendingTokens,hHi,hc,noInstructionTokens h,tokenSliceNext hHi hc]

variable {l : Launch}

private theorem loadTokenWithWait {g : Nat} {s u : TState} {e : Event} {ds : List Nat} {ta : Nat}
    (hHook : Assumptions.all.any (·.tcLdWait s.pc) = true) (hs : s.sub = 0)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.tcLd ds ta .s32x32b none)) e (some u))
    : eventToken e = some (s.pc,0) ∧ u.pc = s.pc ∧ u.sub = 1 := by
  have hShape : ∀ sh, TcShape.s32x32b ≠ .packed16 sh := by intro _ h; cases h
  simp only [eventTmpl,tcLdTmpl,hHook,hs,↓reduceIte,tcTmpl_tcLd_none hShape] at hf
  cases ha : readBits l g s 32 (.reg ta) with
  | error f =>
    simp [ofExec,ha,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp [Tmpl.thenWaitLd,Fires] at hf
  | ok v =>
    simp [ofExec,ha,bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Tmpl.thenWaitLd,Fires,reduceCtorEq,and_false] at hf
    obtain ⟨_,_,rfl,hu⟩ := hf
    obtain rfl := Option.some.inj hu
    exact ⟨rfl,rfl,rfl⟩

private theorem storeTokenOfCore {g pc : Nat} {s u : TState} {e : Event} {ta : Nat} {ss : List Opnd}
    (hf : Fires pc (tcTmpl l g s (.tcSt ta ss .s32x32b)) e (some u)) :
    eventToken e = some (pc,2) ∧ u = next s := by
  cases ha : readBits l g s 32 (.reg ta) <;>
  cases hv : ss.mapM (readValue l g s 32) <;>
    simp only [tcTmpl,ofExec,ha,hv,bind,Except.bind,pure,Except.pure,throw,throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires,reduceCtorEq,and_false] at hf
  obtain ⟨rfl,hu⟩ := hf
  exact ⟨rfl,Option.some.inj hu⟩

private theorem pendingAtLoad {g hi : Nat} {s u : TState} {e : Event} {i : Instr} {ds : List Nat}
    {ta : Nat} (hHi : s.pc < hi) (hc : kernel.code[s.pc]? = some i)
    (hop : i.op = .tcLd ds ta .s32x32b none) (hS : ScoreScratchReady i.op s)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s i.op) e (some u)) :
    pendingTokens hi s = (eventToken e).toList ++ pendingTokens hi u := by
  rw [hop] at hf hS
  by_cases hHook : Assumptions.all.any (·.tcLdWait s.pc) = true
  · by_cases hz : s.sub = 0
    · obtain ⟨hT,hPc,hSub⟩ := loadTokenWithWait hHook hz hf
      simp [hT,pendingTokens,hHi,hc,hop,hHook,hz,hPc,hSub,instructionTokens]
    · obtain ⟨rfl,rfl⟩ := fires_tcLd_wait hHook hz hf
      rw [pendingOfClear (s := { next s with sub := 0 }) rfl]
      simp [eventToken,correctionTensorOperation,pendingTokens,hHi,hc,hop,hHook,hz,
        instructionTokens,next]
  have hOff : Assumptions.all.any (·.tcLdWait s.pc) = false := by simpa using hHook
  have hClear : s.sub = 0 := by simpa [ScoreScratchReady,hOff] using hS.1
  obtain ⟨_,values,_,rfl,rfl⟩ := fires_tcLd (by intro _ h; cases h) hf hOff
  have hSub : (setRegs (next s) ds values).sub = 0 :=
    ((setRegs_skel (next s) ds values).2.1).trans hClear
  rw [pendingOfClear (s := setRegs (next s) ds values) hSub,
    (setRegs_skel (next s) ds values).1]
  simp [eventToken,correctionTensorOperation,pendingTokens,hHi,hc,hop,hOff,hClear,
    instructionTokens,next]

private theorem pendingAtStore {g hi : Nat} {s u : TState} {e : Event} {i : Instr} {ta : Nat}
    {ss : List Opnd} (hHi : s.pc < hi) (hc : kernel.code[s.pc]? = some i)
    (hop : i.op = .tcSt ta ss .s32x32b) (hS : ScoreScratchReady i.op s)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s i.op) e (some u)) :
    pendingTokens hi s = (eventToken e).toList ++ pendingTokens hi u := by
  rw [hop] at hf hS
  by_cases hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = true
  · by_cases hz : s.sub = 0
    · simp only [eventTmpl,tcStTmpl,hHook,hz,↓reduceIte] at hf
      split at hf
      · obtain rfl := hf.1
        obtain rfl := Option.some.inj hf.2
        simp [eventToken,correctionTensorOperation,pendingTokens,hHi,hc,hop,hHook,hz,
          instructionTokens]
      · cases hf.2
    · rw [eventTmpl_tcSt_afterWait hHook hz] at hf
      obtain ⟨hT,rfl⟩ := storeTokenOfCore hf
      rw [pendingOfClear (s := next { s with sub := 0 }) rfl]
      simp [hT,pendingTokens,hHi,hc,hop,hHook,hz,instructionTokens,next]
  have hOff : Assumptions.all.any (·.tcStWaitLd s.pc) = false := by simpa using hHook
  have hClear : s.sub = 0 := by simpa [ScoreScratchReady,hOff] using hS.1
  rw [eventTmpl_tcSt_noWait hOff] at hf
  obtain ⟨hT,rfl⟩ := storeTokenOfCore hf
  rw [pendingOfClear (s := next s) hClear]
  simp [hT,pendingTokens,hHi,hc,hop,hOff,hClear,instructionTokens,next]

private theorem pendingAtStoreWait {g hi : Nat} {s u : TState} {e : Event} {i : Instr}
    (hHi : s.pc < hi) (hc : kernel.code[s.pc]? = some i) (hop : i.op = .tcWaitSt)
    (hS : ScoreScratchReady i.op s)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s i.op) e (some u)) :
    pendingTokens hi s = (eventToken e).toList ++ pendingTokens hi u := by
  rw [hop] at hf hS
  obtain ⟨rfl,rfl⟩ := fires_tcWaitSt hf
  rw [pendingOfClear (s := next s) hS.1]
  simp [eventToken,correctionTensorOperation,pendingTokens,hHi,hc,hop,instructionTokens,next]

private theorem pendingAtOrdinaryEvent {g hi : Nat} {s u : TState} {e : Event} {i : Instr}
    (hHi : s.pc < hi) (hc : kernel.code[s.pc]? = some i) (hNotData : tcDataOp i.op = false)
    (hOp : scoreEventOp i.op = true) (hOrdinary : Epilogue.ordinaryEvent i.op = true)
    (hReg : 0 ∉ scoreEventWrites i.op) (hSub : s.sub ≤ 3) (hS : ScoreScratchReady i.op s)
    (he : EStep kernel Assumptions.all l g s e (some u))
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s i.op) e (some u)) :
    pendingTokens hi s = (eventToken e).toList ++ pendingTokens hi u := by
  have hNoToken : eventToken e = none := by
    have hNo : isTcData e = false := by
      cases ht : isTcData e
      · rfl
      · exact (Bool.noConfusion (hNotData.symm.trans (fires_tcData_op hf ht)))
    obtain ⟨_,kd⟩ := e
    cases kd <;> try rfl
    rename_i tc
    cases tc <;> first | rfl | cases hNo
  rw [hNoToken]
  rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOrdinary) hf with hStay | hNext
  · obtain ⟨hSrc,_⟩ := tokensAtOrdinary hHi hc hNotData
    obtain ⟨hDst,_⟩ := tokensAtOrdinary (s := u) (hStay.symm ▸ hHi) (hStay.symm ▸ hc) hNotData
    rw [hSrc,hDst,hStay]
    rfl
  · have hClear : ScoreScratchClear u := by
      have h := scoreEventScratch hc hOp hSub hReg he hS
      simpa only [hNext,Nat.succ_ne_self,↓reduceIte] using h
    rw [pendingOfClear (s := u) hClear.1,hNext]
    exact (tokensAtOrdinary hHi hc hNotData).1

private theorem pendingAtEvent {g : Nat} {s u : TState} {e : Event} (round : Softmax.Round)
    (hLo : startPc round ≤ s.pc) (hHi : s.pc < finishPc round) (hSub : s.sub ≤ 3)
    (hS : ScoreScratchState s) (he : EStep kernel Assumptions.all l g s e (some u)) :
    pendingTokens (finishPc round) s =
      (eventToken e).toList ++ pendingTokens (finishPc round) u := by
  obtain ⟨i,hc,hNonlocal,hf⟩ := estep_event_source he
  have hReady : ScoreScratchReady i.op s := by
    simpa only [ScoreScratchState,hc,hNonlocal,Bool.false_eq_true,↓reduceIte] using hS
  have ha := (Bool.and_eq_true_iff.mp (tokenWindowAudit round hLo hHi hc)).1
  unfold supportedTokenOp at ha
  split at ha
  next ds ta hop => exact pendingAtLoad hHi hc hop hReady hf
  next ta ss hop => exact pendingAtStore hHi hc hop hReady hf
  next hop => exact pendingAtStoreWait hHi hc hop hReady hf
  next =>
    simp only [hNonlocal,Bool.false_or,Bool.and_eq_true,Bool.not_eq_true'] at ha
    have hR : 0 ∉ scoreEventWrites i.op := by
      intro hm
      have hYes : (scoreEventWrites i.op).contains 0 = true := List.contains_iff_mem.mpr hm
      exact Bool.noConfusion (hYes.symm.trans ha.2.1.2)
    exact pendingAtOrdinaryEvent hHi hc ha.1 ha.2.1.1 ha.2.2 hR hSub hReady he hf

private theorem localHasNoTensor {o : Op} (h : o.isLocal = true) : tcDataOp o = false := by
  cases o <;> simp_all [Op.isLocal,tcDataOp]

private theorem skipHasNoTensor {i : Instr} {s : TState} (ha : supportedTokenOp i = true)
    (hs : guardHolds s i.guard = .ok false) : tcDataOp i.op = false := by
  have hNone : i.guard ≠ none := by rintro hg; simp [hg,guardHolds,pure,Except.pure] at hs
  unfold supportedTokenOp at ha
  split at ha
  · simp [Option.isNone_iff_eq_none,hNone] at ha
  · simp [Option.isNone_iff_eq_none,hNone] at ha
  · simp [Option.isNone_iff_eq_none,hNone] at ha
  · exact by simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp ha).1

private def segmentKeepsTokens (round : Softmax.Round) (pc : Nat) : Bool :=
  if startPc round ≤ pc ∧ pc < finishPc round then
    match cuteExp2.matchAt kernel pc with
    | some m => decide (tokenSlice (finishPc round) pc = tokenSlice (finishPc round) m.stop)
    | none => false
  else true

set_option maxRecDepth 100000 in
private theorem segmentTokenFrame (round : Softmax.Round) {pc : Nat} {m : SegMatch CuteSlot}
    (hLo : startPc round ≤ pc) (hHi : pc < finishPc round)
    (hs : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some m) :
    tokenSlice (finishPc round) pc = tokenSlice (finishPc round) m.stop := by
  have hAll : Assumptions.swExp2Sites.all (segmentKeepsTokens round) = true :=
    by cases round <;> decide +kernel
  have h := List.all_eq_true.mp hAll pc hs
  unfold segmentKeepsTokens at h
  rw [ite_eq_left ⟨hLo,hHi⟩,hm] at h
  exact of_decide_eq_true h

private theorem pendingAtLocal {g : Nat} {s u : TState} (round : Softmax.Round)
    (hLo : startPc round ≤ s.pc) (hHi : s.pc < finishPc round) (hS : ScoreScratchState s)
    (ht : Tau kernel Assumptions.all l g s u) :
    pendingTokens (finishPc round) s = pendingTokens (finishPc round) u := by
  obtain ⟨i,hc,_,hExec⟩ := tauScoreSource ht
  have ha := Bool.and_eq_true_iff.mp (tokenWindowAudit round hLo hHi hc)
  rcases hExec with ⟨rfl,hSkip⟩ | ⟨_,hLocal,hExec⟩
  · rw [pendingOfClear (show (skip s).sub = 0 from rfl)]
    exact (tokensAtOrdinary hHi hc (skipHasNoTensor ha.1 hSkip)).1
  have ⟨hZero,_⟩ := scratchClearOfLocal hc hLocal hS
  have hBody := tokensAtOrdinary hHi hc (localHasNoTensor hLocal)
  rcases scoreExecLocal hExec with hFrame | ⟨m,hMark,hMatch,hRun⟩
  · rw [pendingOfClear (s := u) (hFrame.sub.trans hZero)]
    have hPc := hFrame.pc
    cases hop : i.op <;> simp only [hop,nextPc,BrxTarget,or_false] at hPc
    case bra dest uni =>
      have hJump : startPc round ≤ dest ∧ dest ≤ finishPc round ∧
          tokenSlice (finishPc round) s.pc = tokenSlice (finishPc round) dest := by
        simpa only [hop,tokenJump,decide_eq_true_eq] using ha.2
      rw [hPc]
      exact hBody.2.symm.trans hJump.2.2
    case brx => simp [hop,tokenJump] at ha
    all_goals rw [hPc]; exact hBody.1
  · obtain ⟨hPc,hSub,_,_⟩ := scoreSegmentFrame hRun
    rw [pendingOfClear (s := u) hSub,hPc]
    exact hBody.2.symm.trans (segmentTokenFrame round hLo hHi hMark hMatch)

/-- The Tensor Memory events, including each implicit wait at its decoded source position. -/
@[no_expose] def softmaxTraceTokens (events : List Event) : List (Nat × Fin 4) :=
  events.filterMap eventToken

private def EnteredWindow (round : Softmax.Round) (entry s : TState) : Prop :=
  startPc round ≤ s.pc ∧ s.pc ≤ finishPc round ∧ s.sub ≤ 3 ∧ ScoreScratchState s ∧
    (s.pc = finishPc round → s.fault = none) ∧
    ∀ r ∈ (windowSite (softWindow round)).keeps, s.regs r = entry.regs r

private theorem roundReturns (round : Softmax.Round) {l : Launch} {g : Nat} {s u entry : TState}
    {ev : Option Event} (hs : EnteredWindow round entry s)
    (hn : s.pc ≠ finishPc round) (hStep : WStep kernel Assumptions.all l g s ev u) :
    EnteredWindow round entry u ∧ pendingTokens (finishPc round) s =
      (ev.bind eventToken).toList ++ pendingTokens (finishPc round) u := by
  obtain ⟨hLo,hHi,hSub,hScratch,_,hRegs⟩ := hs
  have hLt : s.pc < finishPc round := by omega
  obtain ⟨hL,hH,hS,hF,hR⟩ := windowStepFrame (softWindow round) hLo hLt hSub hStep
  have hEmpty : (windowSite (softWindow round)).exits = [] := by cases round <;> rfl
  simp only [hEmpty,List.not_mem_nil,or_false] at hH
  refine ⟨⟨hL,hH,hS,windowStepScratch _ hLo hLt hSub hStep hScratch,?_,?_⟩,?_⟩
  · intro hu
    exact hF.resolve_right (fun h => hn (h.symm.trans hu))
  · exact fun r hr => (hR r hr).trans (hRegs r hr)
  · rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
    · exact pendingAtLocal round hLo hLt hScratch ht
    · exact pendingAtEvent round hLo hLt hSub hScratch he

private theorem cutSoftmaxVisit {g : Nat} {s entry : TState} {events : List Event}
    {visits : List Visit} {target : Event} (round : Softmax.Round)
    (hw : Walk kernel Assumptions.all l g s events visits) (hs : EnteredWindow round entry s)
    (hMem : target ∈ events) (hLate : finishPc round ≤ target.pc) :
    ∃ u pre tail rest, events = pre ++ tail ∧ u.pc = finishPc round ∧
      EnteredWindow round entry u ∧ softmaxTraceTokens pre = pendingTokens (finishPc round) s ∧
      target ∈ tail ∧ Walk kernel Assumptions.all l g u tail rest := by
  have hCut {t : TState} {es : List Event} {vs : List Visit} (hp : t.pc = finishPc round)
      (ht : EnteredWindow round entry t) (hm : target ∈ es)
      (hw : Walk kernel Assumptions.all l g t es vs) :
      ∃ u pre tail rest, es = pre ++ tail ∧ u.pc = finishPc round ∧
        EnteredWindow round entry u ∧ softmaxTraceTokens pre = pendingTokens (finishPc round) t ∧
        target ∈ tail ∧ Walk kernel Assumptions.all l g u tail rest :=
    ⟨t,[],es,vs,rfl,hp,ht,by simp [softmaxTraceTokens,pendingTokens,hp],hm,hw⟩
  induction hw with
  | stop => cases hMem
  | @tau t u fs vs ht hw ih =>
    by_cases hp : t.pc = finishPc round
    · exact hCut hp hs hMem (.tau ht hw)
    obtain ⟨hu,hPending⟩ := roundReturns round hs hp (.inl ⟨rfl,ht⟩)
    rw [hPending]
    exact ih hu hMem
  | @ev t u e fs vs he hw ih =>
    by_cases hp : t.pc = finishPc round
    · exact hCut hp hs hMem (.ev he hw)
    obtain ⟨hu,hPending⟩ := roundReturns round hs hp (.inr ⟨e,rfl,he⟩)
    have hNe : target ≠ e := by
      intro h
      have hPc := estep_source_pc he
      have hEnd := hs.2.1
      rw [h] at hLate
      omega
    obtain ⟨out,pre,tail,rest,hE,hP,hO,hPlan,hTail,hWalk⟩ :=
      ih hu ((List.mem_cons.mp hMem).resolve_left hNe)
    refine ⟨out,e::pre,tail,rest,by rw [hE,List.cons_append],hP,hO,?_,hTail,hWalk⟩
    rw [hPending, ← hPlan]
    cases hT : eventToken e <;> simp [hT,softmaxTraceTokens]
  | @last t e he =>
    by_cases hp : t.pc = finishPc round
    · exact hCut hp hs hMem (.last he)
    obtain rfl := List.mem_singleton.mp hMem
    have hPc := estep_source_pc he
    have hEnd := hs.2.1
    omega

/-- Every actual completed softmax visit emits its decoded Tensor Memory token sequence
in order. The next role checkpoint retains the precise loop-counter frame. -/
private theorem softmaxVisitTraceDecompose {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {target : Event} (round : Softmax.Round)
    (hw : Walk kernel Assumptions.all l g s events visits) (hPc : s.pc = startPc round)
    (hScratch : ScoreScratchClear s) (hFault : s.fault = none) (hMem : target ∈ events)
    (hLate : finishPc round ≤ target.pc) :
    ∃ u pre tail rest, events = pre ++ tail ∧ u.pc = finishPc round ∧ u.fault = none ∧
      ScoreScratchState u ∧
      (∀ r ∈ (windowSite (softWindow round)).keeps, u.regs r = s.regs r) ∧
      softmaxTraceTokens pre = softmaxVisitTokens round ∧
      target ∈ tail ∧ Walk kernel Assumptions.all l g u tail rest := by
  have hHi : s.pc ≤ finishPc round := by rw [hPc]; cases round <;> decide
  have hSub : s.sub ≤ 3 := by rw [hScratch.1]; decide
  have hFrame : EnteredWindow round s s :=
    ⟨hPc.ge,hHi,hSub,scratchStateOfClear hScratch,fun _ => hFault,fun _ _ => rfl⟩
  obtain ⟨u,pre,tail,rest,hSplit,hU,hs,hPlan,hTail,hWalk⟩ :=
    cutSoftmaxVisit round hw hFrame hMem hLate
  have hLabels := hPlan.trans (pendingOfClear hScratch.1)
  rw [hPc, softmaxVisitTokenTable round] at hLabels
  exact ⟨u,pre,tail,rest,hSplit,hU,hs.2.2.2.2.1 hU,hs.2.2.2.1,hs.2.2.2.2.2,
    hLabels,hTail,hWalk⟩

theorem softmaxTraceTokensAppend (left right : List Event) :
    softmaxTraceTokens (left ++ right) = softmaxTraceTokens left ++ softmaxTraceTokens right :=
  List.filterMap_append

private theorem softmaxEventTokenSome {e : Event} :
    (eventToken e).isSome = isTcData e := by
  rcases e with ⟨p,kind⟩
  cases kind <;> try rfl
  rename_i tc
  cases tc <;> rfl

theorem softmaxTraceTokensNone {events : List Event}
    (h : ∀ e ∈ events, isTcData e = false) : softmaxTraceTokens events = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  cases hx : eventToken e with
  | none => rfl
  | some _ => have hh := softmaxEventTokenSome (e := e); simp [hx, h e he] at hh

/-- Under actual softmax event classification, selects the exact site and operation at
the ordinal counted by the execution's Tensor Memory collective predicate. -/
theorem softmaxTraceTokensAt {events : List Event} {i k : Nat} {e : Event}
    (hClass : ∀ x ∈ events, isTcColl x = isTcData x)
    (he : events[i]? = some e) (hColl : isTcColl e = true)
    (hOrd : (events.take i).countP isTcColl = k) :
    ∃ op, correctionTensorOperation e.kind = some op ∧
      (softmaxTraceTokens events)[k]? = some (e.pc, op) := by
  have hData := hColl.symm.trans (hClass e (List.mem_of_getElem? he))
  have hSome : (correctionTensorOperation e.kind).isSome = true := by
    have h := softmaxEventTokenSome (e := e)
    rw [← hData] at h
    simpa [eventToken] using h
  obtain ⟨op,hOp⟩ := Option.isSome_iff_exists.mp hSome
  refine ⟨op,hOp,?_⟩
  rw [← hOrd]
  have hLabel : eventToken e = some (e.pc,op) := by simp [eventToken,hOp]
  clear hOrd k hData hSome hColl hOp
  unfold softmaxTraceTokens
  induction events generalizing i with
  | nil => simp at he
  | cons x xs ih =>
    cases i with
    | zero =>
      have := Option.some.inj he
      subst e
      simp [hLabel]
    | succ i =>
      have hTail (y : Event) (hy : y ∈ xs) := hClass y (List.mem_cons_of_mem _ hy)
      have hNext := ih hTail (by simpa using he)
      cases hHead : eventToken x with
      | none =>
        have hNo : isTcColl x = false := by
          rw [hClass x List.mem_cons_self, ← softmaxEventTokenSome, hHead]
          rfl
        simpa [hHead,hNo] using hNext
      | some label =>
        have hYes : isTcColl x = true := by
          rw [hClass x List.mem_cons_self, ← softmaxEventTokenSome, hHead]
          rfl
        simpa [hHead,hYes] using hNext

theorem softmaxTraceTokensCount {events : List Event}
    (hClass : ∀ x ∈ events, isTcColl x = isTcData x) :
    (softmaxTraceTokens events).length = events.countP isTcColl := by
  unfold softmaxTraceTokens
  rw [List.length_filterMap_eq_countP]
  apply List.countP_congr
  intro e he
  exact Bool.eq_iff_iff.mp (softmaxEventTokenSome.trans (hClass e he).symm)

/-- The first visit emits the decoded Tensor Memory sequence and keeps the integer geometry
that determines the two repeated visits. -/
theorem softmaxFirstTensorTrace {g blocks cap past : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {target : Event} (hs : At s 3425 (firstLoopGeometry blocks cap past))
    (hw : Walk kernel Assumptions.all l g s events visits) (hTarget : target ∈ events)
    (hLate : 5006 ≤ target.pc) :
    ∃ u pre tail rest, events = pre ++ tail ∧
      At u 5006 (firstLoopGeometry blocks cap past) ∧
      softmaxTraceTokens pre = softmaxVisitTokens .first ∧
      target ∈ tail ∧ Walk kernel Assumptions.all l g u tail rest := by
  obtain ⟨u,pre,tail,rest,hSplit,hU,hF,hScratch,hRegs,hTokens,hMem,hWalk⟩ :=
    softmaxVisitTraceDecompose .first hw hs.1 ⟨hs.2.1,hs.2.2.1⟩ hs.2.2.2.1 hTarget hLate
  change u.pc = 5006 at hU
  have hClear := scratchClearOfLocal (hU.symm ▸ Flow.code_5006) rfl hScratch
  refine ⟨u,pre,tail,rest,hSplit,⟨hU,hClear.1,hClear.2,hF,?_⟩,hTokens,hMem,hWalk⟩
  exact Epilogue.holdsSchedulerFrame hs.2.2.2.2 hRegs (fun _ hr => by
    simpa [firstLoopGeometry,softWindow,windowSite] using List.mem_map_of_mem (f := Prod.fst) hr)

@[no_expose] def softmaxLoopRound : ScoreLoop → Softmax.Round
  | .biased => .biased
  | .plain => .unbiased

private theorem loopTokenStart (loop : ScoreLoop) :
    startPc (softmaxLoopRound loop) = (scoreLoopSite loop).head := by cases loop <;> rfl

private theorem loopTokenStop (loop : ScoreLoop) :
    finishPc (softmaxLoopRound loop) = (scoreLoopSite loop).increment := by cases loop <;> rfl

theorem softmaxScratchAcrossSilent {g : Nat} {s u : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) (hs : ScoreScratchState s)
    : ScoreScratchState u := by
  induction h with
  | refl => exact hs
  | tail _ ht ih => exact scoreScratchTau ht ih

theorem softmaxScratchAtLoopHead (loop : ScoreLoop) {s : TState}
    (hp : s.pc = (scoreLoopSite loop).head) (hs : ScoreScratchState s) : ScoreScratchClear s := by
  cases loop
  · change s.pc = 5032 at hp
    exact scratchClearOfLocal (hp.symm ▸ Flow.code_5032) rfl hs
  · change s.pc = 6661 at hp
    exact scratchClearOfLocal (hp.symm ▸ Flow.code_6661) rfl hs

theorem softmaxHealthyBeforeLaterTarget {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} {target : Event} (hw : Walk kernel Assumptions.all l g s events visits)
    (hm : target ∈ events) (hPc : s.pc < target.pc) : s.fault = none := by
  cases hf : s.fault with
  | none => rfl
  | some f =>
    have hOut : out kernel Assumptions.all l g s = .ev (.ub f) := by simp [out,hf]
    cases hw with
    | stop => cases hm
    | tau ht _ => cases hOut.symm.trans ht
    | ev he _ =>
      obtain ⟨_,h,hF⟩ := he
      obtain rfl := Out.ev.inj (hOut.symm.trans h)
      cases hF.2
    | last he =>
      obtain rfl := List.mem_singleton.mp hm
      have h := estep_source_pc he
      omega

/-- A complete repeated softmax loop emits the actual per-visit Tensor Memory tokens
exactly as many times as indicated by its initialized loop counter. -/
theorem softmaxRepeatedTensorTrace {g w : Nat} {s : TState} (loop : ScoreLoop) {events : List Event}
    {visits : List Visit} {target : Event} (hw : Walk kernel Assumptions.all l g s events visits)
    (hPc : s.pc = (scoreLoopSite loop).head) (hScratch : ScoreScratchClear s)
    (hFault : s.fault = none) (hWord : s.regs (scoreLoopSite loop).word = some (b32 w))
    (hW : w < 2^32) (hTarget : target ∈ events)
    (hLate : (scoreLoopSite loop).increment+4 ≤ target.pc) :
    ∃ u pre tail rest, events = pre ++ tail ∧ u.pc = (scoreLoopSite loop).increment+4 ∧
      u.sub = 0 ∧ u.acc = [] ∧ u.fault = none ∧
      (∀ r ∈ [1229,1359], u.regs r = s.regs r) ∧
      softmaxTraceTokens pre =
        (List.replicate (scoreLoopDistance loop w)
          (softmaxVisitTokens (softmaxLoopRound loop))).flatten ∧
      target ∈ tail ∧ Walk kernel Assumptions.all l g u tail rest := by
  generalize hDistance : scoreLoopDistance loop w = n
  induction n using Nat.strong_induction_on generalizing s w events visits with
  | h n ih =>
    let round := softmaxLoopRound loop
    have hStart : s.pc = startPc round := hPc.trans (loopTokenStart loop).symm
    have hLimit : finishPc round ≤ target.pc := by
      rw [show finishPc round = (scoreLoopSite loop).increment from loopTokenStop loop]
      omega
    obtain ⟨v,pre,tail,rest,hSplit,hV,hVF,hVS,hRegs,hTokens,hMem,hWalk⟩ :=
      softmaxVisitTraceDecompose round hw hStart hScratch hFault hTarget hLimit
    have hInc : v.pc = (scoreLoopSite loop).increment := hV.trans (loopTokenStop loop)
    have hKeepWord : (scoreLoopSite loop).word ∈ (windowSite (softWindow round)).keeps := by
      cases loop <;> decide
    obtain ⟨q,hRun,hQ,hQSub,_,hQWord,hPred,hKeep⟩ :=
      scoreLoopTestActualFrame loop hW hVF hInc ((hRegs _ hKeepWord).trans hWord)
    rcases Mma.advanceWalkLocals hRun hWalk with rfl | ⟨_,_,_,hQWalk⟩
    · cases hMem
    obtain ⟨u,vs,hU,hSub,hUWord,hURegs,hClean,hSteps,hUWalk⟩ :=
      scoreTailForLaterEvent loop hQ hPred hQWalk hMem hLate
    have hSameRegs (r : Nat) (hr : r ∈ [1229,1359]) : u.regs r = s.regs r := by
      have hCutReg : r ∈ (windowSite (softWindow round)).keeps := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> cases loop <;> decide
      have hQReg : q.regs r = v.regs r := by
        apply hKeep <;> (
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl <;> cases loop <;> decide)
      exact (hURegs r hr).trans (hQReg.trans (hRegs r hCutReg))
    let w' := (w+1)%2^32
    change u.pc = (if decide (w' ≠ (scoreLoopSite loop).sentinel) then
      (scoreLoopSite loop).head else (scoreLoopSite loop).increment + 4) at hU
    by_cases hNext : w' ≠ (scoreLoopSite loop).sentinel
    · have hBack : u.pc = (scoreLoopSite loop).head := by
        simpa only [decide_eq_true hNext,↓reduceIte] using hU
      have hProtected : u.fault = none := by
        apply softmaxHealthyBeforeLaterTarget hUWalk hMem
        have hB : (scoreLoopSite loop).head < (scoreLoopSite loop).increment+4 := by
          cases loop <;> decide
        exact hBack.symm ▸ hB.trans_le hLate
      have hUScratch := softmaxScratchAtLoopHead loop hBack
        (softmaxScratchAcrossSilent hSteps (softmaxScratchAcrossSilent (run_rtg hRun) hVS))
      have hDist := (scoreLoopDistance_step loop hW hNext).trans hDistance
      change scoreLoopDistance loop w' + 1 = n at hDist
      obtain ⟨out,mid,after,path,hTailSplit,hFinal,hS,hA,hF,hRet,hMid,hAfter,hOut⟩ :=
        ih (scoreLoopDistance loop w') (by omega) hUWalk hBack hUScratch hProtected
          (hUWord.trans hQWord) (Nat.mod_lt _ (by decide)) hMem rfl
      refine ⟨out,pre++mid,after,path,by rw [hSplit,hTailSplit,List.append_assoc],
        hFinal,hS,hA,hF,fun r hr => (hRet r hr).trans (hSameRegs r hr),?_,hAfter,hOut⟩
      rw [softmaxTraceTokensAppend,hTokens,hMid,← hDist,List.replicate_succ,List.flatten_cons]
    · have hFinish : u.pc = (scoreLoopSite loop).increment + 4 := by
        simpa only [decide_eq_false hNext,Bool.false_eq_true,↓reduceIte] using hU
      have hDist := (distanceOnExit loop hW (not_ne_iff.mp hNext))
      have hn : n = 1 := hDistance.symm.trans hDist
      obtain ⟨hs,ha,hf⟩ := hClean (decide_eq_false hNext)
      refine ⟨u,pre,tail,vs,hSplit,hFinish,hs,ha,hf,hSameRegs,?_,hMem,hUWalk⟩
      simpa [hn] using hTokens

end
end PTX.Kernels.TmlFa4Fwd.Thread
