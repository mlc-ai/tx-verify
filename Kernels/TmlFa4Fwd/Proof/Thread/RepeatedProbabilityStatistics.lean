-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleStatisticsPublication
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedExponent
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Flow.Code.Part101

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Softmax

private def repeatedNoticePc (biased : Bool) : Nat := if biased then 5683 else 6891

private def postStatistics (biased : Bool) (site : Nat) : Prop :=
  repeatedNoticePc biased < site ∧ site ≤ Softmax.probabilityPc (Softmax.rescaleRound biased) 3

private instance (biased : Bool) (site : Nat) : Decidable (postStatistics biased site) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def statisticsIngress (biased : Bool) (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || Epilogue.ordinaryEvent i.op) &&
    match i.op with
    | .bra dst _ => !decide (postStatistics biased dst) || decide (postStatistics biased pc)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem statisticsIngressAudit (biased : Bool) :
    ((((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103)).all
      (fun (i,pc) => statisticsIngress biased pc i) = true := by
  cases biased <;> kernel_rfl

private theorem statisticsIngressAt (biased : Bool) {site : Nat} {i : Instr}
    (hLo : 3103 ≤ site) (hHi : site < 7742) (hCode : kernel.code[site]? = some i) :
    statisticsIngress biased site i = true := by
  apply List.all_eq_true.mp (statisticsIngressAudit biased) (i,site)
  apply List.mem_of_getElem? (i := site-3103)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hCode]
  rfl

private theorem repeatedNoticeCode (biased : Bool) :
    kernel.code[repeatedNoticePc biased]? =
      some ⟨none,.barArrive (.reg 5127) (.imm 64) true⟩ := by
  cases biased
  · exact Flow.code_6891
  · exact Flow.code_5683

section
variable {l : Launch}

private theorem noticeKindAt {g : Nat} {s u : TState} {e : Event} (biased : Bool)
    (hAt : s.pc = repeatedNoticePc biased) (he : EStep kernel Assumptions.all l g s e (some u)) :
    notice e = some (rescalePublication biased) := by
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  rw [hAt,repeatedNoticeCode biased] at hCode
  obtain rfl := Option.some.inj hCode
  have hSite : e.pc = repeatedNoticePc biased := (estep_source_pc he).trans hAt
  have hKind : ∃ id count, e.kind = .bar id count .arrive := by
    change Fires s.pc (barTmpl l g s (.reg 5127) (some (.imm 64)) .arrive) e (some u)
      at hFire
    unfold barTmpl at hFire
    repeat' split at hFire
    all_goals first | exact ⟨_,_,congrArg Event.kind hFire.1⟩ | cases hFire.2
  obtain ⟨id,count,hKind⟩ := hKind
  unfold notice
  rw [hKind,hSite]
  cases biased <;> rfl

private def plainProbabilityProgress (pc : Nat) : Nat :=
  if pc ≤ 6891 then 0 else if pc ≤ 7416 then 1 else if pc ≤ 7425 then 2
  else if pc ≤ 7434 then 3 else if pc ≤ 7435 then 4 else if pc ≤ 7437 then 5
  else if pc ≤ 7446 then 6 else 7

private def plainProbabilityEvent : Op → Bool
  | .barArrive .. | .tcSt _ _ .s32x32b | .tcWaitSt | .mbarArrive .. => true
  | _ => false

private def plainProbabilityControl (pc : Nat) (ins : Instr) : Bool :=
  (if postStatistics false pc ∨ postStatistics false (pc+1) then
    (ins.op.isLocal || (ins.guard.isNone && plainProbabilityEvent ins.op)) &&
      decide (plainProbabilityProgress (pc+1) =
        plainProbabilityProgress pc + if ins.op.isLocal then 0 else 1)
   else true) &&
  match ins.op with
  | .bra target _ =>
    if postStatistics false target then
      decide (postStatistics false pc ∧
        plainProbabilityProgress target = plainProbabilityProgress pc)
    else true
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem plainProbabilityControlAudit :
    (((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103).all
      (fun (ins,pc) => plainProbabilityControl pc ins) = true := by kernel_rfl

private theorem plainProbabilityControlAt {pc : Nat} {ins : Instr}
    (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hc : kernel.code[pc]? = some ins) :
    plainProbabilityControl pc ins = true := by
  apply List.all_eq_true.mp plainProbabilityControlAudit (ins,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

set_option maxRecDepth 100000 in
private theorem plainProbabilitySegmentAudit :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | none => false
      | some seg => if postStatistics false seg.stop then
          decide (postStatistics false pc ∧
            plainProbabilityProgress seg.stop = plainProbabilityProgress pc)
        else true) = true := by kernel_rfl

private theorem plainProbabilityWindow {pc : Nat}
    (h : postStatistics false pc ∨ postStatistics false (pc+1)) : 6891 ≤ pc := by
  change (6891 < pc ∧ _) ∨ (6891 < pc+1 ∧ _) at h
  omega

private theorem probabilityCoreStoreNext {g : Nat} {s u : TState} {e : Event} {dst : Nat}
    {src : List Opnd} (hf : Fires s.pc (tcTmpl l g s (.tcSt dst src .s32x32b)) e (some u)) :
    u.pc = s.pc+1 := by
  rw [tcTmpl_tcSt_plain (by intro _ h; cases h)] at hf
  cases hAddr : readBits l g s 32 (.reg dst) <;>
    cases hVals : src.mapM (readValue l g s 32) <;>
    simp only [ofExec,hAddr,hVals,bind,Except.bind,pure,Except.pure,throw,throwThe,
      MonadExceptOf.throw] at hf
  all_goals split_ifs at hf <;> simp only [Fires, reduceCtorEq] at hf
  all_goals try (cases hf.2)
  exact congrArg TState.pc (Option.some.inj hf.2)

private theorem probabilityEventNext {g : Nat} {s u : TState} {e : Event} {op : Op}
    (hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = false)
    (hOp : plainProbabilityEvent op = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s op) e (some u)) :
    u.pc = s.pc+1 := by
  cases op <;> simp only [plainProbabilityEvent, Bool.false_eq_true] at hOp
  case barArrive a n aligned =>
    simp only [eventTmpl] at hf
    unfold barTmpl at hf
    repeat' split at hf
    all_goals first | exact congrArg TState.pc (Option.some.inj hf.2) | cases hf.2
  case mbarArrive base off tx count cluster release scope dest =>
    cases dest <;> exact congrArg TState.pc (fires_arrive_state hf).1
  case tcWaitSt => exact congrArg TState.pc (fires_tcWaitSt hf).1
  case tcSt dst src shape =>
    have hShape : shape = .s32x32b := by cases shape <;> simp_all
    subst shape
    rw [eventTmpl_tcSt_noWait hHook] at hf
    exact probabilityCoreStoreNext hf

private theorem plainProbabilityNext {g : Nat} {s u : TState} {e : Event} {op : Op}
    (hs : 6891 ≤ s.pc) (hOp : plainProbabilityEvent op = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s op) e (some u)) :
    u.pc = s.pc+1 := by
  apply probabilityEventNext (op := op) ?_ hOp hf
  rw [Assumptions.all_tcStWaitLd]
  have hAll : Assumptions.delayedTmemSites.all (fun pc => decide (pc < 6891)) = true := by decide
  by_contra! h
  have hMem : s.pc ∈ Assumptions.delayedTmemSites := by simpa using h
  have hBound := of_decide_eq_true (List.all_eq_true.mp hAll _ hMem)
  omega

private def PlainStatisticsClock (X : Execution) (g index : Nat) (s : TState) : Prop :=
  postStatistics false s.pc →
    ∃ prior, Publishes X (g,prior) .plain ∧ index = prior+plainProbabilityProgress s.pc

private theorem plainStatisticsClockStep {X : Execution} {g index : Nat} {s u : TState}
    {event : Option Event} (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742)
    (hSeen : PlainStatisticsClock X g index s) (hStep : WStep kernel Assumptions.all l g s event u)
    (hGet : ∀ e, event = some e → X.get (g,index) = some e) :
    PlainStatisticsClock X g (index+event.toList.length) u := by
  intro hNew
  have keep (hOld : postStatistics false s.pc)
      (hProgress : plainProbabilityProgress u.pc =
        plainProbabilityProgress s.pc+event.toList.length) :
      ∃ prior, Publishes X (g,prior) .plain ∧
        index+event.toList.length = prior+plainProbabilityProgress u.pc := by
    obtain ⟨prior,hNotice,hEq⟩ := hSeen hOld
    exact ⟨prior,hNotice,by omega⟩
  have beforeNext (hPc : u.pc = s.pc+1) :
      postStatistics false s.pc ∨ s.pc = repeatedNoticePc false := by
    unfold postStatistics at *
    exact or_iff_not_imp_right.mpr (fun h => ⟨by omega,by omega⟩)
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · obtain ⟨ins,hCode,_,hLocal⟩ := Softmax.tauScoreSource hTau
    have hLocalOpcode (hCase : postStatistics false s.pc ∨ postStatistics false (s.pc+1)) :
        ins.op.isLocal = true := by
      have hTest := (Bool.and_eq_true_iff.mp (plainProbabilityControlAt hLo hHi hCode)).1
      rw [ite_eq_left hCase,Bool.and_eq_true,Bool.or_eq_true] at hTest
      rcases hTest.1 with hYes | hNonlocal
      · exact hYes
      · have hGuard := Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp hNonlocal).1
        rcases hLocal with ⟨_,hSkip⟩ | ⟨_,hYes,_⟩
        · rw [hGuard] at hSkip
          cases hSkip
        · exact hYes
    have fall (hPc : u.pc = s.pc+1) :
        ∃ prior, Publishes X (g,prior) .plain ∧ index = prior+plainProbabilityProgress u.pc := by
      have hCase := hPc ▸ hNew
      have hOp := hLocalOpcode (.inr hCase)
      have hNo : s.pc ≠ repeatedNoticePc false := by
        intro hNotice
        rw [hNotice,repeatedNoticeCode false] at hCode
        obtain rfl := Option.some.inj hCode
        cases hOp
      have hTest := (Bool.and_eq_true_iff.mp (plainProbabilityControlAt hLo hHi hCode)).1
      rw [ite_eq_left (Or.inr hCase),Bool.and_eq_true,hOp,ite_eq_left rfl,
        decide_eq_true_eq] at hTest
      exact keep ((beforeNext hPc).resolve_right hNo) (by rw [hPc]; exact hTest.2)
    rcases hLocal with ⟨rfl,_⟩ | ⟨_,_,hExec⟩
    · exact fall rfl
    rcases Softmax.scoreExecLocal hExec with hFrame | ⟨seg,hSite,hMatch,hResult⟩
    · have hChecked := plainProbabilityControlAt hLo hHi hCode
      unfold plainProbabilityControl at hChecked
      have hBranch := (Bool.and_eq_true_iff.mp hChecked).2
      have hPc := hFrame.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra dst uniform =>
        have h := hPc ▸ hNew
        rw [hOp] at hBranch
        change (if postStatistics false dst then decide (postStatistics false s.pc ∧
          plainProbabilityProgress dst = plainProbabilityProgress s.pc) else true) = true at hBranch
        rw [ite_eq_left h,decide_eq_true_eq] at hBranch
        exact keep hBranch.1 (hPc.symm ▸ hBranch.2)
      case brx => simp [hOp] at hBranch
      all_goals exact fall hPc
    · have hPc := (Softmax.scoreSegmentFrame hResult).1
      have h := List.all_eq_true.mp plainProbabilitySegmentAudit _ hSite
      rw [hMatch] at h
      change (if postStatistics false seg.stop then decide (postStatistics false s.pc ∧
        plainProbabilityProgress seg.stop = plainProbabilityProgress s.pc) else true) = true at h
      rw [ite_eq_left (hPc ▸ hNew),decide_eq_true_eq] at h
      exact keep h.1 (hPc.symm ▸ h.2)
  · obtain ⟨ins,hCode,hNonlocal,hFire⟩ := estep_event_source hEvent
    have hAudit := (Bool.and_eq_true_iff.mp (statisticsIngressAt false hLo hHi hCode)).1
    have hOrd : Epilogue.ordinaryEvent ins.op = true := by simpa [hNonlocal] using hAudit
    have hCase : postStatistics false s.pc ∨ postStatistics false (s.pc+1) := by
      rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOrd) hFire with h | h
      · exact .inl (h ▸ hNew)
      · exact .inr (h ▸ hNew)
    have hTest := (Bool.and_eq_true_iff.mp (plainProbabilityControlAt hLo hHi hCode)).1
    rw [ite_eq_left hCase,Bool.and_eq_true,hNonlocal,Bool.false_or,ite_eq_right (by decide),
      decide_eq_true_eq] at hTest
    have hPc := plainProbabilityNext (plainProbabilityWindow hCase)
      (Bool.and_eq_true_iff.mp hTest.1).2 hFire
    rcases beforeNext hPc with hOld | hNotice
    · exact keep hOld (by rw [hPc]; exact hTest.2)
    refine ⟨index,⟨e,hGet e rfl,noticeKindAt false hNotice hEvent⟩,?_⟩
    rw [hPc,hNotice]
    rfl

/-- The selected plain quarter has the expected event offset from its same-visit
coefficient write, including the explicit wait and credit before the tail quarter. -/
theorem plainProbabilityCoefficientPosition {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (q : Fin 4) {g store address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get (g,store) =
      some ⟨Softmax.probabilityPc .unbiased q,.tc (.st address vals shape)⟩) :
    ∃ pos a data, StatisticsStore X (g,pos) (Softmax.rescaleStore false) a data ∧
      store = pos+2+Softmax.Repeated.unbiased.probabilityStoreOffset q := by
  have hBounds : 3420 ≤ Softmax.probabilityPc .unbiased q ∧
      Softmax.probabilityPc .unbiased q < 7742 ∧
      postStatistics false (Softmax.probabilityPc .unbiased q) := by fin_cases q <;> decide
  have hStart : ¬ postStatistics false 3103 := by decide
  obtain ⟨s,_,hSeen,hStep⟩ := Softmax.softmaxRoleReplayAt hp hX he hBounds.1 hBounds.2.1
    (PlainStatisticsClock X g) (fun _ _ _ hAt hIn => (hStart (hAt.1 ▸ hIn)).elim)
    (fun hLo hHi _ hPrior hStep hGet => plainStatisticsClockStep hLo hHi hPrior hStep hGet)
  obtain ⟨prior,hNotice,hRank⟩ := hSeen ((estep_source_pc hStep) ▸ hBounds.2.2)
  have hProg : plainProbabilityProgress (Softmax.probabilityPc .unbiased q) =
      1+Softmax.Repeated.unbiased.probabilityStoreOffset q := by fin_cases q <;> decide
  rw [← estep_source_pc hStep,hProg] at hRank
  obtain ⟨pos,a,data,hPos,hStore,_⟩ := rescaleStoreBeforePublication hX false hNotice
  exact ⟨pos,a,data,hStore,by omega⟩

private def biasedProbabilityProgress (pc : Nat) : Nat :=
  if pc ≤ 5683 then 0 else if pc ≤ 6508 then 1 else if pc ≤ 6517 then 3
  else if pc ≤ 6526 then 4 else if pc ≤ 6527 then 5 else if pc ≤ 6532 then 6
  else if pc ≤ 6541 then 7 else 8

private def biasedProbabilityClock (s : TState) : Nat :=
  biasedProbabilityProgress s.pc + if s.pc = 6508 ∧ s.sub ≠ 0 then 1 else 0

private def biasedProbabilityControl (pc : Nat) (ins : Instr) : Bool :=
  (if postStatistics true pc ∨ postStatistics true (pc+1) then
    (ins.op.isLocal || (ins.guard.isNone && plainProbabilityEvent ins.op)) &&
      decide (biasedProbabilityProgress (pc+1) = biasedProbabilityProgress pc +
        if ins.op.isLocal then 0 else if pc = 6508 then 2 else 1)
   else true) &&
  match ins.op with
  | .bra target _ =>
    if postStatistics true target then
      decide (postStatistics true pc ∧
        biasedProbabilityProgress target = biasedProbabilityProgress pc)
    else true
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem biasedProbabilityControlAudit :
    (((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103).all
      (fun (ins,pc) => biasedProbabilityControl pc ins) = true := by kernel_rfl

private theorem biasedProbabilityControlAt {pc : Nat} {ins : Instr}
    (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hc : kernel.code[pc]? = some ins) :
    biasedProbabilityControl pc ins = true := by
  apply List.all_eq_true.mp biasedProbabilityControlAudit (ins,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
    Nat.add_sub_of_le hLo,hc]
  rfl

set_option maxRecDepth 100000 in
private theorem biasedProbabilitySegmentAudit :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | none => false
      | some seg => if postStatistics true seg.stop then
          decide (postStatistics true pc ∧ pc ≠ 6508 ∧
            biasedProbabilityProgress seg.stop = biasedProbabilityProgress pc)
        else true) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem probabilityScratchCode :
    ((kernel.code.drop 3103).take (7742-3103)).all
      (fun i => i.op.isLocal ||
        (scoreEventOp i.op && !(scoreEventWrites i.op).contains 2535)) = true := by kernel_rfl

private theorem probabilityScratchStep {g : Nat} {s u : TState} {event : Option Event}
    (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3) (hScratch : ScoreScratchState s)
    (hStep : WStep kernel Assumptions.all l g s event u) :
    ScoreScratchState u := by
  rcases hStep with ⟨rfl,ht⟩ | ⟨_,rfl,he⟩
  · exact scoreScratchTau ht hScratch
  · obtain ⟨ins,hc,hLocal,_⟩ := estep_event_source he
    have hMem : ins ∈ (kernel.code.drop 3103).take (7742-3103) := by
      apply List.mem_of_getElem? (i := s.pc-3103)
      rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
    have hAudit := List.all_eq_true.mp probabilityScratchCode ins hMem
    simp only [hLocal,Bool.false_or,Bool.and_eq_true,Bool.not_eq_true'] at hAudit
    have hKeep : 2535 ∉ scoreEventWrites ins.op := by simpa using hAudit.2
    have hReady : ScoreScratchReady ins.op s := by
      simpa only [ScoreScratchState,hc,hLocal,Bool.false_eq_true,ite_false] using hScratch
    have hClear := scoreEventScratch hc hAudit.1 hSub hKeep he hReady
    by_cases hSame : u.pc = s.pc
    · simpa only [hSame,ScoreScratchState,hc,hLocal,Bool.false_eq_true,ite_false,ite_true]
        using hClear
    · exact scratchStateOfClear (by simpa only [hSame,ite_false] using hClear)

private theorem biasedDelayedOut {g : Nat} {s : TState} (hPc : s.pc = 6508) (hSub : s.sub = 0)
    (hFault : s.fault = none) (hBlock : l.block % 32 = 0) :
    out kernel Assumptions.all l g s = .ev (.tc .waitLd {s with sub := 1}) := by
  have hCode := hPc.symm ▸ Flow.code_6508
  have hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = true := by
    rw [hPc,Assumptions.all_tcStWaitLd]
    decide
  rw [out_event hFault hCode rfl rfl,eventTmpl_tcSt_wait hHook hSub hBlock]

private theorem biasedDelayedKind {g : Nat} {s : TState} {e : Event} {ending : Option TState}
    (hBlock : l.block % 32 = 0) (hPc : s.pc = 6508) (hSub : s.sub = 0)
    (he : EStep kernel Assumptions.all l g s e ending) :
    (∃ f, e.kind = .ub f ∧ ending = none) ∨
      (e.kind = .tc .waitLd ∧ ending = some {s with sub := 1}) := by
  obtain ⟨tmpl,hOut,hFire⟩ := he
  cases hFault : s.fault with
  | none =>
    rw [biasedDelayedOut hPc hSub hFault hBlock] at hOut
    obtain rfl := Out.ev.inj hOut
    exact .inr ⟨congrArg Event.kind hFire.1,by simpa only [hFault] using hFire.2⟩
  | some f =>
    simp only [out,hFault,Out.ev.injEq] at hOut
    subst tmpl
    exact .inl ⟨f,congrArg Event.kind hFire.1,hFire.2⟩

private theorem biasedStoreAfterWaitNext {g : Nat} {s u : TState} {e : Event} (hs : s.pc = 6508)
    (hSub : s.sub ≠ 0) (he : EStep kernel Assumptions.all l g s e (some u)) : u.pc = s.pc+1 := by
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
  obtain ⟨src,_,hStoreCode⟩ := probabilityCode .biased 0
  let dst := probabilityReg .biased 0
  have hAt : s.pc = probabilityPc .biased 0 := hs
  have hDecode : kernel.code[s.pc]? = some ⟨none,.tcSt dst src .s32x32b⟩ :=
    hAt.symm ▸ hStoreCode
  have hInstr : ins = ⟨none,.tcSt dst src .s32x32b⟩ :=
    Option.some.inj (hCode.symm.trans hDecode)
  have hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = true := by
    rw [hs,Assumptions.all_tcStWaitLd]
    decide
  have hTemplate := eventTmpl_tcSt_afterWait (A := Assumptions.all) (L := l) (g := g)
    (t := s) (ta := dst) (ss := src) (sh := .s32x32b) hHook hSub
  have hFire' : Fires s.pc
      (tcTmpl l g {s with sub := 0} (.tcSt dst src .s32x32b)) e (some u) := by
    rw [hInstr] at hFire
    exact hTemplate ▸ hFire
  exact probabilityCoreStoreNext (l := l) (g := g) (s := {s with sub := 0})
    (dst := dst) (src := src) hFire'

private theorem delayedStoreIsNonlocal {pc : Nat} {i : Instr}
    (hp : pc = 6508) (hc : kernel.code[pc]? = some i) : i.op.isLocal = false := by
  rw [hp,Flow.code_6508] at hc
  obtain rfl := Option.some.inj hc
  rfl

private theorem delayedStorePredecessorLocal {pc : Nat} {i : Instr}
    (hp : pc+1 = 6508) (hc : kernel.code[pc]? = some i) : i.op.isLocal = true := by
  have hs : pc = 6507 := by omega
  rw [hs,Flow.code_6507] at hc
  obtain rfl := Option.some.inj hc
  rfl

private def BiasedStatisticsClock (X : Execution) (g index : Nat) (s : TState) : Prop :=
  ScoreScratchState s ∧ (postStatistics true s.pc →
    ∃ prior, Publishes X (g,prior) .biased ∧ index = prior+biasedProbabilityClock s)

private theorem biasedStatisticsClockStep {X : Execution} {g index : Nat} {s u : TState}
    {event : Option Event} (hBlock : l.block % 32 = 0) (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742)
    (hSub : s.sub ≤ 3) (hSeen : BiasedStatisticsClock X g index s)
    (hStep : WStep kernel Assumptions.all l g s event u)
    (hGet : ∀ e, event = some e → X.get (g,index) = some e) :
    BiasedStatisticsClock X g (index+event.toList.length) u := by
  refine ⟨probabilityScratchStep hLo hHi hSub hSeen.1 hStep,?_⟩
  intro hNew
  have keep (hOld : postStatistics true s.pc)
      (hProgress : biasedProbabilityClock u =
        biasedProbabilityClock s+event.toList.length) :
      ∃ prior, Publishes X (g,prior) .biased ∧
        index+event.toList.length = prior+biasedProbabilityClock u := by
    obtain ⟨prior,hNotice,hEq⟩ := hSeen.2 hOld
    exact ⟨prior,hNotice,by omega⟩
  have beforeNext (hPc : u.pc = s.pc+1) :
      postStatistics true s.pc ∨ s.pc = repeatedNoticePc true := by
    unfold postStatistics at *
    exact or_iff_not_imp_right.mpr (fun h => ⟨by omega,by omega⟩)
  rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
  · obtain ⟨ins,hCode,_,hLocal⟩ := Softmax.tauScoreSource hTau
    have hLocalOpcode (hCase : postStatistics true s.pc ∨ postStatistics true (s.pc+1)) :
        ins.op.isLocal = true := by
      have hTest := (Bool.and_eq_true_iff.mp (biasedProbabilityControlAt hLo hHi hCode)).1
      rw [ite_eq_left hCase,Bool.and_eq_true,Bool.or_eq_true] at hTest
      rcases hTest.1 with hYes | hNonlocal
      · exact hYes
      · have hGuard := Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp hNonlocal).1
        rcases hLocal with ⟨_,hSkip⟩ | ⟨_,hYes,_⟩
        · rw [hGuard] at hSkip
          cases hSkip
        · exact hYes
    have fall (hPc : u.pc = s.pc+1) (hSubU : u.sub = 0) :
        ∃ prior, Publishes X (g,prior) .biased ∧ index = prior+biasedProbabilityClock u := by
      have hCase := hPc ▸ hNew
      have hOp := hLocalOpcode (.inr hCase)
      have hNoDelay : s.pc ≠ 6508 := fun h => by
        rw [delayedStoreIsNonlocal h hCode] at hOp
        cases hOp
      have hNo : s.pc ≠ repeatedNoticePc true := by
        intro hNotice
        rw [hNotice,repeatedNoticeCode true] at hCode
        obtain rfl := Option.some.inj hCode
        cases hOp
      have hTest := (Bool.and_eq_true_iff.mp (biasedProbabilityControlAt hLo hHi hCode)).1
      rw [ite_eq_left (Or.inr hCase),Bool.and_eq_true,hOp,ite_eq_left rfl,
        decide_eq_true_eq] at hTest
      exact keep ((beforeNext hPc).resolve_right hNo) (by
        simpa [biasedProbabilityClock,hPc,hSubU,hNoDelay] using hTest.2)
    rcases hLocal with ⟨rfl,_⟩ | ⟨_,hExecLocal,hExec⟩
    · exact fall rfl rfl
    have hSubS := (scratchClearOfLocal hCode hExecLocal hSeen.1).1
    rcases Softmax.scoreExecLocal hExec with hFrame | ⟨seg,hSite,hMatch,hResult⟩
    · have hSubU := hFrame.sub.trans hSubS
      have hChecked := biasedProbabilityControlAt hLo hHi hCode
      unfold biasedProbabilityControl at hChecked
      have hBranch := (Bool.and_eq_true_iff.mp hChecked).2
      have hPc := hFrame.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra dst uniform =>
        rw [hOp] at hBranch
        change (if postStatistics true dst then decide (postStatistics true s.pc ∧
          biasedProbabilityProgress dst = biasedProbabilityProgress s.pc) else true) =
          true at hBranch
        rw [ite_eq_left (hPc ▸ hNew),decide_eq_true_eq] at hBranch
        exact keep hBranch.1 (by simpa [biasedProbabilityClock,hPc,hSubS,hSubU] using hBranch.2)
      case brx => simp [hOp] at hBranch
      all_goals exact fall hPc hSubU
    · obtain ⟨hPc,hSubU,_,_⟩ := Softmax.scoreSegmentFrame hResult
      have h := List.all_eq_true.mp biasedProbabilitySegmentAudit _ hSite
      rw [hMatch] at h
      change (if postStatistics true seg.stop then decide (postStatistics true s.pc ∧
        s.pc ≠ 6508 ∧ biasedProbabilityProgress seg.stop = biasedProbabilityProgress s.pc)
        else true) = true at h
      rw [ite_eq_left (hPc ▸ hNew),decide_eq_true_eq] at h
      exact keep h.1 (by simpa [biasedProbabilityClock,hPc,hSubU,h.2.1] using h.2.2)
  · obtain ⟨ins,hCode,hNonlocal,hFire⟩ := estep_event_source hEvent
    have hAudit := (Bool.and_eq_true_iff.mp (statisticsIngressAt true hLo hHi hCode)).1
    have hOrd : Epilogue.ordinaryEvent ins.op = true := by simpa [hNonlocal] using hAudit
    have hCase : postStatistics true s.pc ∨ postStatistics true (s.pc+1) := by
      rcases callbackFrame_fires (Epilogue.ordinaryEventFrame hOrd) hFire with h | h
      · exact .inl (h ▸ hNew)
      · exact .inr (h ▸ hNew)
    have hTest := (Bool.and_eq_true_iff.mp (biasedProbabilityControlAt hLo hHi hCode)).1
    rw [ite_eq_left hCase,Bool.and_eq_true,hNonlocal,Bool.false_or,ite_eq_right (by decide),
      decide_eq_true_eq] at hTest
    have hOpcode := (Bool.and_eq_true_iff.mp hTest.1).2
    by_cases hDelayed : s.pc = 6508
    · by_cases hZero : s.sub = 0
      · rcases biasedDelayedKind hBlock hDelayed hZero hEvent with ⟨_,_,hNone⟩ | ⟨_,hAfter⟩
        · cases hNone
        · obtain rfl := Option.some.inj hAfter
          exact keep hNew (by simp [biasedProbabilityClock,hDelayed,hZero])
      · have hPc := biasedStoreAfterWaitNext hDelayed hZero hEvent
        have hAfter : u.pc ≠ 6508 := by omega
        have hOld : postStatistics true s.pc := by rw [hDelayed]; decide
        exact keep hOld (by
          rw [ite_eq_left hDelayed] at hTest
          simpa [biasedProbabilityClock,hPc,hDelayed,hZero,hAfter] using hTest.2)
    have hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = false := by
      rw [Assumptions.all_tcStWaitLd]
      have hNotice : 5683 ≤ s.pc := by
        change (5683 < s.pc ∧ _) ∨ (5683 < s.pc+1 ∧ _) at hCase
        omega
      simp [Assumptions.delayedTmemSites,hDelayed,show s.pc ≠ 4826 by omega]
    have hPc := probabilityEventNext hHook hOpcode hFire
    have hNo : u.pc ≠ 6508 := by
      intro hEq
      have hLocal := delayedStorePredecessorLocal (hPc.symm.trans hEq) hCode
      rw [hNonlocal] at hLocal
      cases hLocal
    rcases beforeNext hPc with hOld | hNotice
    · exact keep hOld (by
        rw [ite_eq_right hDelayed] at hTest
        unfold biasedProbabilityClock
        rw [ite_eq_right (fun h => hNo h.1),ite_eq_right (fun h => hDelayed h.1),hPc]
        simpa only [Nat.add_zero,Option.toList_some,List.length_singleton] using hTest.2)
    · refine ⟨index,⟨e,hGet e rfl,noticeKindAt true hNotice hEvent⟩,?_⟩
      rw [biasedProbabilityClock,hPc,hNotice]
      rfl
end

private theorem biasedClockAtQuarter (q : Fin 4) (sub : Nat)
    (hDelay : probabilityPc .biased q = 6508 → sub ≠ 0) :
    biasedProbabilityProgress (probabilityPc .biased q) +
      (if probabilityPc .biased q = 6508 ∧ sub ≠ 0 then 1 else 0) =
      1+Repeated.biased.probabilityStoreOffset q := by
  have hProgress : biasedProbabilityProgress (probabilityPc .biased q) +
      (if probabilityPc .biased q = 6508 then 1 else 0) =
      1+Repeated.biased.probabilityStoreOffset q := by fin_cases q <;> decide
  by_cases hs : probabilityPc .biased q = 6508
  · rw [ite_eq_left ⟨hs,hDelay hs⟩]
    simpa only [ite_eq_left hs] using hProgress
  · rw [ite_eq_right (fun h => hs h.1)]
    simpa only [ite_eq_right hs] using hProgress

/-- The selected biased quarter has the exact offset from its coefficient write,
including the same-PC load wait and the early publication before the tail. -/
theorem biasedProbabilityCoefficientPosition {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (q : Fin 4) {g store address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get (g,store) =
      some ⟨Softmax.probabilityPc .biased q,.tc (.st address vals shape)⟩) :
    ∃ pos a data, StatisticsStore X (g,pos) (Softmax.rescaleStore true) a data ∧
      store = pos+2+Softmax.Repeated.biased.probabilityStoreOffset q := by
  have hBounds : 3420 ≤ Softmax.probabilityPc .biased q ∧
      Softmax.probabilityPc .biased q < 7742 ∧
      postStatistics true (Softmax.probabilityPc .biased q) := by fin_cases q <;> decide
  have hStart : ¬ postStatistics true 3103 := by decide
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨s,_,hSeen,hStep⟩ := Softmax.softmaxRoleReplayAt hp hX he hBounds.1 hBounds.2.1
    (BiasedStatisticsClock X g)
    (fun _ _ _ hAt => ⟨scratchStateOfClear ⟨hAt.2.1,hAt.2.2.1⟩,
      fun hIn => (hStart (hAt.1 ▸ hIn)).elim⟩)
    (fun hLo hHi hSub hPrior hStep hGet =>
      biasedStatisticsClockStep hBlock hLo hHi hSub hPrior hStep hGet)
  obtain ⟨prior,hNotice,hRank⟩ := hSeen.2 ((estep_source_pc hStep) ▸ hBounds.2.2)
  have hPc := (estep_source_pc hStep).symm
  have hProg : biasedProbabilityClock s =
      1+Softmax.Repeated.biased.probabilityStoreOffset q := by
    have hDelay : s.pc = 6508 → s.sub ≠ 0 := by
      intro hDelayed hZero
      rcases biasedDelayedKind hBlock hDelayed hZero hStep with ⟨_,h, _⟩ | ⟨h, _⟩ <;> cases h
    change s.pc = probabilityPc .biased q at hPc
    unfold biasedProbabilityClock
    rw [hPc]
    exact biasedClockAtQuarter q s.sub (fun h => hDelay (hPc.trans h))
  rw [hProg] at hRank
  obtain ⟨pos,a,data,hPos,hStore,_⟩ := rescaleStoreBeforePublication hX true hNotice
  exact ⟨pos,a,data,hStore,by omega⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
