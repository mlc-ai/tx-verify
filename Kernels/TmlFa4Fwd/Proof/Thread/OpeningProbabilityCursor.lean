-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasReturn
public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilityOrder
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
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
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part075

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

/-- Upper instruction boundary after the indicated number of events since the affine entry.
The delayed wait and its following store use the same instruction address. -/
private def firstStoreLimit : Nat → Nat
  | 0 => 4397
  | 1 => 4826
  | 2 => 4826
  | 3 => 4835
  | 4 => 4844
  | 5 => 4845
  | 6 => 4847
  | _ => 4856

private def firstStoreCursor (n : Nat) (s : TState) : Prop :=
  3425 ≤ s.pc ∧ s.pc ≤ firstStoreLimit n ∧ s.sub ≤ 3 ∧ ScoreScratchState s ∧
    (n = 1 → s.pc = 4826 → s.sub = 0)

private theorem firstStoreLimit_le (n : Nat) : firstStoreLimit n ≤ 4856 := by
  unfold firstStoreLimit
  split <;> decide

private def respectsFirstStoreLimit (cut : Nat) : Op → Bool
  | .bra dst _ => decide (dst ≤ cut)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem firstStoreBranchAudit (n : Nat) :
    ((kernel.code.drop 3425).take (firstStoreLimit n - 3425)).all
      (fun i => respectsFirstStoreLimit (firstStoreLimit n) i.op) = true := by
  unfold firstStoreLimit
  split <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstStoreSegmentAudit (n : Nat) :
    Assumptions.swExp2Sites.all (fun pc =>
      if 3425 ≤ pc ∧ pc < firstStoreLimit n then
        match cuteExp2.matchAt kernel pc with
        | some seg => decide (seg.stop ≤ firstStoreLimit n)
        | none => false
      else true) = true := by
  unfold firstStoreLimit
  split <;> kernel_rfl

private theorem firstStoreLimitInstruction (n : Nat) :
    ∃ op, kernel.code[firstStoreLimit n]? = some ⟨none,op⟩ ∧ op.isLocal = false := by
  unfold firstStoreLimit
  split
  · exact ⟨_, Flow.code_4397, rfl⟩
  · exact ⟨_, Flow.code_4826, rfl⟩
  · exact ⟨_, Flow.code_4826, rfl⟩
  · exact ⟨_, Flow.code_4835, rfl⟩
  · exact ⟨_, Flow.code_4844, rfl⟩
  · exact ⟨_, Flow.code_4845, rfl⟩
  · exact ⟨_, Flow.code_4847, rfl⟩
  · exact ⟨_, Flow.code_4856, rfl⟩

private theorem beforeFirstStoreSilent {l : Launch} {g n : Nat} {s u : TState}
    (hs : firstStoreCursor n s) (ht : Tau kernel Assumptions.all l g s u) :
    firstStoreCursor n u := by
  obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
  obtain ⟨hLo,hHi,hSub,hScratch,hDelay⟩ := hs
  have hWindow : s.pc < (windowSite .firstRoundCounters).stop := by
    have h := firstStoreLimit_le n
    change s.pc < 5006
    omega
  have hw := windowStepFrame .firstRoundCounters hLo hWindow hSub (.inl ⟨rfl,ht⟩)
  have hScratchU := windowStepScratch .firstRoundCounters hLo hWindow hSub
    (.inl ⟨rfl,ht⟩) hScratch
  have hBefore : s.pc < firstStoreLimit n := by
    apply lt_of_le_of_ne hHi
    intro h
    obtain ⟨op,hCode,hNonlocal⟩ := firstStoreLimitInstruction n
    rw [h,hCode] at hc
    obtain rfl := Option.some.inj hc.symm
    rcases hExec with ⟨_, hh⟩ | ⟨_,hh,_⟩
    · cases hh
    · rw [hNonlocal] at hh
      cases hh
  refine ⟨hw.1,?_,hw.2.2.1,hScratchU,?_⟩
  · have hi : ins ∈ (kernel.code.drop 3425).take (firstStoreLimit n - 3425) := by
      apply List.mem_of_getElem? (i := s.pc-3425)
      rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
    rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
    · change s.pc+1 ≤ _
      omega
    rcases scoreExecLocal hLocal with hFrame | ⟨seg,hSite,hMatch,hRun⟩
    · have hAudit := List.all_eq_true.mp (firstStoreBranchAudit n) ins hi
      have hNext := hFrame.pc
      cases hop : ins.op <;> simp only [hop,nextPc,BrxTarget,or_false] at hNext
      case bra dst uni =>
        simpa only [hop,respectsFirstStoreLimit,decide_eq_true_eq,hNext] using hAudit
      case brx => simp [hop,respectsFirstStoreLimit] at hAudit
      all_goals omega
    · have hAudit := List.all_eq_true.mp (firstStoreSegmentAudit n) s.pc hSite
      rw [ite_eq_left ⟨hLo,hBefore⟩,hMatch,decide_eq_true_eq] at hAudit
      exact (scoreSegmentFrame hRun).1.symm ▸ hAudit
  · intro hn hu
    subst n
    rcases hExec with ⟨rfl,_⟩ | ⟨_,hLocal,hExec⟩
    · rfl
    rcases scoreExecLocal hExec with hFrame | ⟨_,_,_,hRun⟩
    · exact hFrame.sub.trans (scratchClearOfLocal hc hLocal hScratch).1
    · exact (scoreSegmentFrame hRun).2.1

private theorem firstDelayedWaitOut {l : Launch} {g : Nat} {s : TState}
    (hs : s.pc = 4826) (hSub : s.sub = 0) (hFault : s.fault = none)
    (hBlock : l.block % 32 = 0) :
    out kernel Assumptions.all l g s = .ev (.tc .waitLd {s with sub := 1}) := by
  have hCode := hs.symm ▸ Flow.code_4826
  have hHook : Assumptions.all.any (·.tcStWaitLd s.pc) = true := by
    rw [hs,Assumptions.all_tcStWaitLd]
    decide
  rw [out_event hFault hCode rfl rfl,eventTmpl_tcSt_wait hHook hSub hBlock]

private theorem firstStoreEventAudit :
    ((kernel.code.drop 3425).take (4856+1-3425)).all
      (fun i => i.op.isLocal ||
        (scoreEventOp i.op && !(scoreEventWrites i.op).contains 100000)) = true := by decide +kernel

private theorem firstStoreLimitAdvance (n : Nat) (hn : n < 6) (hOne : n ≠ 1) :
    firstStoreLimit n+1 ≤ firstStoreLimit (n+1) := by
  interval_cases n
  all_goals first | contradiction | exact of_decide_eq_true rfl

private theorem beforeFirstStoreEvent {l : Launch} {g n : Nat} {s u : TState}
    {e : Event} (hBlock : l.block % 32 = 0) (hn : n < 6)
    (hs : firstStoreCursor n s) (he : EStep kernel Assumptions.all l g s e (some u)) :
    firstStoreCursor (n+1) u := by
  obtain ⟨hLo,hHi,hSub,hScratch,hDelay⟩ := hs
  have hUpper := firstStoreLimit_le n
  have hWindow : s.pc < (windowSite .firstRoundCounters).stop := by
    change s.pc < 5006
    omega
  have hw := windowStepFrame .firstRoundCounters hLo hWindow hSub (.inr ⟨_,rfl,he⟩)
  have hScratchU := windowStepScratch .firstRoundCounters hLo hWindow hSub
    (.inr ⟨_,rfl,he⟩) hScratch
  obtain ⟨ins,hc,hLocal,_⟩ := estep_event_source he
  have hi : ins ∈ (kernel.code.drop 3425).take (4856+1-3425) := by
    apply List.mem_of_getElem? (i := s.pc-3425)
    rwa [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hLo]
  have hOp := List.all_eq_true.mp firstStoreEventAudit _ hi
  simp only [hLocal,Bool.false_or,Bool.and_eq_true, Bool.not_eq_true'] at hOp
  have hKeep : 100000 ∉ scoreEventWrites ins.op := by simpa using hOp.2
  have hProgress := scoreEventStep hc hOp.1 hSub hKeep he
  have hPc : u.pc ≤ s.pc+1 := by rcases hProgress.1.pc with ⟨h,_⟩ | ⟨h,_⟩ <;> omega
  refine ⟨hw.1,?_,hw.2.2.1,hScratchU,?_⟩
  · by_cases hN : n = 1
    · subst n
      change s.pc ≤ 4826 at hHi
      by_cases hHere : s.pc = 4826
      · obtain ⟨tmpl,hOut,hFire⟩ := he
        cases hFault : s.fault with
        | some f =>
          simp only [out,hFault,Out.ev.injEq] at hOut
          subst tmpl
          cases hFire.2
        | none =>
          rw [firstDelayedWaitOut hHere (hDelay rfl hHere) hFault hBlock] at hOut
          obtain rfl := Out.ev.inj hOut
          obtain rfl := Option.some.inj hFire.2
          exact hHi
      · change u.pc ≤ 4826
        omega
    · have hAdvance := firstStoreLimitAdvance n hn hN
      omega
  · intro h hHere
    have hZero : n = 0 := by omega
    subst n
    change s.pc ≤ 4397 at hHi
    omega

private theorem firstStoreAtCursor {l : Launch} {g n : Nat} {s : TState}
    {ending : Option TState} (hBlock : l.block % 32 = 0)
    (q : Fin 4) (hn : n < 1+probabilityTraceIndex q)
    (hs : firstStoreCursor n s) {a : Nat} {values : List Value} {shape : TcShape}
    (he : EStep kernel Assumptions.all l g s
      ⟨probabilityPc .first q,.tc (.st a values shape)⟩ ending) : False := by
  have hPc := estep_source_pc he
  have hBound := hs.2.1
  fin_cases q
  · change n < 2 at hn
    change 4826 = s.pc at hPc
    interval_cases n
    · change s.pc ≤ 4397 at hBound
      omega
    · obtain ⟨tmpl,hOut,hFire⟩ := he
      cases hFault : s.fault with
      | some f =>
        simp only [out,hFault,Out.ev.injEq] at hOut
        subst tmpl
        cases congrArg Event.kind hFire.1
      | none =>
        rw [firstDelayedWaitOut hPc.symm (hs.2.2.2.2 rfl hPc.symm) hFault hBlock] at hOut
        obtain rfl := Out.ev.inj hOut
        cases congrArg Event.kind hFire.1
  · change n < 3 at hn
    change 4835 = s.pc at hPc
    interval_cases n <;> change s.pc ≤ _ at hBound <;> norm_num [firstStoreLimit] at hBound <;>
      omega
  · change n < 4 at hn
    change 4844 = s.pc at hPc
    interval_cases n <;> norm_num [firstStoreLimit] at hBound <;> omega
  · change n < 7 at hn
    change 4856 = s.pc at hPc
    interval_cases n <;> norm_num [firstStoreLimit] at hBound <;> omega

private theorem firstStoreWalkIndex {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (hBlock : l.block % 32 = 0)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (q : Fin 4) {a : Nat} {values : List Value} {shape : TcShape} {index n : Nat}
    (hs : firstStoreCursor n s)
    (he : events[index]? = some ⟨probabilityPc .first q,.tc (.st a values shape)⟩) :
    1+probabilityTraceIndex q ≤ n+index := by
  by_contra! hShort
  have hCap : 1+probabilityTraceIndex q ≤ 7 := by fin_cases q <;> decide
  induction hw generalizing n index with
  | stop => simp at he
  | tau ht _ ih => exact ih (beforeFirstStoreSilent hs ht) he hShort
  | ev h _ ih =>
    cases index with
    | zero => cases Option.some.inj he; exact firstStoreAtCursor hBlock q (by omega) hs h
    | succ index =>
      exact ih (beforeFirstStoreEvent hBlock (by omega) hs h)
        (List.getElem?_cons_succ.symm.trans he) (by omega)
  | last h =>
    cases index with
    | zero => cases Option.some.inj he; exact firstStoreAtCursor hBlock q (by omega) hs h
    | succ index => simp at he

set_option maxRecDepth 100000 in
private theorem beforeProbabilityFloor :
    (kernel.code.drop 4826).all (fun i => Thread.staysPastEvent 4826 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem beforeProbabilitySegments :
    ∀ site, 4826 ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → 4826 ≤ seg.stop := by
  have hAudit : Assumptions.swExp2Sites.all (fun site =>
      if 4826 ≤ site then match cuteExp2.matchAt kernel site with
        | some seg => decide (4826 ≤ seg.stop)
        | none => false
      else true) = true := by kernel_rfl
  intro site hSite hMember seg hMatch
  have h := List.all_eq_true.mp hAudit site hMember
  rw [ite_eq_left hSite,hMatch,decide_eq_true_eq] at h
  exact h

/-- An actual first-visit store certifies that its lane recorded the whole affine,
statistics, and probability prefix through the corresponding store. -/
theorem OpeningFmaLane.probabilityStoreBound {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch wait : Nat} {stage : Fin 2} (entry : OpeningFmaLane p l X g batch stage wait)
    (q : Fin 4) {store address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get (g,store) = some ⟨probabilityPc .first q,.tc (.st address vals shape)⟩) :
    entry.pos+1+probabilityTraceIndex q ≤ store := by
  have hPc : 4826 ≤ probabilityPc .first q := by fin_cases q <;> decide
  have hPos : entry.pos ≤ store := by
    rw [entry.position]
    by_cases hLane : laneOf l g = 0
    · rw [ite_eq_left hLane]
      have hPrior := Thread.traceOrderOfSegmentFloor hX beforeProbabilityFloor
        beforeProbabilitySegments (entry.releasedBias hLane) he (by change 3590 < 4826; decide) hPc
      omega
    · rw [ite_eq_right hLane]
      have hPrior := Thread.traceOrderOfSegmentFloor hX beforeProbabilityFloor
        beforeProbabilitySegments entry.arrival.arrival he (by change 3583 < 4826; decide) hPc
      omega
  let suffix := (X.tr g).drop entry.pos
  have hFound : suffix[store-entry.pos]? =
      some ⟨probabilityPc .first q,.tc (.st address vals shape)⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact he
  have hSuffix : suffix ≠ [] := by intro h; simp [h] at hFound
  obtain ⟨_,hw⟩ := Mma.walkFromRun
    (entry.continuation.after_local_nonempty entry.localSteps hSuffix)
  have hReady : firstStoreCursor 0 entry.ready := by
    have hAt := entry.checkpoint
    exact ⟨by rw [hAt.1]; decide,by rw [hAt.1]; decide,
      by rw [hAt.2.1]; decide,scratchStateOfClear ⟨hAt.2.1,hAt.2.2.1⟩,by intro h; cases h⟩
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hIndex := firstStoreWalkIndex hBlock hw q hReady hFound
  omega

end PTX.Kernels.TmlFa4Fwd.Softmax
