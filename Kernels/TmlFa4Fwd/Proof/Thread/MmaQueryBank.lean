-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
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
import Kernels.TmlFa4Fwd.Proof.MmaQkOperandFrame
import Kernels.TmlFa4Fwd.Proof.MmaQkQueryRetarget
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (RoleShape qkSetupStart qkPc qkStage qStart qkFragment
  QueryOperandFragment SharedOperandRange qkSetupRunBeforeEvent retargetQkQueryBank
  sharedDescriptorWord mmaCutStep mmaStepReg mmaWrites qDescriptorFacts
  observedQkOperand out_eq_core initialQueryBankBeforeEvent)

noncomputable section

private def queryBankStage (pos : Nat) : Fin 2 :=
  if (qkPc 0 ≤ pos ∧ pos ≤ qkSetupStart 1) ∨ (qkPc 2 ≤ pos ∧ pos ≤ qkSetupStart 3)
    then 0 else 1

private def startsSetup (pos : Nat) : Bool :=
  (List.finRange 4).any fun block => qkSetupStart block == pos

private def insideSetup (pos : Nat) : Bool :=
  (List.finRange 4).any fun block => decide (qkSetupStart block < pos ∧ pos < qkPc block)

private def bankRegisters : List Nat := 9632 :: (List.finRange 8).map (fun i => 9624+i.val)

private def stableDestination (pos dest : Nat) : Bool :=
  decide (2768 ≤ dest) ||
    (decide (1935 ≤ dest) && !insideSetup dest && (queryBankStage pos == queryBankStage dest))

private def bankCode (pos : Nat) (i : Instr) : Bool :=
  startsSetup pos || insideSetup pos ||
    (((bankRegisters.all fun r => !(mmaWrites i.op).contains r) &&
      stableDestination pos (pos+1)) &&
      match i.op with
      | .bra dest _ => stableDestination pos dest
      | .brx .. => false
      | _ => true)

set_option maxRecDepth 100000 in
private theorem bankCodeAudit :
    (((kernel.code.drop 1935).take (2768-1935)).zipIdx 1935).all
      (fun (i,pos) => bankCode pos i) = true := by kernel_rfl

private theorem bankCodeAt {pos : Nat} {i : Instr} (hLo : 1935 ≤ pos) (hHi : pos < 2768)
    (hStart : startsSetup pos = false) (hInside : insideSetup pos = false)
    (hGet : kernel.code[pos]? = some i) :
    (bankRegisters.all fun r => !(mmaWrites i.op).contains r) = true ∧
      stableDestination pos (pos+1) = true ∧
      (match i.op with
      | .bra dest _ => stableDestination pos dest
      | .brx .. => false
      | _ => true) = true := by
  let code := ((kernel.code.drop 1935).take (2768-1935)).zipIdx 1935
  have hMem : (i,pos) ∈ code := by
    apply List.mem_of_getElem? (i := pos-1935)
    dsimp only [code]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hGet]
    rfl
  have h := List.all_eq_true.mp bankCodeAudit (i,pos) hMem
  simp only [bankCode,hStart,hInside,Bool.false_or,Bool.and_eq_true] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

private structure BankFrame (l : Launch) (s : TState) : Prop where
  lower : 1935 ≤ s.pc
  outside : insideSetup s.pc = false
  shape : RoleShape s
  role : s.regs 1062 = some (b32 12)
  id : s.regs 9632 = some (b32 0x8200490)
  values : ∀ step : Fin 8, s.regs (9624+step.val) = some
    (b64 (sharedDescriptorWord (qStart l (queryBankStage s.pc)+qkFragment step) 16))

private theorem ordinaryBankStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hs : BankFrame l s) (hHi : s.pc < 2768) (hStart : startsSetup s.pc = false)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    2768 ≤ u.pc ∨ BankFrame l u := by
  have hCode {i : Instr} (h : kernel.code[s.pc]? = some i) :=
    bankCodeAt hs.lower hHi hStart hs.outside h
  have hCore : out kernel Assumptions.all l g s = out kernel [] l g s :=
    out_eq_core (by have := hs.lower; omega) hHi
  have hMove : stableDestination s.pc u.pc = true := by
    rcases hStep with ⟨rfl,hTau⟩ | ⟨e,rfl,hEvent⟩
    · have ht : Tau kernel [] l g s u := by
        unfold Tau at hTau ⊢
        rwa [← hCore]
      obtain ⟨ins,hGet⟩ := tau_core_has_code ht
      have hAudit := hCode hGet
      rcases tau_core_frame hGet ht with rfl | hFrame
      · exact hAudit.2.1
      have hPc := hFrame.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra dst uni => simpa only [hOp,hPc] using hAudit.2.2
      case brx =>
        simp only [hOp,Bool.false_eq_true] at hAudit
        exact hAudit.2.2.elim
      all_goals exact hPc.symm ▸ hAudit.2.1
    · have he : EStep kernel [] l g s e (some u) := by
        obtain ⟨tm,hOut,hFire⟩ := hEvent
        exact ⟨tm,hCore ▸ hOut,hFire⟩
      obtain ⟨i,hGet,_,_⟩ := estep_event_source hEvent
      rcases (estep_return_pc he (fun _ _ _ h => execLocal_frame h)).2 with h | h
      · exact h.symm ▸ (by
          simp [stableDestination,hs.lower,hs.outside] : stableDestination s.pc s.pc = true)
      · exact h.symm ▸ (hCode hGet).2.1
  simp only [stableDestination,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
    Bool.not_eq_true',beq_iff_eq] at hMove
  rcases hMove with hExit | ⟨⟨hLower,hInside⟩,hPhase⟩
  · exact .inl hExit
  have hRegs {r : Nat} (hr : r ∈ bankRegisters) : u.regs r = s.regs r := by
    refine mmaStepReg (by have := hs.lower; omega) hHi (fun i hi => ?_) hStep
    have hKeep := List.all_eq_true.mp (hCode hi).1 r hr
    simpa using hKeep
  have hNext := (mmaCutStep (by have := hs.lower; omega) hHi hStep ⟨hs.shape,hs.role⟩).2
  refine .inr ⟨hLower,hInside,hNext.1,hNext.2,(hRegs (by simp [bankRegisters])).trans hs.id,?_⟩
  intro step
  have hMem : 9624+step.val ∈ bankRegisters := by
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (by simp))
  rw [hRegs hMem,← hPhase]
  exact hs.values step

private theorem setupPreservesScalar (block : Fin 4) :
    ((kernel.code.drop (qkSetupStart block)).take 40).all (fun i =>
      ([1062,9632] : List Nat).all (fun r => !(writesRegs i.op).contains r)) = true ∧
        ((kernel.code.drop (qkSetupStart block)).take 39).all
          (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
  fin_cases block <;> exact ⟨by set_option maxRecDepth 100000 in kernel_rfl,
    by set_option maxRecDepth 100000 in kernel_rfl⟩

private theorem actualBankSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {es : List Event} {vs : List Visit} (block : Fin 4)
    (hStart : s.pc = qkSetupStart block) (hs : BankFrame l s) (hClean : s.fault = none)
    (hw : Walk kernel Assumptions.all l g s es vs) {e : Event} (hMem : e ∈ es)
    (hNotUb : ∀ f, e.kind ≠ .ub f) :
    ∃ t post, BankFrame l t ∧ post.length < vs.length ∧
      Walk kernel Assumptions.all l g t es post := by
  have hSub : s.sub = 0 := hs.shape.2.2 (by rw [hStart]; fin_cases block <;> decide)
  have hAt : At s (qkPc block-40) [] := ⟨hStart,hSub,hs.shape.2.1,hClean,trivial⟩
  obtain ⟨t,post,hRun,ht,hLen,hWalk⟩ :=
    qkSetupRunBeforeEvent block hAt hw hMem (.inr hNotUb)
  obtain ⟨hAudit,hFlow⟩ := setupPreservesScalar block
  have hKeep {r} (hr : r ∈ [1062,9632]) : t.regs r = s.regs r :=
    Epilogue.schedulerLocalFrame hAudit hFlow hRun hStart.ge (by rw [hStart]) hr
  have hInput : queryBankStage (qkSetupStart block) = if qkStage block = 0 then 1 else 0 := by
    fin_cases block <;> rfl
  have hOutput : queryBankStage (qkPc block) = qkStage block := by fin_cases block <;> rfl
  have hOut : 1935 ≤ qkPc block ∧ insideSetup (qkPc block) = false := by
    fin_cases block <;> decide
  have hWords := retargetQkQueryBank hp block hAt (by
    intro step
    rw [← hInput,← hStart]
    exact hs.values step) hRun
  have hT : BankFrame l t :=
    ⟨ht.1.symm ▸ hOut.1,ht.1.symm ▸ hOut.2,
      ⟨ht.2.1.symm ▸ by decide,ht.2.2.1,fun _ => ht.2.1⟩,
      (hKeep (by simp)).trans hs.role,(hKeep (by simp)).trans hs.id,
      fun step => by rw [ht.1,hOutput]; exact hWords step⟩
  exact ⟨t,post,hT,by omega,hWalk⟩

private theorem cleanBeforeMma {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {e : Event}
    (hw : Walk kernel Assumptions.all l g s es vs) (he : e ∈ es)
    (hNotUb : ∀ f, e.kind ≠ .ub f) : s.fault = none := by
  cases h : s.fault with
  | none => rfl
  | some fault =>
    have hOut : out kernel Assumptions.all l g s = .ev (.ub fault) := by simp [out,h]
    cases hw with
    | stop => cases he
    | tau ht _ => rw [Tau,hOut] at ht; cases ht
    | ev hv _ =>
      obtain ⟨tm,hm,hf⟩ := hv
      obtain rfl := Out.ev.inj (hm.symm.trans hOut)
      cases hf.2
    | last hv =>
      obtain rfl := List.mem_singleton.mp he
      obtain ⟨tm,hm,hf⟩ := hv
      obtain rfl := Out.ev.inj (hm.symm.trans hOut)
      exact (hNotUb fault (congrArg Event.kind hf.1)).elim

set_option maxRecDepth 100000 in
private theorem bankExitFloor :
    (kernel.code.drop 2768).all (fun i => staysPastEvent 2768 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem bankExitSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2768 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem actualBankAtQk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) (block : Fin 4) (step : Fin 8)
    {s : TState} {events : List Event} {visits : List Visit} (hs : BankFrame l s)
    (hw : Walk kernel Assumptions.all l g s events visits)
    {index dst : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hGet : events[index]? = some ⟨qkPc block+step.val,.tc (.mma dst op accum mask)⟩) :
    QueryOperandFragment l g (qkStage block) step op := by
  let event : Event := ⟨qkPc block+step.val,.tc (.mma dst op accum mask)⟩
  have hTarget : event.pc < 2768 := by
    change qkPc block+step.val < 2768
    fin_cases block <;> fin_cases step <;> decide
  have hClean : ∀ f, event.kind ≠ .ub f := by intro f h; cases h
  have hPhase : queryBankStage event.pc = qkStage block := by
    change queryBankStage (qkPc block+step.val) = qkStage block
    fin_cases block <;> fin_cases step <;> rfl
  change events[index]? = some event at hGet
  generalize hSize : visits.length = fuel
  induction fuel using Nat.strong_induction_on generalizing s events visits index with
  | h fuel ih =>
    have hMem : event ∈ events := List.mem_of_getElem? hGet
    have hHi : s.pc < 2768 := by
      by_contra! hExit
      exact (Nat.not_le_of_lt hTarget (eventTailEvents bankExitFloor bankExitSegments
        hw hExit event hMem)).elim
    by_cases hSetup : startsSetup s.pc = true
    · obtain ⟨setup,_,hPc⟩ := List.any_eq_true.mp hSetup
      have hAt : s.pc = qkSetupStart setup := (beq_iff_eq.mp hPc).symm
      obtain ⟨t,post,hBank,hSmall,hWalk⟩ :=
        actualBankSetup hp setup hAt hs (cleanBeforeMma hw hMem hClean) hw hMem hClean
      exact ih post.length (by omega) hBank hWalk hGet rfl
    · have hOther := Bool.eq_false_iff.mpr hSetup
      have hNext {s u : TState} {es : List Event} {vs : List Visit}
          (hL : vs.length < fuel) (hs : BankFrame l s) (hHi : s.pc < 2768)
          (hSkip : startsSetup s.pc = false) {ev : Option Event}
          (h : WStep kernel Assumptions.all l g s ev u)
          (hw : Walk kernel Assumptions.all l g u es vs) {j : Nat} (hj : es[j]? = some event) :
          QueryOperandFragment l g (qkStage block) step op := by
        rcases ordinaryBankStep hs hHi hSkip h with hExit | hBank
        · exact (Nat.not_le_of_lt hTarget (eventTailEvents bankExitFloor bankExitSegments
            hw hExit event (List.mem_of_getElem? hj))).elim
        · exact ih vs.length hL hBank hw hj rfl
      cases hw with
      | stop => simp at hGet
      | @tau t u es vs ht hw =>
        exact hNext (by simp at hSize; omega) hs hHi hOther (.inl ⟨rfl,ht⟩) hw hGet
      | @ev t u e es vs he hw =>
        cases index with
        | zero =>
          obtain rfl := Option.some.inj hGet
          have hPc := (estep_source_pc he).symm
          have hA := hs.values step
          rw [hPc,hPhase] at hA
          obtain ⟨_,_,_,_,heq,hOp,_⟩ := observedQkOperand hp hg block step hPc hA hs.id he
          have hKind := congrArg Event.kind heq
          cases hKind
          exact hOp
        | succ j =>
          exact hNext (by simp at hSize; omega) hs hHi hOther (.inr ⟨e,rfl,he⟩) hw hGet
      | last he =>
        obtain rfl := List.mem_singleton.mp hMem
        obtain ⟨tm,_,hFires⟩ := he
        rcases fires_none_ends hFires with ⟨_,h⟩ | h <;> cases h

/-- Any actual QK fragment, including a repeated visit of a loop bank, reads
the query descriptor for its stage. -/
theorem QkInstruction.queryOperand {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {block : Fin 4} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hIssue : QkInstruction X i block step d op accum mask) :
    QueryOperandFragment l i.1 (qkStage block) step op := by
  obtain ⟨g,index⟩ := i
  let e : Event := ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩
  have hGet : X.get (g,index) = some e := hIssue.decoded
  have hPc : 1916 < e.pc ∧ e.pc < 2768 := by
    change 1916 < qkPc block+step.val ∧ qkPc block+step.val < 2768
    fin_cases block <;> fin_cases step <;> decide
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX hGet (by omega) hHint
  have hWarp : warpIndex l g = 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  obtain ⟨s,_,hIndex,hs,hr⟩ := initialQueryBankBeforeEvent hp hX hGet hWarp hPc.1
    (by intro _ h; cases h)
  obtain ⟨vs,hw⟩ := Mma.walkFromRun hr
  let start := Mma.descriptorShufflePos (laneOf l g)+1
  have hTail : ((X.tr g).drop start)[index-start]? = some e := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hIndex]
    exact hGet
  have hBank : BankFrame l s := by
    refine ⟨hs.1.symm ▸ by decide,hs.1.symm ▸ by decide,
      ⟨hs.2.1.symm ▸ by decide,hs.2.2.1,fun _ => hs.2.1⟩,
      hs.2.2.2.2.1,hs.2.2.2.2.2.1,?_⟩
    intro frag
    rw [hs.1,show queryBankStage 1935 = 1 from rfl]
    exact holds_mem (hs.2.2.2.2.2.2) (List.mem_map_of_mem (by simp))
  exact actualBankAtQk hp (event_thread_lt hX hGet) block step hBank hw hTail

/-- A pending or actual QK A byte of any query/key loop visit is allocated
and cannot address the low shared-memory mbarrier area. -/
theorem QkInstruction.queryByteRange {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {block : Fin 4} {step : Fin 8} {d index : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} {loc : Loc}
    (hIssue : QkInstruction X i block step d op accum mask)
    (hByte : op.byteLoc .a index = some loc) :
    SharedOperandRange l i.1 loc :=
  (hIssue.queryOperand hp hX).operandRange hp hByte

end
end PTX.Kernels.TmlFa4Fwd.Thread
