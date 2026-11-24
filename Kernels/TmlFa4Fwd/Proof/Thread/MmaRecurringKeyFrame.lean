-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyPrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseOrdinal
import Kernels.TmlFa4Fwd.Proof.Thread.MmaKeyReadyProjection
import Kernels.TmlFa4Fwd.Proof.MmaOperandRange
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheBroadcasts
import Kernels.TmlFa4Fwd.Proof.Thread.MmaOperandReady
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueSender
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
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
import Lemmas.Flow.TauFrame
import Lemmas.Flow.Final
import Lemmas.Flow.Tc

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

noncomputable section

private def keyBroadcast : Nat := 2361

private def keyLive (pos : Nat) : Prop :=
  keyBroadcast < pos ∧ pos ≤ 2515

private instance (pos : Nat) : Decidable (keyLive pos) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def keyUse (X : Execution) (g pos : Nat) : Nat :=
  (((X.tr g).take pos).filterMap readyEvent).length - 1

private def keyRank (X : Execution) (g pos : Nat) : Nat :=
  Thread.Mma.readyOccurrence X g pos .loopKey

private def keyCarries (l : Launch) (X : Execution) (g pos : Nat) (s : TState) : Prop :=
  keyLive s.pc → s.regs 2600 = some (b32 (keyDescriptorLow l (keyUse X g pos))) ∧
    keyUse X g pos % 2 = 0 ∧ 2 ≤ keyUse X g pos ∧
      keyUse X g pos = 2 * keyRank X g pos

private theorem keyCursorThroughEvent {X : Execution} {g pos : Nat} {e : Event}
    (he : X.get (g,pos) = some e) (hReady : readyEvent e = none) :
    keyUse X g (pos+1) = keyUse X g pos ∧ keyRank X g (pos+1) = keyRank X g pos := by
  change (X.tr g)[pos]? = some e at he
  have hRank := recurringKeyPollCountErased (events := [e]) (by simp [hReady])
  constructor
  · simp [keyUse,List.take_add_one,he,hReady]
  · change ((X.tr g).take (pos+1)).countP (readyAtSite 2) =
      ((X.tr g).take pos).countP (readyAtSite 2)
    rw [List.take_add_one,he,Option.toList_some,List.countP_append,hRank,Nat.add_zero]

private theorem keyCursorThroughPrefix {X : Execution} {g pos : Nat} {pre tail : List Event}
    (hSuffix : (X.tr g).drop pos = pre ++ tail)
    (hReady : pre.filterMap readyEvent = []) :
    keyUse X g (pos+pre.length) = keyUse X g pos ∧
      keyRank X g (pos+pre.length) = keyRank X g pos := by
  constructor
  · simp [keyUse,List.take_add,hSuffix,List.filterMap_append,hReady]
  · change ((X.tr g).take (pos+pre.length)).countP (readyAtSite 2) =
      ((X.tr g).take pos).countP (readyAtSite 2)
    rw [List.take_add,hSuffix,List.take_left,List.countP_append,
      recurringKeyPollCountErased hReady,Nat.add_zero]

private def keyPreservedEdge (pos dst : Nat) : Bool :=
  !decide (keyLive dst) || decide (keyLive pos)

private def keyCarryCode (pos : Nat) (ins : Instr) : Bool :=
  pos == keyBroadcast ||
    ((!(mmaWrites ins.op).contains 2600 &&
      keyPreservedEdge pos (pos+1)) &&
      match ins.op with
      | .bra dst _ => keyPreservedEdge pos dst
      | .brx .. => false
      | _ => true)

set_option maxRecDepth 100000 in
private theorem keyCarryAudit :
    (((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907).all
      (fun (ins,pos) => keyCarryCode pos ins) = true := by kernel_rfl

private theorem keyCarryCheck {pos : Nat} {ins : Instr}
    (hLo : 1907 ≤ pos) (hHi : pos < 2768) (hOrd : pos ≠ keyBroadcast)
    (hc : kernel.code[pos]? = some ins) :
    (mmaWrites ins.op).contains 2600 = false ∧
      keyPreservedEdge pos (pos+1) = true ∧
      (match ins.op with
      | .bra dst _ => keyPreservedEdge pos dst
      | .brx .. => false
      | _ => true) = true := by
  let code := ((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907
  have hmem : (ins,pos) ∈ code := by
    apply List.mem_of_getElem? (i := pos-1907)
    dsimp only [code]
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hc]
    rfl
  have h := List.all_eq_true.mp (keyCarryAudit) (ins,pos) hmem
  simp only [keyCarryCode,beq_eq_false_iff_ne.mpr hOrd,Bool.false_or,Bool.and_eq_true,
    Bool.not_eq_true'] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

private theorem ordinaryKeyCarry {l : Launch} {X : Execution} {g pos : Nat} {s u : TState}
    {ev : Option Event} (hLo : 1907 ≤ s.pc) (hHi : s.pc < 2768)
    (hExcept : s.pc ≠ keyBroadcast) (hs : keyCarries l X g pos s)
    (hw : WStep kernel Assumptions.all l g s ev u)
    (hGet : ∀ e, ev = some e → X.get (g,pos) = some e) :
    keyCarries l X g (pos+if ev.isSome then 1 else 0) u := by
  intro hLive
  have hCheck {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :=
    keyCarryCheck hLo hHi hExcept hc
  have hKeep : u.regs 2600 =
      s.regs 2600 := by
    apply mmaStepReg (by omega) hHi _ hw
    intro ins hc
    simpa using (hCheck hc).1
  have hCore := out_eq_core (show 1904 ≤ s.pc by omega) hHi (l := l) (g := g) (t := s)
  have hEdge : keyPreservedEdge s.pc u.pc = true := by
    rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
    · have hTau : Tau kernel [] l g s u := by
        unfold Tau at ht ⊢
        rwa [← hCore]
      obtain ⟨ins,hGet⟩ := tau_core_has_code hTau
      rcases tau_core_frame hGet hTau with rfl | h
      · exact (hCheck hGet).2.1
      have hPc := h.pc
      cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
      case bra dst uni => simpa only [hOp,hPc] using (hCheck hGet).2.2
      case brx =>
        have hNo := (hCheck hGet).2.2
        simp only [hOp,Bool.false_eq_true] at hNo
      all_goals exact hPc.symm ▸ (hCheck hGet).2.1
    · obtain ⟨ins,hGet,_,_⟩ := estep_event_source he
      have heCore : EStep kernel [] l g s e (some u) := by
        obtain ⟨tm,hOut,hFire⟩ := he
        exact ⟨tm,hCore ▸ hOut,hFire⟩
      rcases (estep_return_pc heCore (fun _ _ _ h => execLocal_frame h)).2 with h | h
      · rw [h]
        simp [keyPreservedEdge]
      · exact h.symm ▸ (hCheck hGet).2.1
  have hSource : keyLive s.pc := by
    simpa [keyPreservedEdge,hLive] using hEdge
  rw [hKeep,(hs hSource).1]
  let offset := if ev.isSome then 1 else 0
  have hCursor : keyUse X g (pos+offset) = keyUse X g pos ∧
      keyRank X g (pos+offset) = keyRank X g pos := by
    rcases hw with ⟨rfl,_⟩ | ⟨e,rfl,hEvent⟩
    · simp [offset]
    · apply keyCursorThroughEvent (hGet e rfl)
      apply readyEventOutside 5
      have hPc := estep_source_pc hEvent
      have ⟨hMin,hMax⟩ := hSource
      change 2361 < s.pc at hMin
      change 2355 ≤ e.pc ∧ e.pc < 2524
      omega
  rw [hCursor.1,hCursor.2]
  exact ⟨rfl,(hs hSource).2⟩

private theorem keyBroadcastStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} (hWarp : warpIndex l g = 12)
    {s u : TState} {ev : Option Event} (hPc : s.pc = keyBroadcast)
    (hw : WStep kernel Assumptions.all l g s ev u)
    (hActual : ∀ e, ev = some e → X.get (g,index) = some e) :
    keyCarries l X g (index+if ev.isSome then 1 else 0) u := by
  have hc : kernel.code[s.pc]? = some ⟨none,
      .warp ⟨.shfl .idx,some (.int .b 32),[some 2600],
        [.reg 2592,.imm 0,.imm 31],some (.imm (-1))⟩⟩ := by
    rw [hPc]
    exact Flow.code_2361
  have hCore := out_eq_core (show 1904 ≤ s.pc by rw [hPc]; decide)
    (show s.pc < 2768 by rw [hPc]; decide) (l := l) (g := g) (t := s)
  rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · unfold Tau at ht
    rw [hCore] at ht
    exact (tau_core_not_event hc rfl ht).elim
  · obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hCode.symm.trans hc)
    obtain ⟨sent,b,c,recv,ok,rfl,rfl⟩ := fires_shfl (p := none) hFire
    have hGet := hActual _ rfl
    rw [hPc] at hGet
    have hValue := actualKeyDescriptorReceivedForReadyUse hp hX hWarp hGet
    have hCount := Thread.Mma.readyUsesAtPrefix hp hX (event_thread_lt hX hGet) hWarp index
    have hEven := (actualKeyDescriptorSentForReadyOrdinal hp hX hWarp hGet).2.2.2
    dsimp only at hValue hEven
    rw [← hCount] at hValue hEven
    intro _
    have hAfter := keyCursorThroughEvent hGet (show readyEvent ⟨2361, _⟩ = none from rfl)
    change (Function.update s.regs 2600 (some recv)) 2600 =
        some (b32 (keyDescriptorLow l (keyUse X g (index+1)))) ∧ keyUse X g (index+1) % 2 = 0 ∧
          2 ≤ keyUse X g (index+1) ∧ keyUse X g (index+1) = 2 * keyRank X g (index+1)
    rw [Function.update_self,hValue,hAfter.1,hAfter.2]
    exact ⟨rfl,hEven⟩

set_option maxRecDepth 100000 in
private theorem keyFrameExitFloor :
    (kernel.code.drop 2768).all (fun i => staysPastEvent 2768 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem keyFrameExitSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2768 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private abbrev outsideKeyPack (stage : Fin 2) (step : Fin 8) (pos : Nat) : Prop :=
  descriptorSetupOutside (qkSetupPc (recurringKeyBlock stage) 0-2)
    (qkPc (recurringKeyBlock stage)+step.val) pos

set_option maxRecDepth 100000 in
private theorem keyPackAudit (stage : Fin 2) (step : Fin 8) :
    (((kernel.code.drop 1907).take (2768-1907)).zipIdx 1907).all
      (fun (i,pos) => descriptorSetupStepCode (qkSetupPc (recurringKeyBlock stage) 0-2)
        (qkPc (recurringKeyBlock stage)+step.val) pos i) = true := by
  fin_cases stage <;> fin_cases step <;> kernel_rfl

private theorem leavesKeyIssue {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (stage : Fin 2) (step : Fin 8) (hPc : s.pc = qkPc (recurringKeyBlock stage)+step.val)
    (hw : WStep kernel Assumptions.all l g s e u) : outsideKeyPack stage step u.pc := by
  have hc : kernel.code[s.pc]? = some _ := hPc.symm ▸ qkCode (recurringKeyBlock stage) step
  right
  rcases hw with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hRange : 1904 ≤ qkPc (recurringKeyBlock stage)+step.val ∧
        qkPc (recurringKeyBlock stage)+step.val < 2768 := by
      fin_cases stage <;> fin_cases step <;> decide
    have hCore := out_eq_core (hPc.symm ▸ hRange.1) (hPc.symm ▸ hRange.2)
      (l := l) (g := g) (t := s)
    unfold Tau at ht
    rw [hCore] at ht
    rcases tau_core_frame hc ht with rfl | hFrame
    · exact hPc.symm ▸ Nat.lt_succ_self _
    · have h := hFrame.pc
      change u.pc = s.pc+1 ∨ False at h
      rw [h.resolve_right id,hPc]
      exact Nat.lt_succ_self _
  · obtain ⟨i,hCode,_,hFire⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hCode.symm.trans hc)
    rw [fires_tcMma (.inr (.inl rfl)) hFire]
    exact hPc.symm ▸ Nat.lt_succ_self _

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem keyPackedInWalk (stage : Fin 2) (step : Fin 8) {g : Nat}
    (hWarp : warpIndex l g = 12) {s : TState} {es : List Event} {vs : List Visit}
    (hs : 1907 ≤ s.pc ∧ s.pc < 2768) (hShape : RoleShape s ∧ s.regs 1062 = some (b32 12))
    (hOutside : outsideKeyPack stage step s.pc) {base index : Nat} (hF : keyCarries l X g base s)
    (hw : Walk kernel Assumptions.all l g s es vs) (hSuffix : es = (X.tr g).drop base)
    (hIndex : base ≤ index) {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hActual : X.get (g,index) =
      some ⟨qkPc (recurringKeyBlock stage)+step.val,.tc (.mma d op accum mask)⟩) :
    op.b = sharedDescriptor (kvStart l (keyUse X g index)+qkFragment step) 16 ∧
      keyUse X g index % 2 = 0 ∧ 2 ≤ keyUse X g index ∧
      keyUse X g index = 2 * keyRank X g index := by
  let block := recurringKeyBlock stage
  let target : Event := ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩
  let start := qkSetupPc block 0-2
  have hTarget : target.pc < 2768 := by
    change qkPc (recurringKeyBlock stage)+step.val < 2768
    fin_cases stage <;> fin_cases step <;> decide
  have hSetup : 2355 ≤ start ∧ start < target.pc ∧ keyLive start ∧ keyLive target.pc := by
    change 2355 ≤ qkSetupPc (recurringKeyBlock stage) 0-2 ∧
      qkSetupPc (recurringKeyBlock stage) 0-2 < qkPc (recurringKeyBlock stage)+step.val ∧
      keyLive (qkSetupPc (recurringKeyBlock stage) 0-2) ∧
      keyLive (qkPc (recurringKeyBlock stage)+step.val)
    fin_cases stage <;> fin_cases step <;> decide
  have getSuffix {tail : List Event} {pos : Nat} (hp : pos ≤ index)
      (hDrop : tail = (X.tr g).drop pos) : tail[index-pos]? = some target := by
    rwa [hDrop,List.getElem?_drop,Nat.add_sub_of_le hp]
  generalize hCount : vs.length = fuel
  induction fuel using Nat.strong_induction_on generalizing s es vs base with
  | h fuel ih =>
    have hMem := List.mem_of_getElem? (getSuffix hIndex hSuffix)
    have next {v u : TState} {ev : Option Event} {rest : List Event} {post : List Visit}
        {pos : Nat} (hShort : post.length < fuel)
        (hv : 1907 ≤ v.pc ∧ v.pc < 2768) (hRole : RoleShape v ∧ v.regs 1062 = some (b32 12))
        (hFr : keyCarries l X g pos v) (hPermit : outsideKeyPack stage step u.pc)
        (hStep : WStep kernel Assumptions.all l g v ev u)
        (hWalk : Walk kernel Assumptions.all l g u rest post)
        (hGet : ∀ e, ev = some e → X.get (g,pos) = some e)
        (hRest : rest = (X.tr g).drop (pos+if ev.isSome then 1 else 0))
        (hFound : pos+(if ev.isSome then 1 else 0) ≤ index) :
        op.b = sharedDescriptor (kvStart l (keyUse X g index)+qkFragment step) 16 ∧
          keyUse X g index % 2 = 0 ∧ 2 ≤ keyUse X g index ∧
          keyUse X g index = 2 * keyRank X g index := by
      obtain ⟨hBounds,hShape⟩ := mmaCutStep hv.1 hv.2 hStep hRole
      rcases hBounds with hIn | ⟨hExit,_⟩
      · have hNew : keyCarries l X g (pos+if ev.isSome then 1 else 0) u := by
          by_cases h : v.pc = keyBroadcast
          · exact keyBroadcastStep hp hX hWarp h hStep hGet
          · exact ordinaryKeyCarry hv.1 hv.2 h hFr hStep hGet
        exact ih post.length hShort hIn hShape hPermit hNew hWalk hRest hFound rfl
      · have hm := List.mem_of_getElem? (getSuffix hFound hRest)
        simp only [List.mem_singleton] at hExit
        exact (Nat.not_le_of_lt hTarget (eventTailEvents keyFrameExitFloor
          keyFrameExitSegments hWalk (show 2768 ≤ u.pc by omega) target hm)).elim
    by_cases hStart : s.pc = start
    · obtain ⟨hSlot,hEven⟩ := hF (hStart.symm ▸ hSetup.2.2.1)
      have hAt : At s start
          [(2600,b32 (keyDescriptorLow l (keyUse X g base))),(1062,b32 12)] :=
        ⟨hStart,hShape.1.2.2 (by rw [hStart]; have := hSetup.1; omega),hShape.1.2.1,
          normalBeforeLaterEvent hw hMem (by rw [hStart]; exact hSetup.2.1),
          hSlot,hShape.2,trivial⟩
      obtain ⟨v,rest,post,hPc,hReg,hWord,hRole,hLen,pre,hSplit,hWalk,_,hPre⟩ :=
        recurringKeyPrefixRanged hp stage step (keyUse X g base) hAt hw hMem rfl
      let pos := base+pre.length
      have hRest : rest = (X.tr g).drop pos := by
        rw [← List.drop_drop,← hSuffix,hSplit,List.drop_append_length]
      have hPos : pos ≤ index := by
        by_contra! hLate
        have hOff : index-base < pre.length := by dsimp [pos] at hLate; omega
        have hActual := getSuffix hIndex hSuffix
        rw [hSplit,List.getElem?_append_left hOff] at hActual
        have hIn := List.mem_of_getElem? hActual
        exact (Nat.lt_irrefl target.pc (hPre _ hIn).2)
      have hNone : pre.filterMap readyEvent = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro e he
        have ⟨hLo,hHi⟩ := hPre e he
        apply readyEventOutside 5
        change 2355 ≤ e.pc ∧ e.pc < 2524
        have hUpper : target.pc < 2524 := by
          change qkPc (recurringKeyBlock stage)+step.val < 2524
          fin_cases stage <;> fin_cases step <;> decide
        change start ≤ e.pc at hLo
        change e.pc < target.pc at hHi
        have := hSetup.1
        omega
      have hCursor : keyUse X g pos = keyUse X g base ∧
          keyRank X g pos = keyRank X g base :=
        keyCursorThroughPrefix (hSuffix.symm.trans hSplit) hNone
      have hV : 1907 ≤ v.pc ∧ v.pc < 2768 := by
        rw [hPc]
        change 1907 ≤ target.pc ∧ target.pc < 2768
        omega
      have hKeep : keyCarries l X g pos v := by
        intro _
        rw [hCursor.1,hCursor.2]
        exact ⟨hWord,hEven⟩
      cases hWalk with
      | stop => exfalso; simpa using getSuffix hPos hRest
      | tau ht hW =>
        have hStep : WStep kernel Assumptions.all l g _ none _ := .inl ⟨rfl,ht⟩
        exact next (pos := pos) (by simp at hLen; omega) hV hRole hKeep
          (leavesKeyIssue stage step hPc hStep) hStep hW (fun _ h => by cases h)
          (by simpa using hRest) (by simpa using hPos)
      | @ev t u e tail visits he hW =>
        have hGet : X.get (g,pos) = some e := by
          change (X.tr g)[pos]? = _
          rw [← Nat.add_zero pos,← List.getElem?_drop,← hRest,List.getElem?_cons_zero]
        by_cases hEq : pos = index
        · have hEv : e = target := Option.some.inj (hGet.symm.trans (hEq.symm ▸ hActual))
          subst e
          rw [← hEq,hCursor.1,hCursor.2]
          exact ⟨qkKeyDescriptorOfRegister hp block step _ hReg he,hEven⟩
        have hTail : tail = (X.tr g).drop (pos+1) := by rw [← List.drop_drop,← hRest]; rfl
        have hStep : WStep kernel Assumptions.all l g _ (some e) _ := .inr ⟨e,rfl,he⟩
        exact next (by simp at hLen; omega) hV hRole hKeep
          (leavesKeyIssue stage step hPc hStep) hStep hW
          (fun f h => Option.some.inj h ▸ hGet) hTail (by simp; omega)
      | last hLast =>
        have hTarget := List.mem_singleton.mp (List.mem_of_getElem? (getSuffix hPos hRest))
        obtain ⟨tm,_,hFires⟩ := hTarget.symm ▸ hLast
        rcases fires_none_ends hFires with ⟨_,h⟩ | h <;> cases h
    · have hSkip : s.pc ≠ target.pc := by
        change s.pc ≤ start ∨ target.pc < s.pc at hOutside
        omega
      cases hw with
      | stop => exfalso; simpa using getSuffix hIndex hSuffix
      | tau ht hW =>
        have hStep : WStep kernel Assumptions.all l g _ none _ := .inl ⟨rfl,ht⟩
        exact next (pos := base) (by simp at hCount; omega) hs hShape hF
          (ordinaryDescriptorSetupStep (keyPackAudit stage step) hs.1 hs.2 hOutside hStart hStep)
          hStep hW (fun _ h => by cases h) (by simpa using hSuffix) (by simpa using hIndex)
      | @ev t u e tail visits he hW =>
        have hGet : X.get (g,base) = some e := by
          change (X.tr g)[base]? = _
          rw [← Nat.add_zero base,← List.getElem?_drop,← hSuffix,List.getElem?_cons_zero]
        have hNe : base ≠ index := by
          intro hEq
          have hEv : e = target := Option.some.inj (hGet.symm.trans (hEq.symm ▸ hActual))
          exact hSkip ((estep_source_pc he).symm.trans (congrArg Event.pc hEv))
        have hTail : tail = (X.tr g).drop (base+1) := by rw [← List.drop_drop,← hSuffix]; rfl
        have hStep : WStep kernel Assumptions.all l g _ (some e) _ := .inr ⟨e,rfl,he⟩
        exact next (by simp at hCount; omega) hs hShape hF
          (ordinaryDescriptorSetupStep (keyPackAudit stage step) hs.1 hs.2 hOutside hStart hStep)
          hStep hW (fun f h => Option.some.inj h ▸ hGet) hTail (by simp; omega)
      | last hLast =>
        have hEq := List.mem_singleton.mp hMem
        exact (hSkip ((estep_source_pc hLast).symm.trans (congrArg Event.pc hEq.symm))).elim

/-- A recurring QK fragment uses the physical slot for twice the number of
successful key acquires reached on its issuing lane. -/
theorem QkInstruction.recurringKeyOperandOfReadyOrdinal (stage : Fin 2) {issue : EvId}
    {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X issue (recurringKeyBlock stage) step d op accum mask) :
    let d := Thread.Mma.atPrefix l X issue.1 issue.2
    let use := d.kvAcquires 0+d.kvAcquires 1+d.kvAcquires 2-1
    op.b = sharedDescriptor (kvStart l use + qkFragment step) 16 ∧ use % 2 = 0 ∧
      2 ≤ use ∧ use = 2 * Thread.Mma.readyOccurrence X issue.1 issue.2 .loopKey := by
  obtain ⟨g,index⟩ := issue
  let block := recurringKeyBlock stage
  let e : Event := ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩
  have hGet : X.get (g,index) = some e := hIssue.decoded
  have hR : 1907 < e.pc ∧ e.pc < 2768 ∧ e.pc ∉ registerHintSites := by
    change 1907 < qkPc block+step.val ∧ qkPc block+step.val < 2768 ∧
      qkPc block+step.val ∉ registerHintSites
    fin_cases stage <;> fin_cases step <;> decide
  have hRole := roleBodyPcOfEvent hp hX hGet (by omega) hR.2.2
  have hWarp : warpIndex l g = 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  obtain ⟨s,visits,hIndex,hs,hw,_,_,_⟩ := mmaRoleWalkOfDemand hp hX hGet hWarp (.inl hR.1)
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ by decide,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  have hOutside : outsideKeyPack stage step s.pc := by
    rw [hs.1]
    left
    fin_cases stage <;> decide
  have hInit : keyCarries l X g 6 s := by
    intro h
    rw [hs.1] at h
    exact (show ¬ keyLive 1908 from by decide) h |>.elim
  have hDescriptor := keyPackedInWalk hp hX stage step hWarp (by rw [hs.1]; decide) hShape
    hOutside hInit hw rfl hIndex hIssue.decoded
  have hUse := Thread.Mma.readyUsesAtPrefix hp hX (event_thread_lt hX hGet) hWarp index
  unfold keyUse at hDescriptor
  dsimp only at hUse ⊢
  rw [hUse] at hDescriptor
  exact hDescriptor

/-- Every recurring QK B descriptor uses a positive even position of the cache ring. -/
theorem QkInstruction.recurringKeyOperandOfPositiveEvenReadyUse (stage : Fin 2) {issue : EvId}
    {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X issue (recurringKeyBlock stage) step d op accum mask) :
    let d := Thread.Mma.atPrefix l X issue.1 issue.2
    let use := d.kvAcquires 0+d.kvAcquires 1+d.kvAcquires 2-1
    op.b = sharedDescriptor (kvStart l use + qkFragment step) 16 ∧ use % 2 = 0 ∧ 2 ≤ use := by
  obtain ⟨hDesc,hEven,hPositive,_⟩ := hIssue.recurringKeyOperandOfReadyOrdinal hp hX stage
  exact ⟨hDesc,hEven,hPositive⟩

/-- Every actual recurring QK B descriptor uses an even position of the ring. -/
theorem QkInstruction.recurringKeyOperandOfEvenReadyUse (stage : Fin 2) {issue : EvId}
    {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X issue (recurringKeyBlock stage) step d op accum mask) :
    let d := Thread.Mma.atPrefix l X issue.1 issue.2
    let use := d.kvAcquires 0+d.kvAcquires 1+d.kvAcquires 2-1
    op.b = sharedDescriptor (kvStart l use + qkFragment step) 16 ∧ use % 2 = 0 := by
  obtain ⟨hDesc,hEven,_⟩ := hIssue.recurringKeyOperandOfPositiveEvenReadyUse hp hX stage
  exact ⟨hDesc,hEven⟩

/-- A recurring QK B descriptor selects the latest successful ready use. -/
theorem QkInstruction.recurringKeyOperandOfReadyUse (stage : Fin 2) {issue : EvId} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X issue (recurringKeyBlock stage) step d op accum mask) :
    let d := Thread.Mma.atPrefix l X issue.1 issue.2
    let use := d.kvAcquires 0+d.kvAcquires 1+d.kvAcquires 2-1
    op.b = sharedDescriptor (kvStart l use + qkFragment step) 16 :=
  (hIssue.recurringKeyOperandOfEvenReadyUse hp hX stage).1

/-- The physical K descriptor and its last ready observation select one logical cache use. -/
theorem QkInstruction.recurringKeyReadyUseExact (stage : Fin 2) {g index : Nat} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask) :
    ∃ wait use,
      op.b = sharedDescriptor (kvStart l use+qkFragment step) 16 ∧
      Thread.Mma.ReadyPoll l X g wait (readyStage use) (readyWord use) true .cta ∧
      TraceBefore X (g,wait) (g,index) ∧
      (((X.tr g).take wait).filterMap readyEvent).length = use ∧
      use = (Thread.Mma.atPrefix l X g index).kvAcquires 0 +
        (Thread.Mma.atPrefix l X g index).kvAcquires 1 +
        (Thread.Mma.atPrefix l X g index).kvAcquires 2 - 1 := by
  have hm : X.MmaIssue (g,index) d op accum mask := ⟨_,hIssue.decoded⟩
  have hw := (mmaIssueElection hp hX hm).1
  have hg := event_thread_lt hX hIssue.decoded
  obtain ⟨_,prior,slot,phase,_,hPoll,hResume,_⟩ := Thread.Mma.actualMmaOperandReady hp hX hm
  obtain ⟨gate,hGate⟩ := hPoll.atGate hp hX hw
  have hBefore : prior < index := hResume.1.2.1
  let e : Event := ⟨readyHead gate,
    .wait (Thread.Mma.Observation.readyObject l g slot) phase true true .cta⟩
  have hGet : ((X.tr g).take index)[prior]? = some e := by
    rwa [List.getElem?_take_of_lt hBefore]
  have hMark : readyEvent e =
      some (Thread.Mma.Observation.readyObject l g slot,phase) := by
    have hSite : (List.finRange 4).any (fun i => readyHead i == readyHead gate) = true :=
      List.any_eq_true.mpr ⟨gate,by simp,beq_self_eq_true _⟩
    simp [readyEvent,e,hSite]
  have hPresent := List.mem_filterMap.mpr ⟨e,List.mem_of_getElem? hGet,hMark⟩
  let n := (((X.tr g).take index).filterMap readyEvent).length
  have hNonempty : 0 < n := List.length_pos_of_mem hPresent
  let use := n-1
  obtain ⟨j,hj,hReady,hOrdinal⟩ :=
    Thread.Mma.readyPollAtOrdinalBefore hp hX hg hw (stop := index) (use := use)
      (Nat.sub_lt hNonempty (by decide))
  have hDescriptor := hIssue.recurringKeyOperandOfReadyUse hp hX stage
  have hOrdinalEq := Thread.Mma.readyUsesAtPrefix hp hX hg hw index
  dsimp only at hDescriptor hOrdinalEq
  rw [← hOrdinalEq] at hDescriptor
  exact ⟨j,use,hDescriptor,hReady,⟨rfl,hj,len_of_get hIssue.decoded⟩,hOrdinal,
    congrArg (· - 1) hOrdinalEq⟩

/-- Every recurring QK issue uses a descriptor in the live three-slot key ring. -/
theorem QkInstruction.recurringKeyOperand (stage : Fin 2) {issue : EvId} {step : Fin 8} {d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X issue (recurringKeyBlock stage) step d op accum mask) :
    ∃ slot : Fin 3, op.b = sharedDescriptor (kvStart l slot.val+qkFragment step) 16 := by
  let d := Thread.Mma.atPrefix l X issue.1 issue.2
  let use := d.kvAcquires 0+d.kvAcquires 1+d.kvAcquires 2-1
  refine ⟨readyStage use,?_⟩
  have hr := hIssue.recurringKeyOperandOfReadyUse hp hX stage
  have hSlot : kvSlot (readyStage use).val = kvSlot use := by
    change (use%3)%3 = use%3
    omega
  simpa only [kvStart,hSlot] using hr

/-- Both the initial and recurring QK banks use an encoded key ring descriptor. -/
theorem QkInstruction.keyOperand {issue : EvId} {block : Fin 4} {step : Fin 8} {d : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X issue block step d op accum mask) :
    ∃ use, op.b = sharedDescriptor (kvStart l use+qkFragment step) 16 := by
  fin_cases block
  · exact ⟨0,hIssue.initialKeyOperand hp hX 0⟩
  · exact ⟨0,hIssue.initialKeyOperand hp hX 1⟩
  · obtain ⟨slot,h⟩ := hIssue.recurringKeyOperand hp hX 0
    exact ⟨slot.val,h⟩
  · obtain ⟨slot,h⟩ := hIssue.recurringKeyOperand hp hX 1
    exact ⟨slot.val,h⟩

/-- Every actual QK B byte, including in recurring banks, belongs to its CTA's key ring. -/
theorem QkInstruction.keyByteBank {issue : EvId} {block : Fin 4} {step : Fin 8} {d index : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {loc : Loc}
    (hIssue : QkInstruction X issue block step d op accum mask)
    (hByte : op.byteLoc .b index = some loc) :
    SharedOperandRange l issue.1 loc ∧ l.sharedBase + 68608 ≤ loc.addr := by
  have hQ := hIssue.queryOperand hp hX
  obtain ⟨use,hB⟩ := hIssue.keyOperand hp hX
  have hSame : op.byteLoc .b index = (qkOperands l issue.1 block step use).byteLoc .b index := by
    simp only [TcMma.OperandSpec.byteLoc,qkOperands,hQ.descriptor,hQ.ctaLow,hQ.ctaHigh,
      hB,reduceCtorEq,false_and,↓reduceIte]
    rfl
  obtain ⟨hRange,hLower,_⟩ :=
    qkOperandBankRange hp issue.1 block step use (hSame.symm.trans hByte)
  exact ⟨hRange, by simp only [qkInputStart, kvStart] at hLower; omega⟩

/-- The actual key byte lies within its CTA data banks. -/
theorem QkInstruction.keyByteRange {issue : EvId} {block : Fin 4} {step : Fin 8} {d index : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} {loc : Loc}
    (hIssue : QkInstruction X issue block step d op accum mask)
    (hByte : op.byteLoc .b index = some loc) : SharedOperandRange l issue.1 loc :=
  (hIssue.keyByteBank hp hX hByte).1

end
end PTX.Kernels.TmlFa4Fwd.Thread
