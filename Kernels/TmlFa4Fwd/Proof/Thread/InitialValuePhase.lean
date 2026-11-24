-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperandReply
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveAnchor
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
import Kernels.TmlFa4Fwd.Proof.MmaValueAnchorBroadcast
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Kernels.TmlFa4Fwd.Proof.MmaElect
import Lemmas.Flow.NotShfl
import Lemmas.Order.ElectOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (RoleShape electSite electTemplate electStateFrame
  initialKeyCursor initialMmaTrace initialValueAnchorFromKey initialValueBroadcastFromAnchor
  kvStart mmaWrites pvFragment pvRoleAfterEventFramed readyEvent readyFrame readyHead
  valueAnchorShuffle valueBroadcastReached valueDescriptorEvent valueDescriptorLow
  valueDescriptorSite sharedDescriptor)
open Mma.Observation (readyObject)

noncomputable section

private structure InitialValueAnchor (l : Launch) (X : Execution) (g : Nat) where
  index : Nat
  instanceId : Nat
  leader : Nat
  state : TState
  visits : List Visit
  observed : X.Elect (g,index) 2271 (2^32-1) instanceId leader
  atState : At state 2272 (readyFrame l)
  suffix : Walk kernel Assumptions.all l g state ((X.tr g).drop (index+1)) visits

private theorem readyProjection (gate : Fin 4) (loc : Loc) (parity : Nat) :
    readyEvent ⟨readyHead gate, .wait loc parity true true .cta⟩ = some (loc, parity) := by
  have h : (List.finRange 4).any (fun i => readyHead i == readyHead gate) = true :=
    List.any_eq_true.mpr ⟨gate, by simp, beq_self_eq_true _⟩
  simp [readyEvent,h]

private theorem anchorBeforeSecondOutput {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X (g,j) spec) :
    ∃ a : InitialValueAnchor l X g,
      0 < (((X.tr g).take a.index).filterMap readyEvent).length := by
  let target : Event := ⟨2646,.tc (.commit spec)⟩
  have hCommitGet : X.get (g,j) = some target := hCommit.decoded
  have hw : warpIndex l g = 12 := by
    have hBody := roleBodyPcOfEvent hp hX hCommitGet (show 173 < 2646 by decide)
      (show 2646 ∉ registerHintSites by decide)
    change roleBodyPc (warpIndex l g) 2646 at hBody
    unfold roleBodyPc at hBody
    rcases hBody with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨value,hv,hvOrder,hvOrd⟩ := initialValueAcquireBeforeSecondOutputCommit hp hX hCommit
  have hValueBefore : value < j := hvOrder.2.1
  have hBefore : 0 < (((X.tr g).take value).filterMap readyEvent).length := by
    change (((X.tr g).take value).filterMap readyEvent).length = 1 at hvOrd
    omega
  obtain ⟨key,hKeyBefore,hk,_⟩ :=
    Mma.readyPollAtOrdinalBefore hp hX (event_thread_lt hX hCommitGet) hw hBefore
  obtain ⟨keyGate,hKey⟩ := hk.atGate hp hX hw
  obtain ⟨valueGate,hValue⟩ := hv.atGate hp hX hw
  have hKeyLo : 2145 ≤ readyHead keyGate := by fin_cases keyGate <;> decide
  have hKeyHi : readyHead keyGate < 2768 := by fin_cases keyGate <;> decide
  obtain ⟨base,s,_,hBase,hs,hWalk⟩ := initialMmaTrace hp hX hKey hKeyLo hKeyHi
  let es := (X.tr g).drop (base+1)
  have hAt {i : Nat} {e : Event} (hg : X.get (g,i) = some e) (hi : base+1 ≤ i) :
      es[i-(base+1)]? = some e := by
    dsimp only [es]
    rwa [List.getElem?_drop, Nat.add_sub_of_le hi]
  have hTwo : 1 < ((es.take (j-(base+1))).filterMap readyEvent).length :=
    twoReadyProjections (hAt hKey (by omega)) (hAt hValue (by omega)) (by omega) (by omega)
      (readyProjection keyGate _ _) (readyProjection valueGate _ _)
  obtain ⟨suffix,hTake⟩ := List.take_prefix (j-(base+1)) es
  have hAll : 1 < (es.filterMap readyEvent).length := by
    rw [← hTake,List.filterMap_append,List.length_append]
    omega
  have hs' : At s 1908 (readyFrame l) :=
    hs.mono ⟨hs.2.2.2.2.2.1,hs.2.2.2.2.1,trivial⟩
  obtain ⟨t,pre,rest,visits,hSplit,hK,ht,htWalk⟩ := initialKeyCursor hp hs' hWalk hAll
  change es = pre++rest at hSplit
  have hEarly : pre.length < j-(base+1) := by
    by_contra! h
    rw [hSplit,List.take_append_of_le_length h] at hTwo
    obtain ⟨endPre,hEnd⟩ := List.take_prefix (j-(base+1)) pre
    have hLength := congrArg (fun e => (e.filterMap readyEvent).length) hEnd
    simp only [List.filterMap_append,List.length_append,hK,List.length_singleton] at hLength
    omega
  have hRest : target ∈ rest := by
    have h := hAt hCommitGet (by omega)
    rw [hSplit,List.getElem?_append_right hEarly.le] at h
    exact List.mem_of_getElem? h
  obtain ⟨inst,leader,u,pre',tail,post,hAnchor,hu,huWalk,_⟩ :=
    initialValueAnchorFromKey ht htWalk hRest (show 2271 < 2646 by decide)
  let anchor : Event := ⟨2271,.elect (2^32-1) inst leader⟩
  let offset := (pre++pre').length
  have hEvent : es = (pre++pre') ++ anchor :: tail := by
    simp [hSplit,hAnchor,anchor,List.append_assoc]
  have hAnchorAt : es[offset]? = some anchor := by
    dsimp only [offset]
    rw [hEvent,List.getElem?_append_right le_rfl,Nat.sub_self]
    rfl
  have hObserved : X.Elect (g,base+1+offset) 2271 (2^32-1) inst leader := by
    rw [show es = (X.tr g).drop (base+1) from rfl,List.getElem?_drop] at hAnchorAt
    change (X.tr g)[base+1+offset]? = some anchor
    exact hAnchorAt
  have hDrop : (X.tr g).drop (base+1+offset+1) = tail := by
    rw [← List.drop_drop, ← List.drop_drop]
    change (es.drop offset).drop 1 = tail
    dsimp only [offset]
    rw [hEvent,List.drop_append_length]
    rfl
  refine ⟨⟨_,inst,leader,u,post,hObserved,hu,hDrop.symm ▸ huWalk⟩,?_⟩
  let body := (X.tr g).take (base+1) ++ pre ++ pre'
  have hLen : body.length = base+1+offset := by
    have hKeyBound : key < (X.tr g).length := (List.getElem?_eq_some_iff.mp hKey).1
    simp [body,offset,List.length_take_of_le (by omega : base+1 ≤ (X.tr g).length),Nat.add_assoc]
  have hFull : X.tr g = body ++ anchor :: tail := by
    rw [← List.take_append_drop (base+1) (X.tr g)]
    change (X.tr g).take (base+1) ++ es = _
    simp [hEvent,body,List.append_assoc]
  change 0 < (((X.tr g).take (base+1+offset)).filterMap readyEvent).length
  rw [← hLen,hFull,List.take_append_length]
  simp [body,List.filterMap_append,hK]

private theorem anchorContinuation {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j inst leader : Nat} (he : X.Elect (g,j) 2271 (2^32-1) inst leader)
    (hMore : j+1 < (X.tr g).length) :
    ∃ a : InitialValueAnchor l X g, a.index = j := by
  let anchor : Event := ⟨2271,.elect (2^32-1) inst leader⟩
  obtain ⟨base,s,_,hBase,hs,hWalk⟩ :=
    initialMmaTrace hp hX he (show 2145 ≤ 2271 by decide) (show 2271 < 2768 by decide)
  let es := (X.tr g).drop (base+1)
  have hGet : es[j-(base+1)]? = some anchor := by
    dsimp only [es]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  have hLength : j-(base+1)+1 < es.length := by
    rw [show es = (X.tr g).drop (base+1) from rfl,List.length_drop]
    omega
  have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  have hAudit : ((kernel.code.drop 1907).take (2768-1907)).all
      (fun i => [2535].all (fun r => !(mmaWrites i.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t,u,post,hFire,hUShape,hF,hUWalk⟩ :=
    pvRoleAfterEventFramed (F := [(2535,b32 l.sharedBase)]) hAudit hWalk
      (by rw [hs.1]; decide) hShape ⟨hs.2.2.2.2.2.1,trivial⟩ hGet hLength
      (show 2271 < 2768 by decide)
  have hState : u.pc = 2272 ∧ u.fault = none := by
    have ht : t.pc = 2271 := (estep_source_pc hFire).symm
    have htFault : t.fault = none := by
      cases hf : t.fault with
      | none => rfl
      | some fault =>
        obtain ⟨tm,hOut,hFires⟩ := hFire
        simp only [out,hf,Out.ev.injEq] at hOut
        subst tm
        cases hFires.2
    obtain ⟨i,hCode,_,hFires⟩ := estep_event_source hFire
    rw [ht,Flow.code_2271] at hCode
    obtain rfl := Option.some.inj hCode
    obtain ⟨_,_,_,_,hu⟩ := fires_elect hFires
    rw [hu]
    exact ⟨by simpa [next,setReg] using ht,
      by simpa [next,setReg] using htFault⟩
  have hShift : es.drop (j-(base+1)+1) = (X.tr g).drop (j+1) := by
    simp only [es,List.drop_drop]
    rw [show base+1+(j-(base+1)+1) = j+1 by omega]
  have hu : At u 2272 (readyFrame l) :=
    ⟨hState.1,hUShape.1.2.2 (by rw [hState.1]; decide),hUShape.1.2.1,
      hState.2,hF.1,hUShape.2,trivial⟩
  exact ⟨⟨j,inst,leader,u,post,he,hu,hShift ▸ hUWalk⟩,rfl⟩

set_option maxRecDepth 100000 in
private theorem valueAnchorTail :
    (kernel.code.drop 2272).all (fun i => staysPastEvent 2272 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem valueAnchorSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (2272 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem codeNoShuffle {lo hi pc : Nat} {i : Instr}
    (hAudit : ((kernel.code.drop lo).take (hi-lo)).all (fun i => !i.op.isShfl) = true)
    (hPc : lo ≤ pc ∧ pc < hi) (hCode : kernel.code[pc]? = some i) : i.op.isShfl = false := by
  have hGet : ((kernel.code.drop lo).take (hi-lo))[pc-lo]? = some i := by
    rw [List.getElem?_take_of_lt (by omega),List.getElem?_drop,Nat.add_sub_of_le hPc.1,hCode]
  have h := List.all_eq_true.mp hAudit i (List.mem_of_getElem? hGet)
  simpa using h

private theorem decodedAnchorShuffle {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {id : EvId} {e : Event}
    (he : X.get id = some e) (hFloor : 2272 ≤ e.pc) :
    valueAnchorShuffle e = if Execution.isShfl e then some e else none := by
  by_cases hs : Execution.isShfl e = true
  · have hMark : 2307 ≤ e.pc ∧ e.pc < 2534 ∨ 2558 ≤ e.pc := by
      obtain ⟨f,hf⟩ | ⟨t,i,o,_,hCode,hFire⟩ := get_source hX he
      · cases e
        simp_all [Execution.isShfl]
      have hShuffle := fires_shfl_op hFire hs
      by_contra! h
      by_cases hi : e.pc < 2307
      · have hAudit : ((kernel.code.drop 2272).take (2307-2272)).all
            (fun i => !i.op.isShfl) = true := by
          set_option maxRecDepth 100000 in kernel_rfl
        rw [codeNoShuffle hAudit ⟨hFloor,hi⟩ hCode] at hShuffle
        cases hShuffle
      · have hRange : 2534 ≤ e.pc ∧ e.pc < 2558 := by omega
        have hAudit : ((kernel.code.drop 2534).take (2558-2534)).all
            (fun i => !i.op.isShfl) = true := by
          set_option maxRecDepth 100000 in kernel_rfl
        rw [codeNoShuffle hAudit hRange hCode] at hShuffle
        cases hShuffle
    simp [valueAnchorShuffle,hMark,hs]
  · simp [valueAnchorShuffle,hs]

private theorem countAnchorShuffle {es : List Event}
    (h : ∀ e ∈ es, valueAnchorShuffle e = if Execution.isShfl e then some e else none) :
    (es.filterMap valueAnchorShuffle).length = es.countP Execution.isShfl := by
  rw [List.countP_eq_length_filter, ← List.filterMap_eq_filter]
  congr 1
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.filterMap_cons,h e List.mem_cons_self]
    rw [ih (fun e he => h e (List.mem_cons_of_mem _ he))]
    rfl

private theorem InitialValueAnchor.projectedCount {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (a : InitialValueAnchor l X g) {es : List Event}
    (hSub : ∀ e ∈ es, e ∈ (X.tr g).drop (a.index+1)) :
    (es.filterMap valueAnchorShuffle).length = es.countP Execution.isShfl := by
  apply countAnchorShuffle
  intro e he
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp (hSub e he)
  rw [List.getElem?_drop] at hi
  exact decodedAnchorShuffle hX (id := (g,a.index+1+i)) hi
    (eventTailEvents valueAnchorTail valueAnchorSegments a.suffix (by rw [a.atState.1])
      e (hSub e he))

private theorem InitialValueAnchor.observationRank {l : Launch} {X : Execution} {g : Nat}
    (a : InitialValueAnchor l X g) :
    ((X.tr g).take (a.index+1)).countP Execution.isShfl =
      ((X.tr g).take a.index).countP Execution.isShfl := by
  have he : (X.tr g)[a.index]? = some ⟨2271,.elect (2^32-1) a.instanceId a.leader⟩ :=
    a.observed
  rw [List.take_add_one,he,Option.toList_some,List.countP_append]
  simp [Execution.isShfl]

private theorem InitialValueAnchor.replay {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (a : InitialValueAnchor l X g)
    (hReached : valueBroadcastReached ((X.tr g).drop (a.index+1))) :
    ∃ steady i recv ok u post,
      X.get (g,i) = some (valueDescriptorEvent l steady recv ok) ∧
      X.ShflK (g,i) (((X.tr g).take a.index).countP Execution.isShfl+1) ∧
      At u ((valueDescriptorSite steady).prepare+9)
        [((valueDescriptorSite steady).output,recv),(1062,b32 12)] ∧
      Walk kernel Assumptions.all l g u ((X.tr g).drop (i+1)) post ∧
      (((X.tr g).take a.index).filterMap readyEvent).length <
        (((X.tr g).take i).filterMap readyEvent).length := by
  obtain ⟨steady,recv,ok,pre,prob,tail,u,post,hSplit,hPre,hProb,hu,hWalk,hReady⟩ :=
    initialValueBroadcastFromAnchor hp a.atState a.suffix hReached
  let es := (X.tr g).drop (a.index+1)
  let before := pre++[prob]
  let i := a.index+1+before.length
  have hSep : es = before ++ valueDescriptorEvent l steady recv ok :: tail := by
    simpa [before,List.append_assoc] using hSplit
  have hGetRel : es[before.length]? = some (valueDescriptorEvent l steady recv ok) := by
    rw [hSep,List.getElem?_append_right le_rfl,Nat.sub_self]
    rfl
  have hGet : X.get (g,i) = some (valueDescriptorEvent l steady recv ok) := by
    rw [show es = (X.tr g).drop (a.index+1) from rfl,List.getElem?_drop] at hGetRel
    exact hGetRel
  have hCount : before.countP Execution.isShfl = 1 := by
    rw [← a.projectedCount hX (es := before) (fun e he => by
      change e ∈ es
      rw [hSep]
      exact List.mem_append_left _ he)]
    simp [before,hPre,hProb]
  have hALt : a.index < (X.tr g).length := ElectOrd.lt_len a.observed
  have hTaken : (X.tr g).take i = (X.tr g).take (a.index+1) ++ before := by
    have hWhole : (X.tr g).take (a.index+1) ++
        (before ++ valueDescriptorEvent l steady recv ok :: tail) = X.tr g := by
      rw [← hSep]
      exact List.take_append_drop _ _
    have hIndex : i = ((X.tr g).take (a.index+1) ++ before).length := by
      simp [i,List.length_take_of_le (by omega : a.index+1 ≤ (X.tr g).length)]
    calc
      (X.tr g).take i =
          (((X.tr g).take (a.index+1) ++ before) ++
            valueDescriptorEvent l steady recv ok :: tail).take i := by
        rw [List.append_assoc,hWhole]
      _ = _ := by simpa only [hIndex] using List.take_append_length
  have hOrder : X.ShflK (g,i) (((X.tr g).take a.index).countP Execution.isShfl+1) := by
    refine ⟨⟨_,.idx,b32 (valueDescriptorLow l 1),0,31,recv,ok,hGet⟩,?_⟩
    change ((X.tr g).take i).countP Execution.isShfl = _
    rw [hTaken,List.countP_append,a.observationRank,hCount]
  have hRest : (X.tr g).drop (i+1) = tail := by
    change (X.tr g).drop (a.index+1+before.length+1) = tail
    rw [← List.drop_drop, ← List.drop_drop]
    change (es.drop before.length).drop 1 = tail
    rw [hSep,List.drop_append_length]
    rfl
  refine ⟨steady,i,recv,ok,u,post,hGet,hOrder,hu,hRest.symm ▸ hWalk,?_⟩
  have hMono : (((X.tr g).take a.index).filterMap readyEvent).length ≤
      (((X.tr g).take (a.index+1)).filterMap readyEvent).length := by
    have he : (X.tr g)[a.index]? = some ⟨2271,.elect (2^32-1) a.instanceId a.leader⟩ :=
      a.observed
    simp [List.take_add_one,he,readyEvent]
  rw [hTaken,List.filterMap_append,List.length_append]
  have hNonzero : 0 < (before.filterMap readyEvent).length := by
    exact hReady.trans_le (by simp [before,List.filterMap_append])
  omega

set_option maxRecDepth 100000 in
private theorem outputCommitTail :
    (kernel.code.drop 2646).all (fun i => staysPastEvent 2646 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem outputCommitSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (2646 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem ownerReached {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    (a : InitialValueAnchor l X g) (c : InitialValueReplyCursor l X (g,j)) :
    valueBroadcastReached ((X.tr g).drop (a.index+1)) := by
  let e := valueDescriptorEvent l c.steady c.word c.valid
  have hPc : 2272 ≤ e.pc ∧ e.pc ≠ 2307 ∧ e.pc ≠ 2558 := by
    cases h : c.steady <;> simp [e,valueDescriptorEvent,h,valueDescriptorSite]
  have hAfter : a.index < c.index :=
    traceOrderOfPcFloor hX valueAnchorTail valueAnchorSegments a.observed c.send
      (show 2271 < 2272 by decide) hPc.1
  have hGet : ((X.tr g).drop (a.index+1))[c.index-(a.index+1)]? = some e := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hAfter]
    exact c.send
  have hMarked := decodedAnchorShuffle hX c.send hPc.1
  have hMark : valueAnchorShuffle e = some e := by
    simpa [e,valueDescriptorEvent,Execution.isShfl] using hMarked
  exact .inr ⟨e,List.mem_filterMap.mpr ⟨e,List.mem_of_getElem? hGet,hMark⟩,hPc.2⟩

/-- The actual initial value broadcast receives lane zero's descriptor of physical
slot one. This holds even if the two lanes reach it through different paths. -/
theorem initialValueMatchedReplyWithAcquire {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec) :
    ∃ c : InitialValueReplyCursor l X commit, c.word = b32 (valueDescriptorLow l 1) ∧
      ∃ wait, Mma.ReadyPoll l X commit.1 wait 1 0 true .cta ∧
        TraceBefore X (commit.1,wait) (commit.1,c.index) ∧
        (((X.tr commit.1).take wait).filterMap readyEvent).length = 1 := by
  obtain ⟨g,j⟩ := commit
  obtain ⟨owner,hFirst⟩ := anchorBeforeSecondOutput hp hX hCommit
  obtain ⟨original⟩ := initialValueReplyBeforeSecondOutputCommit hp hX hCommit
  obtain ⟨steady,i,word,ok,u,visits,hGet,hRank,hu,hUWalk,hEarlierReady⟩ :=
    owner.replay hp hX (ownerReached hX owner original)
  have hSend : InitialValueDescriptorSend l X (g,i) word ok := ⟨steady,hGet⟩
  let peer := g-laneOf l g
  let rank := ((X.tr g).take owner.index).countP Execution.isShfl
  obtain ⟨hWarp,_⟩ := laneZero_sameWarp (show 0 < l.block by rw [hp.block]; decide)
    (event_thread_lt hX hGet)
  have hMember : electMember (2^32-1) (laneOf l peer) := by
    refine ⟨Nat.mod_lt _ (by decide),?_⟩
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (Nat.mod_lt _ (by decide))
  obtain ⟨k,hPartner⟩ := ElectOrd.partner hX hWarp owner.observed hMember
  have hCount : ((X.tr peer).take k).countP Execution.isShfl = rank :=
    (shuffleCountAtMatchedElection hX hWarp hPartner).symm
  obtain ⟨pc,pc',mask,mask',inst,lead,lead',hHere,hPeer⟩ := hPartner
  have hHereFixed : pc = 2271 ∧ mask = 2^32-1 := by
    have h := Option.some.inj (hHere.symm.trans owner.observed)
    exact ⟨congrArg Event.pc h, by
      have hk := congrArg Event.kind h
      injection hk⟩
  have ⟨hSamePc,hSameMask,_⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hHere hPeer hWarp
  have hMatched : X.Elect (peer,k) 2271 (2^32-1) inst lead' := by
    rw [← hHereFixed.1,← hHereFixed.2,hSamePc,hSameMask]
    exact hPeer
  obtain ⟨peerIndex,hPeerRank,_⟩ := hSend.actualLaneZeroWord hp hX hRank
  have hPeerAfter : k < peerIndex := by
    by_contra! h
    have hMono := countP_take_mono Execution.isShfl (X.tr peer) h
    have hOrdinal : ((X.tr peer).take peerIndex).countP Execution.isShfl = rank+1 := hPeerRank.2
    omega
  obtain ⟨peerAnchor,hPeerIndex⟩ := anchorContinuation hp hX hMatched
    (by have hLen : peerIndex < (X.tr peer).length := hPeerRank.lt; omega)
  have hPeerCount :
      1 < (((X.tr peer).drop (peerAnchor.index+1)).filterMap valueAnchorShuffle).length := by
    rw [peerAnchor.projectedCount hX (fun e he => he)]
    have hBefore := peerAnchor.observationRank
    rw [hPeerIndex,hCount] at hBefore
    have hFull := congrArg (fun es => es.countP Execution.isShfl)
      (List.take_append_drop (peerAnchor.index+1) (X.tr peer))
    have hTotal : rank+1 < (X.tr peer).countP Execution.isShfl := Step.ShflK.lt_count hPeerRank
    simp only [List.countP_append,hPeerIndex,hBefore] at hFull ⊢
    omega
  obtain ⟨peerSteady,peerSend,peerWord,peerOk,_,_,hPeerGet,hPeerOrder,_,_,_⟩ :=
    peerAnchor.replay hp hX (.inl hPeerCount)
  rw [hPeerIndex,hCount] at hPeerOrder
  have hWord := hSend.receivesFromLaneZero hX
    (show InitialValueDescriptorSend l X (peer,peerSend) peerWord peerOk from ⟨peerSteady,hPeerGet⟩)
    hRank hPeerOrder
  have hBefore : i < j :=
    traceOrderOfPcFloor hX outputCommitTail outputCommitSegments hGet hCommit.decoded
      (by cases steady <;> simp [valueDescriptorEvent,valueDescriptorSite])
      (show 2646 ≤ 2646 by decide)
  have hw : warpIndex l g = 12 := by
    have hBody := roleBodyPcOfEvent hp hX hCommit.decoded (show 173 < 2646 by decide)
      (show 2646 ∉ registerHintSites by decide)
    change roleBodyPc (warpIndex l g) 2646 at hBody
    unfold roleBodyPc at hBody
    rcases hBody with h | h
    · omega
    · split_ifs at h <;> omega
  have hg : g < l.threads := event_thread_lt hX hGet
  obtain ⟨wait,hWait,hPoll,hOrdinal⟩ :=
    Mma.readyPollAtOrdinalBefore hp hX hg hw (stop := i) (use := 1) (by omega)
  exact ⟨⟨steady,i,word,ok,u,visits,hGet,
    ⟨rfl,hBefore,(List.getElem?_eq_some_iff.mp hCommit.decoded).1⟩,hu,hUWalk⟩,hWord,
    wait,hPoll,⟨rfl,hWait,(List.getElem?_eq_some_iff.mp hGet).1⟩,hOrdinal⟩

/-- The actual initial V reply before O1 is the physical slot-one descriptor. -/
theorem initialValueMatchedReplyBeforeSecondOutputCommit {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec) :
    ∃ c : InitialValueReplyCursor l X commit, c.word = b32 (valueDescriptorLow l 1) := by
  obtain ⟨c,hWord,_⟩ := initialValueMatchedReplyWithAcquire hp hX hCommit
  exact ⟨c,hWord⟩

/-- Every fragment in both actual initial PV groups uses the physical slot-one B operand. -/
theorem initialValueIssuesBeforeSecondOutputCommitExact {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec) :
    ∃ steady, ∀ stage : Fin 2, ∀ fragment : Fin 8,
      ∃ issue dst operands accum mask,
        InitialValueFragment X issue steady stage fragment dst operands accum mask ∧
        X.MmaIssue issue dst operands accum mask ∧
        operands.b = sharedDescriptor (kvStart l 1 + pvFragment fragment) 16384 ∧
        TraceBefore X issue commit := by
  obtain ⟨cursor,hWord⟩ := initialValueMatchedReplyBeforeSecondOutputCommit hp hX hCommit
  refine ⟨cursor.steady,?_⟩
  intro stage fragment
  obtain ⟨i,dst,op,accum,mask,hIssue,hB,_,hOrder⟩ :=
    cursor.actualValueFragmentB hp hX hCommit hWord stage fragment
  exact ⟨i,dst,op,accum,mask,hIssue,⟨_,hIssue⟩,hB,hOrder⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
