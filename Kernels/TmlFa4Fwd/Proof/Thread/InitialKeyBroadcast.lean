-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveAnchor
public import Kernels.TmlFa4Fwd.Proof.MmaQkBroadcast
import Kernels.TmlFa4Fwd.Proof.MmaInitialValueCursor
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
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
import Lemmas.Order.ElectOrdinal
import Lemmas.Flow.WarpScan
import Lemmas.Flow.PollRendezvous

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (RoleShape dispatchWarp12 startupFacts readyInterval
  requireReadyIntervalWith requireReadySegmentNonempty pvCutCode pvWalkCut pvWalkEvent
  normalBeforeLaterEvent firstKeyWordLocal firstKLow laneZeroBroadcast out_eq_core localRun
  startupOut_eq_nil electSite electTemplate walkFromRun firstQkElectionBeforeFinalCommit
  advanceWalkLocals)

noncomputable section

private def keyEntryFacts (l : Launch) : List (Nat × Value) :=
  [(1178,b32 (l.sharedBase+68608)),(1062,b32 12)]

private theorem keyEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index inst leader : Nat} (he : X.Elect (g,index) 2153 (2^32-1) inst leader) :
    ∃ t visits, 5 < index ∧ At t 1908 (keyEntryFacts l) ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop 6) visits := by
  have hg := event_thread_lt hX he
  have hw : warpIndex l g = 12 := by
    have hSite := roleBodyPcOfEvent hp hX he (show 173 < 2153 by decide)
      (show 2153 ∉ registerHintSites by decide)
    change roleBodyPc (warpIndex l g) 2153 at hSite
    unfold roleBodyPc at hSite
    rcases hSite with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨t,_,hIndex,ht,hRun⟩ :=
    nonzeroCommonPrefixOfLateEvent hp hX hg (show 0 < warpIndex l g by omega)
      he (show 173 < 2153 by decide)
  have hi : index < (X.tr g).length := ElectOrd.lt_len he
  have hNonempty : (X.tr g).drop 5 ≠ [] :=
    fun h => Nat.not_le_of_lt hi ((List.drop_eq_nil_iff.mp h).trans hIndex)
  have ht' : At t 174 (startupFacts p l) := ht.mono (by
    refine ⟨?_,?_,?_,?_,?_,?_,trivial⟩ <;> apply holds_mem ht.2.2.2.2 <;>
      simp [nonzeroBarrierFacts,abiFacts,hw])
  obtain ⟨s,hLocal,hs⟩ := dispatchWarp12 hp hg ht'
  have hOut : out kernel [] l g s = .ev (.setMaxReg false 80 (next s)) := by
    unfold out
    rw [hs.1,hs.2.2.2.1,Flow.code_1907]
    rfl
  have hNext : Next kernel Assumptions.all l g t s (.setMaxReg false 80 (next s)) :=
    ⟨run_rtg hLocal,(startupOut_eq_nil (by rw [hs.1]; decide)
      (by rw [hs.1]; decide)).trans hOut⟩
  obtain ⟨e,u,hGet,hFire,hSuffix⟩ := hNext.continuing_at_nonempty
    (by rintro e ⟨w,he,hn⟩; cases hn) hRun hNonempty
  obtain ⟨inst',rfl,hAfter⟩ := hFire
  obtain rfl := Option.some.inj hAfter
  have hBefore : 5 < index := by
    by_contra! hn
    have hEq : index = 5 := by omega
    subst index
    have hPc := congrArg Event.pc (Option.some.inj (hGet.symm.trans he))
    change s.pc = 2153 at hPc
    exact (by decide : (1907 : Nat) ≠ 2153) (hs.1.symm.trans hPc)
  obtain ⟨visits,hWalk⟩ := walkFromRun hSuffix
  refine ⟨_,visits,hBefore,hs.next.mono ?_,hWalk⟩
  exact ⟨hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1,trivial⟩

private def anchorObservation (e : Event) : Option Event :=
  if e.pc = 2153 then some e else none

set_option maxRecDepth 100000 in
private theorem keyAnchorTail :
    (kernel.code.drop 2154).all (fun i => staysPastEvent 2154 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem keyAnchorSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (2154 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem atKeyAnchor {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} {inst leader : Nat}
    (ht : At s 2153 []) (hw : Walk kernel Assumptions.all l g s es vs)
    (he : (⟨2153,.elect (2^32-1) inst leader⟩ : Event) ∈ es) :
    ∃ tail, es = ⟨2153,.elect (2^32-1) inst leader⟩ :: tail ∧
      ∀ e ∈ tail, 2154 ≤ e.pc := by
  have hout := electTemplate (l := l) (g := g) 0 ht
  cases hw with
  | stop => cases he
  | tau h _ => simp [Tau,hout] at h
  | @ev s u e es vs h hTail =>
    obtain ⟨tm,ho,hf⟩ := h
    obtain rfl := Out.ev.inj (hout.symm.trans ho)
    obtain ⟨i,lead,rfl,hAfter⟩ := hf
    obtain rfl := Option.some.inj hAfter
    have hPc : 2154 ≤ (PTX.Kernels.TmlFa4Fwd.Mma.electState l g s 0 lead).pc := by
      change 2154 ≤ s.pc+1
      rw [ht.1]
    have hRest := eventTailEvents keyAnchorTail keyAnchorSegments hTail hPc
    rcases List.mem_cons.mp he with h | h
    · exact ⟨_,congrArg (· :: es) h.symm,hRest⟩
    · have hBad := hRest _ h
      exact ((by decide : ¬ 2154 ≤ 2153) hBad).elim
  | last h =>
    obtain ⟨tm,ho,hf⟩ := h
    obtain rfl := Out.ev.inj (hout.symm.trans ho)
    obtain ⟨_,_,_,hNone⟩ := hf
    cases hNone

private theorem anchorSlotZero {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 1908 (keyEntryFacts l)) (hw : Walk kernel Assumptions.all l g s es vs)
    {inst leader : Nat} (he : (⟨2153,.elect (2^32-1) inst leader⟩ : Event) ∈ es) :
    ∃ (pre : List Event) (recv : Value) (ok : Bool) (score : Value) (q : Bool) (tail : List Event),
      es = pre ++ ⟨2151,.shfl .idx (b32 (firstKLow l)) 0 31 recv ok⟩ ::
        ⟨2152,.shfl .idx (b32 0) 0 31 score q⟩ ::
        ⟨2153,.elect (2^32-1) inst leader⟩ :: tail ∧
      (∀ e ∈ pre, e.pc ≠ 2153) ∧ (∀ e ∈ tail, 2154 ≤ e.pc) := by
  let target : Event := ⟨2153,.elect (2^32-1) inst leader⟩
  have hSome : es.filterMap anchorObservation ≠ [] := by
    have hm : target ∈ es.filterMap anchorObservation :=
      List.mem_filterMap.mpr ⟨target,he,rfl⟩
    intro h
    rw [h] at hm
    cases hm
  obtain ⟨t,pre,rest,visits,hExit,ht,hSplit,hPre,hWalk⟩ :=
    requireReadyIntervalWith anchorObservation 0 (fun e h => by
      have hHi : e.pc < 2140 := h.2
      simp [anchorObservation,show e.pc ≠ 2153 by omega])
      (by rw [hs.1]; decide) ⟨rfl,hs.2⟩ (by simp [keyEntryFacts])
      (by simp [keyEntryFacts,readyInterval]) hw hSome
  have hBefore : ∀ e ∈ pre, e.pc ≠ 2153 := by
    intro e he hEq
    have hNone := List.filterMap_eq_nil_iff.mp hPre e he
    simp [anchorObservation,hEq] at hNone
  have hRest : target ∈ rest := by
    rw [hSplit] at he
    exact (List.mem_append.mp he).resolve_left (fun h => by
      exact hBefore target h rfl)
  have hSite : t.pc = 2140 ∨ t.pc = 2763 := by simpa [readyInterval] using hExit
  rcases hSite with hSite | hSite
  swap
  · have ht' : At t t.pc [(1062,b32 12)] := ht.mono ⟨ht.2.2.2.2.2.1,trivial⟩
    have hProjection : rest.filterMap anchorObservation ≠ [] := by
      intro h
      have hm : target ∈ rest.filterMap anchorObservation :=
        List.mem_filterMap.mpr ⟨target,hRest,rfl⟩
      simp [h] at hm
    obtain ⟨u,skip,suffix,post,huExit,huAt,hSplit',hSkip,huW⟩ :=
      requireReadyIntervalWith anchorObservation 8 (fun e h => by
        have hLo : 2548 ≤ e.pc := h.1
        simp [anchorObservation,show e.pc ≠ 2153 by omega])
        (by rw [hSite]; decide) ht' (by simp) (by decide) hWalk hProjection
    have hU : u.pc = 3099 := by simpa [readyInterval] using huExit
    have hFound : target ∈ suffix := by
      rw [hSplit'] at hRest
      apply (List.mem_append.mp hRest).resolve_left
      intro h
      have hn := List.filterMap_eq_nil_iff.mp hSkip target h
      cases hn
    have hh := mmaEpilogueExitEvents hU huAt.2.2.2.1 (.inl rfl) huAt.2.2.2.2.1
      huW target hFound
    exact ((by decide : (2153 : Nat) ≠ 9205) hh).elim
  let F := (2536,b32 0)::keyEntryFacts l
  have hStep : Seg kernel Assumptions.all l g 1 2140 (keyEntryFacts l) 2141 F := by
    intro v hv
    dsimp [F,keyEntryFacts] at hv ⊢
    seg_fp hv using decide
  obtain ⟨u,visits,hu,hUWalk⟩ := requireReadySegmentNonempty hStep ⟨hSite,ht.2⟩ hWalk
    (fun h => by simp [h] at hRest)
  have hAudit : ((kernel.code.drop 2141).take (2148-2141)).all
      (pvCutCode 2141 2148 (F.map Prod.fst)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hShape : RoleShape u ∧ u.regs 1062 = some (b32 12) :=
    ⟨⟨hu.2.1.symm ▸ Nat.zero_le _,hu.2.2.1,fun _ => hu.2.1⟩,hu.2.2.2.2.2.2.1⟩
  obtain ⟨v,skip,suffix,post,hSuffix,hPc,hVShape,hVF,hVWalk,hTarget,hEarly⟩ :=
    pvWalkCut (by decide) (by decide) hAudit hUWalk (by rw [hu.1]; decide) hShape
      hu.2.2.2.2 hRest (show 2148 ≤ 2153 by decide)
  have hv : At v 2148 F := ⟨hPc,hVShape.1.2.2 (by rw [hPc]; decide),hVShape.1.2.1,
    normalBeforeLaterEvent hVWalk hTarget (hPc.symm ▸ (show 2148 < 2153 by decide)),hVF⟩
  obtain ⟨w,hSetup,hwWord⟩ := firstKeyWordLocal hp g v
    (hv.mono ⟨hv.2.2.2.2.2.1,trivial⟩)
  have hClear : ((kernel.code.drop 2148).take 3).all
      (fun i => [2536].all fun r => !(writesRegs i.op).contains r) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hStraight : ((kernel.code.drop 2148).take (3-1)).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hPhase := Epilogue.schedulerLocalFrame (lo := 2148) (len := 3)
    hClear hStraight hSetup hv.1.ge
    (by rw [hv.1]) (show 2536 ∈ [2536] by simp)
  have hWPhase : w.regs 2536 = some (b32 0) := hPhase.trans hv.2.2.2.2.1
  have hSetup' := localRun (show 1904 ≤ 2148 by decide) (show 2148+3 ≤ 2768 by decide)
    hv.1 hStraight hSetup
  rcases advanceWalkLocals hSetup' hVWalk with hNil | ⟨_,_,_,hW⟩
  · rw [hNil] at hTarget
    cases hTarget
  obtain ⟨b,e,tail',_,hFirst,hFires,_,hbW,hT⟩ :=
    pvWalkEvent hW (laneZeroBroadcast hp (by decide) hwWord Flow.code_2151) hTarget
      (hwWord.1.symm ▸ (show 2151 < 2153 by decide))
  obtain ⟨recv,ok,rfl,hAfter⟩ := hFires
  obtain rfl := Option.some.inj hAfter
  have hBPhase : At (next (setReg w 2564 recv)) 2152 [(2536,b32 0)] := by
    have hP : At w 2151 [(2536,b32 0)] := hwWord.mono ⟨hWPhase,trivial⟩
    have hn := hP.set (r := 2564) (v := recv) (by simp)
    exact hn.mono hn.2.2.2.2.2
  obtain ⟨c,e,more,_,hSecond,hSecondFires,_,hcW,hT'⟩ :=
    pvWalkEvent hbW (laneZeroBroadcast hp (by decide) hBPhase Flow.code_2152) hT
      (hBPhase.1.symm ▸ (show 2152 < 2153 by decide))
  obtain ⟨score,q,rfl,hAfter'⟩ := hSecondFires
  obtain rfl := Option.some.inj hAfter'
  have hc : At (next (setReg (next (setReg w 2564 recv)) 2574 score)) 2153 [] := by
    have hn := hBPhase.set (r := 2574) (v := score) (by simp)
    exact hn.mono trivial
  obtain ⟨tail,hAnchor,hFloor⟩ := atKeyAnchor hc hcW hT'
  refine ⟨pre++skip,recv,ok,score,q,tail,?_,?_,hFloor⟩
  · simp [hSplit,hSuffix,hFirst,hSecond,hAnchor,hwWord.1,hBPhase.1,List.append_assoc]
  · intro e h
    rcases List.mem_append.mp h with h | h
    · exact hBefore e h
    · have := hEarly e h
      omega

private theorem keyBeforeMatchedAnchor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index inst leader : Nat} (he : X.Elect (g,index) 2153 (2^32-1) inst leader) :
    ∃ j recv ok score q, j+2 = index ∧
      X.get (g,j) = some ⟨2151,.shfl .idx (b32 (firstKLow l)) 0 31 recv ok⟩ ∧
      X.ShflK (g,j) (((X.tr g).take index).countP Execution.isShfl-2) ∧
      X.get (g,j+1) = some ⟨2152,.shfl .idx (b32 0) 0 31 score q⟩ := by
  let target : Event := ⟨2153,.elect (2^32-1) inst leader⟩
  let es := (X.tr g).drop 6
  obtain ⟨t,visits,hBase,ht,hWalk⟩ := keyEntry hp hX he
  have hGet : es[index-6]? = some target := by
    dsimp only [es]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  obtain ⟨pre,recv,ok,score,q,tail,hSplit,hBefore,hAfter⟩ :=
    anchorSlotZero hp ht hWalk (List.mem_of_getElem? hGet)
  change es = _ at hSplit
  let key : Event := ⟨2151,.shfl .idx (b32 (firstKLow l)) 0 31 recv ok⟩
  let scoreEvent : Event := ⟨2152,.shfl .idx (b32 0) 0 31 score q⟩
  change es = pre++key::scoreEvent::target::tail at hSplit
  have hEq : index-6 = pre.length+2 := by
    by_contra hn
    by_cases hh : index-6 < pre.length
    · rw [hSplit,List.getElem?_append_left hh] at hGet
      exact hBefore target (List.mem_of_getElem? hGet) rfl
    rw [hSplit,List.getElem?_append_right (by omega : pre.length ≤ index-6)] at hGet
    generalize hPos : index-6-pre.length = i at hGet
    have hi : i ≠ 2 := by omega
    cases i with
    | zero =>
      have h := congrArg Event.pc (Option.some.inj hGet)
      exact (by decide : (2151 : Nat) ≠ 2153) h
    | succ n =>
      cases n with
      | zero =>
        have h := congrArg Event.pc (Option.some.inj hGet)
        exact (by decide : (2152 : Nat) ≠ 2153) h
      | succ n =>
        cases n with
        | zero => exact hi rfl
        | succ n =>
          have hM : tail[n]? = some target := hGet
          exact (by decide : ¬ (2154 : Nat) ≤ 2153) (hAfter target (List.mem_of_getElem? hM))
  let j := 6+pre.length
  have hJ : j+2 = index := by dsimp only [j]; omega
  have hKey : X.get (g,j) = some key := by
    change (X.tr g)[6+pre.length]? = some key
    rw [← List.getElem?_drop]
    change es[pre.length]? = some key
    rw [hSplit,List.getElem?_append_right le_rfl,Nat.sub_self]
    rfl
  let earlier := (X.tr g).take 6 ++ pre
  have hLength : earlier.length = j := by
    have hi : index < (X.tr g).length := ElectOrd.lt_len he
    simp [earlier,j,List.length_take_of_le (by omega : 6 ≤ (X.tr g).length)]
  have hFull : X.tr g = earlier ++ key :: scoreEvent :: target :: tail := by
    conv_lhs => rw [← List.take_append_drop 6 (X.tr g)]
    change (X.tr g).take 6 ++ es = _
    rw [hSplit]
    simp [earlier,List.append_assoc]
  have hThan : (X.tr g).take j = earlier := by rw [← hLength,hFull,List.take_append_length]
  have hCount : ((X.tr g).take index).countP Execution.isShfl =
      earlier.countP Execution.isShfl + 2 := by
    have hEnd : index = (earlier++[key,scoreEvent]).length := by simp [hLength,← hJ]
    rw [hEnd]
    conv_lhs => rw [hFull,show earlier++key::scoreEvent::target::tail =
      (earlier++[key,scoreEvent])++target::tail by simp [List.append_assoc],List.take_append_length]
    simp only [List.countP_append]
    rfl
  have hScore : X.get (g,j+1) = some scoreEvent := by
    change (X.tr g)[6+(pre.length+1)]? = some scoreEvent
    rw [← List.getElem?_drop]
    change es[pre.length+1]? = some scoreEvent
    rw [hSplit,List.getElem?_append_right (by omega),
      show pre.length+1-pre.length = 1 by omega]
    rfl
  refine ⟨j,recv,ok,score,q,hJ,hKey,⟨⟨_,.idx,b32 (firstKLow l),0,31,recv,ok,hKey⟩,?_⟩,hScore⟩
  change ((X.tr g).take j).countP Execution.isShfl = _
  rw [hThan,hCount]
  omega

/-- The first QK election immediately follows the score-column broadcast of zero. -/
theorem initialScoreShuffleZeroBeforeElection {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index inst leader : Nat} (he : X.Elect (g,index) 2153 (2^32-1) inst leader) :
    ∃ j score ok, j+1 = index ∧
      X.get (g,j) = some ⟨2152,.shfl .idx (b32 0) 0 31 score ok⟩ := by
  obtain ⟨j,_,_,score,ok,hJ,_,_,hGet⟩ := keyBeforeMatchedAnchor hp hX he
  exact ⟨j+1,score,ok,by omega,hGet⟩

/-- The observed initial QK broadcast sends a physical slot-zero key descriptor. -/
def InitialKeyBroadcast (l : Launch) (X : Execution) (id : EvId)
    (received : Value) (ok : Bool) : Prop :=
  X.get id = some ⟨2151,.shfl .idx (b32 (firstKLow l)) 0 31 received ok⟩

/-- The K descriptor shuffle immediately before the first score election receives
the live lane-zero word for physical key slot zero. -/
theorem initialKeyReplyBeforeFirstElection {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g election inst leader : Nat}
    (hElection : X.Elect (g,election) 2153 (2^32-1) inst leader) :
    ∃ j ok, InitialKeyBroadcast l X (g,j) (b32 (firstKLow l)) ok ∧ j < election := by
  obtain ⟨i,recv,ok,_,_,hi,hSend,hOrd,_⟩ := keyBeforeMatchedAnchor hp hX hElection
  let peer := g-laneOf l g
  obtain ⟨hw,_⟩ := laneZero_sameWarp (show 0 < l.block by rw [hp.block]; decide)
    (event_thread_lt hX hSend)
  have hMember : electMember (2^32-1) (laneOf l peer) := by
    refine ⟨Nat.mod_lt _ (by decide),?_⟩
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (Nat.mod_lt _ (by decide))
  obtain ⟨peerIndex,hPair⟩ := ElectOrd.partner hX hw hElection hMember
  have hSame := shuffleCountAtMatchedElection hX hw hPair
  obtain ⟨pc,pc',mask,mask',inst',lead,lead',hA,hB⟩ := hPair
  have hFix := Option.some.inj (hA.symm.trans hElection)
  have hSite : pc = 2153 := congrArg Event.pc hFix
  have hMask : mask = 2^32-1 := by
    have hKind := congrArg Event.kind hFix
    injection hKind
  obtain ⟨hPcEq,hMaskEq,_⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hA hB hw
  have hPeer : X.Elect (peer,peerIndex) 2153 (2^32-1) inst' lead' := by
    rw [← hSite,← hMask,hPcEq,hMaskEq]
    exact hB
  obtain ⟨j,peerRecv,peerOk,_,_,_,hPeerSend,hPeerOrd,_⟩ := keyBeforeMatchedAnchor hp hX hPeer
  let n := ((X.tr g).take election).countP Execution.isShfl-2
  have hOrdPeer : X.ShflK (peer,j) n := by
    rw [show n = ((X.tr peer).take peerIndex).countP Execution.isShfl-2 by
      exact congrArg (·-2) hSame]
    exact hPeerOrd
  have hSource : g-laneOf l g+(shflSource .idx (laneOf l g) 0 31).1 = peer := by
    simp [peer,shflSource_idx (laneOf l g) (show 0 < 32 by decide)]
  obtain ⟨_,⟨k,_,_,_,_,_,hk,hGet⟩ | hExit⟩ := hX.shfl g i n 2151 .idx _ 0 31 recv ok hSend hOrd
  · rw [hSource] at hk hGet
    have hk' : k = j := ShflK.eq_of_ord hk hOrdPeer
    subst k
    have hWord := congrArg Event.kind (Option.some.inj (hGet.symm.trans hPeerSend))
    have hReply : recv = b32 (firstKLow l) := Kind.shfl.inj hWord |>.2.1
    exact ⟨i,ok,hReply ▸ hSend,by omega⟩
  · rw [hSource] at hExit
    obtain ⟨k,site,hExit,hCount⟩ := hExit
    have hLast : k+1 = (X.tr peer).length := Execution.exit_last hX hw.1.2.1 hExit
    have hLen : j < (X.tr peer).length := hOrdPeer.lt
    have hNe : j ≠ k := by
      rintro rfl
      cases congrArg Event.kind (Option.some.inj (hPeerSend.symm.trans hExit))
    have hEarlier : j+1 ≤ k := by omega
    have hMore := shfl_count_succ hOrdPeer
    have hMono := countP_take_mono Execution.isShfl (X.tr peer) hEarlier
    omega

/-- The actual first K broadcast on the final O1 issuer receives the physical
slot-zero descriptor computed by its own warp's lane zero. -/
theorem initialKeyReplyBeforeSecondOutputCommit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec) :
    ∃ j ok, InitialKeyBroadcast l X (commit.1,j) (b32 (firstKLow l)) ok ∧
      TraceBefore X (commit.1,j) commit := by
  obtain ⟨g,index⟩ := commit
  obtain ⟨election,inst,leader,hEarly,hElection⟩ :=
    firstQkElectionBeforeFinalCommit hp hX (hCommit.issuerWarp hp hX) (.inr rfl) hCommit.decoded
  obtain ⟨j,ok,hReply,hBefore⟩ := initialKeyReplyBeforeFirstElection hp hX hElection
  exact ⟨j,ok,hReply,⟨rfl,by omega,PTX.len_of_get hCommit.decoded⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
