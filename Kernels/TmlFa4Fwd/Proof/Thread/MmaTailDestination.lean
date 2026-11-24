-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveAnchor
import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleExit
import Kernels.TmlFa4Fwd.Proof.MmaElect
import Lemmas.Order.ElectOrdinal
import Lemmas.Flow.PollRendezvous
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Kernels.TmlFa4Fwd.Proof.MmaPvEntry
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
import Lemmas.Flow.MarkedCut
import Lemmas.Flow.NotShfl
import Lemmas.Flow.TcMmaTs
import Lemmas.Flow.TcTmpl
import Lemmas.Execution.EventFrameSource
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

noncomputable section

private abbrev tailBlock (stage : Fin 2) : Fin 4 := firstPvBlock false stage

private def tailDestinationShuffleSite : Fin 2 → Nat
  | 0 => 2561
  | _ => 2601

private def tailDestinationElection (stage : Fin 2) : Fin 20 := pvElection (tailBlock stage)

private theorem tailElectionSite (stage : Fin 2) :
    (electSite (tailDestinationElection stage)).pc = tailDestinationShuffleSite stage+1 := by
  fin_cases stage <;> rfl

private def tailOutPrep (stage : Fin 2) : Nat := tailDestinationShuffleSite stage-1

private def tailOutSrc (stage : Fin 2) : Nat := if stage = 0 then 2627 else 2629

private def tailOutReply (stage : Fin 2) : Nat := if stage = 0 then 2613 else 2617

private def beforeTailOut (station pos : Nat) : Prop :=
  1908 ≤ pos ∧ (pos ≤ station ∨ pos = 2763)

private instance (station pos : Nat) : Decidable (beforeTailOut station pos) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def beforeTailOutCode (station : Nat) (i : Instr) : Bool :=
  match i.op with
  | .bra dst _ => decide (beforeTailOut station dst)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem beforeTailOutAudit (stage : Fin 2) :
    ((kernel.code.drop 1908).take (tailOutPrep stage-1908)).all
      (beforeTailOutCode (tailOutPrep stage)) = true := by fin_cases stage <;> kernel_rfl

private theorem beforeTailOutStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (stage : Fin 2) (hs : beforeTailOut (tailOutPrep stage) s.pc)
    (hPre : s.pc < tailOutPrep stage) (hStep : WStep kernel Assumptions.all l g s ev u) :
    beforeTailOut (tailOutPrep stage) u.pc := by
  have hHi : tailOutPrep stage < 2768 := by fin_cases stage <;> decide
  have hCore := out_eq_core (show 1904 ≤ s.pc by have := hs.1; omega)
    (show s.pc < 2768 by omega) (l := l) (g := g) (t := s)
  have hSeq : beforeTailOut (tailOutPrep stage) (s.pc+1) :=
    ⟨by have := hs.1; omega,.inl (by omega)⟩
  rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hTau : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← hCore]
    obtain ⟨ins,hCode⟩ := tau_core_has_code hTau
    rcases tau_core_frame hCode hTau with rfl | hLocal
    · exact hSeq
    have hPc := hLocal.pc
    have hMem : ins ∈ (kernel.code.drop 1908).take (tailOutPrep stage-1908) := by
      apply List.mem_of_getElem? (i := s.pc-1908)
      rw [List.getElem?_take_of_lt (by have := hs.1; omega),List.getElem?_drop,
        Nat.add_sub_of_le hs.1,hCode]
    have hCheck := List.all_eq_true.mp (beforeTailOutAudit stage) ins hMem
    cases hOp : ins.op <;> simp only [hOp,nextPc,BrxTarget,or_false] at hPc
    case bra dst uni =>
      rw [hPc]
      exact of_decide_eq_true (by simpa only [beforeTailOutCode,hOp] using hCheck)
    case brx => simp [beforeTailOutCode,hOp] at hCheck
    all_goals exact hPc.symm ▸ hSeq
  · have hEStep : EStep kernel [] l g s e (some u) := by
      obtain ⟨tm,hOut,hFire⟩ := he
      exact ⟨tm,hCore ▸ hOut,hFire⟩
    rcases (estep_return_pc hEStep (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h.symm ▸ hs
    · exact h.symm ▸ hSeq

set_option maxRecDepth 100000 in
private theorem afterMmaFloor :
    (kernel.code.drop 2763).all (fun i => staysPastEvent 2763 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterMmaSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2763 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem tailOutCut {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (stage : Fin 2)
    (hs : At s 1908 [(1062,b32 12),(2535,b32 l.sharedBase)])
    (hw : Walk kernel Assumptions.all l g s es vs)
    {e : Event} (he : e ∈ es) (hRange : tailOutPrep stage < e.pc ∧ e.pc < 2763) :
    ∃ t pre rest post, es = pre++rest ∧
      At t (tailOutPrep stage) [(1062,b32 12)] ∧ e ∈ rest ∧
      Walk kernel Assumptions.all l g t rest post ∧ ∀ f ∈ pre, f.pc < tailOutPrep stage := by
  let station := tailOutPrep stage
  have hSub : 1909 < station := by fin_cases stage <;> decide
  have hHi : station < 2768 := by fin_cases stage <;> decide
  let P := fun s => beforeTailOut station s.pc ∧ RoleShape s ∧ s.regs 1062 = some (b32 12)
  have hInit : P s :=
    ⟨by rw [hs.1]; fin_cases stage <;> decide,
      ⟨hs.2.1.symm ▸ by decide,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  have hNext {t u : TState} {ev : Option Event} (ht : P t) (hc : ¬ station ≤ t.pc)
      (hStep : WStep kernel Assumptions.all l g t ev u) :
      P u ∧ 0 = ev.toList.countP (fun _ => false) + 0 := by
    have hB : 1907 ≤ t.pc := by have := ht.1.1; omega
    have hR := (mmaCutStep hB (by omega) hStep ht.2).2
    exact ⟨⟨beforeTailOutStep stage ht.1 (by omega) hStep,hR⟩,by cases ev <;> rfl⟩
  obtain ⟨t,pre,rest,post,hSplit,hRemain,hReg,hCut,_,hPrior,hTail⟩ :=
    hw.cut_marked_where (P := P) (cut := fun s => station ≤ s.pc)
      (good := fun f => f.pc < station) (fun _ => 0) (fun _ => false)
      (fun _ _ _ => rfl) (fun ht hc hStep => hNext ht hc hStep)
      (fun _ hc hStep => by rw [estep_source_pc hStep]; omega)
      hInit he (fun t _ hn h => by
        rw [h] at hn
        exact hn hRange.1.le)
  have hPc : t.pc = station := by
    rcases hReg.1.2 with hLe | hExit
    · omega
    · exact (Nat.not_le_of_lt hRange.2
        (eventTailEvents afterMmaFloor afterMmaSegments hTail hExit.ge e hRemain)).elim
  have hAt : At t station [(1062,b32 12)] :=
    ⟨hPc,hReg.2.1.2.2 (by omega),hReg.2.1.2.1,normalBeforeLaterEvent hTail hRemain
      (by omega),hReg.2.2,trivial⟩
  exact ⟨t,pre,rest,post,hSplit,hAt,hRemain,hTail,hPrior⟩

private theorem setDestinationForSend (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel [] l g 1 (tailOutPrep stage) [(1062,b32 12)]
      (tailDestinationShuffleSite stage)
      [(tailOutSrc stage,b32 (outputColumn stage)),(1062,b32 12)] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

variable {p : Params} {l : Launch}

private theorem tailOutputPrepared {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e) (hRange : tailOutPrep stage < e.pc ∧ e.pc < 2763) :
    ∃ t pos vs, pos ≤ index ∧ At t (tailDestinationShuffleSite stage)
      [(tailOutSrc stage,b32 (outputColumn stage)),(1062,b32 12)] ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop pos) vs ∧
      e ∈ (X.tr g).drop pos := by
  have hHi : 2145 ≤ e.pc ∧ e.pc < 2768 := by
    have hLo : 2145 ≤ tailOutPrep stage := by fin_cases stage <;> decide
    omega
  obtain ⟨base,s,vs,hBase,hs,hw⟩ := initialMmaTrace hp hX he hHi.1 hHi.2
  have hMem : e ∈ (X.tr g).drop (base+1) := by
    apply List.mem_of_getElem? (i := index-(base+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  obtain ⟨t,pre,rest,post,hSplit,hAt,hRemain,hTail,hPrior⟩ := tailOutCut stage hs hw hMem hRange
  obtain ⟨u,hLocal,hu⟩ := setDestinationForSend l g stage t hAt
  have hR : 1904 ≤ tailOutPrep stage ∧ tailOutPrep stage+1 ≤ 2768 := by fin_cases stage <;> decide
  have hr := localRun hR.1 hR.2 hAt.1 rfl hLocal
  rcases advanceWalkLocals hr hTail with rfl | ⟨vs,_,_,hUWalk⟩
  · cases hRemain
  let pos := base+1+pre.length
  have hDrop : (X.tr g).drop pos = rest := by
    rw [← List.drop_drop,hSplit,List.drop_append_length]
  have hBefore : pos ≤ index := by
    by_contra! hEarly
    have hLookup : ((X.tr g).drop (base+1))[index-(base+1)]? = some e := by
      rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
    rw [hSplit,List.getElem?_append_left (by dsimp only [pos] at hEarly; omega)] at hLookup
    exact (Nat.not_lt_of_ge hRange.1.le) (hPrior e (List.mem_of_getElem? hLookup))
  exact ⟨u,pos,vs,hBefore,hu,hDrop.symm ▸ hUWalk,hDrop.symm ▸ hRemain⟩

private theorem tailOutShuffle {m : Mem0} (hp : Pre p l m) (stage : Fin 2) {g : Nat} {t : TState}
    (ht : At t (tailDestinationShuffleSite stage)
      [(tailOutSrc stage,b32 (outputColumn stage)),(1062,b32 12)]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 (outputColumn stage)) 0 31
      (fun v _ => next (setReg t (tailOutReply stage) v))) := by
  have hCode : kernel.code[t.pc]? = some ⟨none,.warp ⟨.shfl .idx,some (.int .b 32),
      [some (tailOutReply stage)],[.reg (tailOutSrc stage),.imm 0,.imm 31],
      some (.imm (-1))⟩⟩ := by
    rw [ht.1]
    fin_cases stage
    · exact Flow.code_2561
    · exact Flow.code_2601
  have hR : 1904 ≤ tailDestinationShuffleSite stage ∧ tailDestinationShuffleSite stage < 2768 :=
    by fin_cases stage <;> decide
  rw [out_eq_core (ht.1.symm ▸ hR.1) (ht.1.symm ▸ hR.2),
    out_event ht.2.2.2.1 hCode rfl rfl]
  change Out.ev (shflTmpl l g t .idx (tailOutReply stage) none (.reg (tailOutSrc stage))
    (.imm 0) (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSrc := ht.2.2.2.2.1
  simp [shflTmpl,readValue,readReg,hSrc,hBlock,Value.bytes,b32,readBits,pure,Except.pure]
  rfl

set_option maxRecDepth 100000 in
private theorem tailElectionFloor (stage : Fin 2) :
    (kernel.code.drop (tailDestinationShuffleSite stage+2)).all
      (fun i => staysPastEvent (tailDestinationShuffleSite stage+2) i.op) = true := by
  fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem tailElectionSegments (stage : Fin 2) :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (tailDestinationShuffleSite stage+2 ≤ seg.stop)
      | none => false) = true := by fin_cases stage <;> kernel_rfl

private theorem tailElectionStarts {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (stage : Fin 2) (hs : At s (tailDestinationShuffleSite stage+1) [])
    (hw : Walk kernel Assumptions.all l g s es vs) {inst lead : Nat}
    (hm : ⟨tailDestinationShuffleSite stage+1,.elect (2^32-1) inst lead⟩ ∈ es) :
    ∃ rest, es = ⟨tailDestinationShuffleSite stage+1,.elect (2^32-1) inst lead⟩ :: rest ∧
      ∀ e ∈ rest, tailDestinationShuffleSite stage+2 ≤ e.pc := by
  let pc := tailDestinationShuffleSite stage
  let target : Event := ⟨pc+1,.elect (2^32-1) inst lead⟩
  have hAt : At s (electSite (tailDestinationElection stage)).pc [] := by
    rw [tailElectionSite]
    exact hs
  have hOut := electTemplate (l := l) (g := g) (tailDestinationElection stage) hAt
  cases hw with
  | stop => cases hm
  | tau h _ => simp [Tau,hOut] at h
  | last h =>
    obtain ⟨tm,hEq,hFire⟩ := h
    obtain rfl := Out.ev.inj (hEq.symm.trans hOut)
    obtain ⟨_,_,_,hNone⟩ := hFire
    cases hNone
  | ev he hWalk =>
    obtain ⟨tm,hEq,hFire⟩ := he
    obtain rfl := Out.ev.inj (hEq.symm.trans hOut)
    obtain ⟨_,chosen,rfl,hAfter⟩ := hFire
    obtain rfl := Option.some.inj hAfter
    have hFloor : pc+2 ≤ (electState l g s (tailDestinationElection stage) chosen).pc := by
      have hResult : (electSite (tailDestinationElection stage)).result = none := by
        fin_cases stage <;> rfl
      have hState : (electState l g s (tailDestinationElection stage) chosen).pc = s.pc+1 := by
        dsimp only [electState]
        rw [hResult]
        rfl
      rw [hState,hs.1]
    have hTail := eventTailEvents (tailElectionFloor stage) (tailElectionSegments stage)
      hWalk hFloor
    rcases List.mem_cons.mp hm with h | h
    · exact ⟨_,congrArg (· :: _) h.symm,hTail⟩
    · have hBad := hTail target h
      change pc+2 ≤ pc+1 at hBad
      omega

private theorem tailShuffleBeforeElection {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g election inst lead : Nat}
    (he : X.Elect (g,election) (tailDestinationShuffleSite stage+1) (2^32-1) inst lead) :
    ∃ pos reply ok, pos+1 = election ∧
      X.get (g,pos) =
        some ⟨tailDestinationShuffleSite stage,
          .shfl .idx (b32 (outputColumn stage)) 0 31 reply ok⟩ := by
  let pc := tailDestinationShuffleSite stage
  let col := b32 (outputColumn stage)
  let target : Event := ⟨pc+1,.elect (2^32-1) inst lead⟩
  have hGet : X.get (g,election) = some target := he
  have hRange : tailOutPrep stage < target.pc ∧ target.pc < 2763 := by
    change tailOutPrep stage < pc+1 ∧ pc+1 < 2763
    fin_cases stage <;> decide
  obtain ⟨s,base,visits,hBase,hs,hw,hMem⟩ := tailOutputPrepared hp hX stage hGet hRange
  have hLater : s.pc < target.pc := by rw [hs.1]; exact Nat.lt_succ_self _
  obtain ⟨u,first,rest,post,hSplit,hFires,_,hWalk,hRemain⟩ :=
    pvWalkEvent hw (tailOutShuffle hp stage hs) hMem hLater
  obtain ⟨reply,ok,rfl,hu⟩ := hFires
  obtain rfl := Option.some.inj hu
  have hAt : At (next (setReg s (tailOutReply stage) reply)) (pc+1) [] := by
    have hNew := (hs.mono (G := []) trivial).set (r := tailOutReply stage) (v := reply) (by simp)
    exact hNew.mono trivial
  obtain ⟨tail,hHead,hRest⟩ := tailElectionStarts stage hAt hWalk hRemain
  have hSplit' : (X.tr g).drop base = ⟨pc,.shfl .idx col 0 31 reply ok⟩ :: target :: tail := by
    rw [hSplit,hHead,hs.1]
  have hLookup : ((X.tr g).drop base)[election-base]? = some target := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  rw [hSplit'] at hLookup
  have hEq : election-base = 1 := by
    cases h : election-base with
    | zero =>
      rw [h,List.getElem?_cons_zero] at hLookup
      cases congrArg Event.kind (Option.some.inj hLookup)
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        rw [h,List.getElem?_cons_succ,List.getElem?_cons_succ] at hLookup
        have hh := hRest target (List.mem_of_getElem? hLookup)
        change pc+2 ≤ pc+1 at hh
        omega
  have hSend : X.get (g,base) = some ⟨pc,.shfl .idx col 0 31 reply ok⟩ := by
    change (X.tr g)[base]? = _
    rw [← Nat.add_zero base,← List.getElem?_drop,hSplit',List.getElem?_cons_zero]
  exact ⟨base,reply,ok,by omega,hSend⟩

private theorem receiveTailDestination {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g pos inst lead : Nat}
    (hWarp : warpIndex l g = 12) {reply : Value} {ok : Bool}
    (hShfl : X.get (g,pos) =
      some ⟨tailDestinationShuffleSite stage,.shfl .idx (b32 (outputColumn stage)) 0 31 reply ok⟩)
    (hElect : X.Elect (g,pos+1) (tailDestinationShuffleSite stage+1) (2^32-1) inst lead) :
    reply = b32 (outputColumn stage) := by
  let peer := g-laneOf l g
  let n := ((X.tr g).take pos).countP Execution.isShfl
  have hw : SameWarp l g peer :=
    (laneZero_sameWarp (by rw [hp.block]; decide) (event_thread_lt hX hShfl)).1
  have hMember : electMember (2^32-1) (laneOf l peer) := by
    have hLane : laneOf l peer < 32 := Nat.mod_lt _ (by decide)
    refine ⟨hLane,?_⟩
    rw [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    exact hLane
  obtain ⟨election,hPair⟩ := ElectOrd.partner hX hw hElect hMember
  have hCounts := shuffleCountAtMatchedElection hX hw hPair
  obtain ⟨p,q,mask,mask',inst',lead',lead'',hSource,hPartner⟩ := hPair
  have hSame := Option.some.inj (hSource.symm.trans hElect)
  have hInst : inst' = inst := (Kind.elect.inj (congrArg Event.kind hSame)).2.1
  subst inst'
  obtain ⟨hPc,hMask,_⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hElect hPartner hw
  rw [← hPc,← hMask] at hPartner
  obtain ⟨j,a,b,hPos,hPeer⟩ := tailShuffleBeforeElection hp hX stage hPartner
  have hLeft : X.ShflK (g,pos) n := ⟨⟨_,_,_,_,_,_,_,hShfl⟩,rfl⟩
  let n' := ((X.tr peer).take j).countP Execution.isShfl
  have hRight : X.ShflK (peer,j) n' := ⟨⟨_,_,_,_,_,_,_,hPeer⟩,rfl⟩
  have hLeft' := shfl_count_succ hLeft
  have hRight' := shfl_count_succ hRight
  change ((X.tr g).take (pos+1)).countP Execution.isShfl =
    ((X.tr peer).take election).countP Execution.isShfl at hCounts
  rw [← hPos,hLeft',hRight'] at hCounts
  have hEqual : n = n' := by omega
  have hSite : tailDestinationShuffleSite stage < 2763 := by fin_cases stage <;> decide
  obtain ⟨k,site,b',c,r,p,hFound,hReturn⟩ :=
    mmaLaneZeroShuffleSource hp hX hWarp hShfl hLeft hSite
  have hIdx : k = j := ShflK.eq_of_ord hFound (hEqual.symm ▸ hRight)
  subst k
  have hEvent := congrArg Event.kind (Option.some.inj (hReturn.symm.trans hPeer))
  exact (Kind.shfl.inj hEvent).2.1

private def setsTailDestination (stage : Fin 2) : Nat := pvPc (tailBlock stage) 0-6

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem setDestinationForIssue (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel [] l g 1 (setsTailDestination stage)
      [(tailOutReply stage,b32 (outputColumn stage)),(1062,b32 12)]
      (setsTailDestination stage+1)
      [((pvSite (tailBlock stage)).dst,b32 (outputColumn stage)),(1062,b32 12)] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using rfl

private theorem pendingTailDestination {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (step : Fin 8) {g index : Nat}
    {e : Event} (hWarp : warpIndex l g = 12) (he : X.get (g,index) = some e)
    (hPc : e.pc = pvPc (tailBlock stage) step) :
    ∃ t rem visits, t.pc = e.pc ∧ t.regs (pvSite (tailBlock stage)).dst =
      some (b32 (outputColumn stage)) ∧
      Walk kernel Assumptions.all l g t rem visits ∧ e ∈ rem := by
  let shfl := tailDestinationShuffleSite stage
  let start := setsTailDestination stage
  let finish := pvPc (tailBlock stage) step
  let col := b32 (outputColumn stage)
  have hBounds : 1909 < shfl ∧ shfl+1 ≤ start ∧ start+1 ≤ finish ∧ finish < 2763 := by
    fin_cases stage <;> fin_cases step <;> decide
  have hPrep : tailOutPrep stage < shfl := by fin_cases stage <;> decide
  have hBegin : shfl < e.pc := by rw [hPc]; change shfl < finish; omega
  obtain ⟨s,base,vs,_,hs,hw,hMem⟩ := tailOutputPrepared hp hX stage he
    ⟨hPrep.trans hBegin,by rw [hPc]; exact hBounds.2.2.2⟩
  obtain ⟨u,observed,tail,post,hSplit,hFire,hStep,hWalk,hLater⟩ :=
    pvWalkEvent hw (tailOutShuffle hp stage hs) hMem (hs.1.symm ▸ hBegin)
  obtain ⟨reply,ok,rfl,hu⟩ := hFire
  let shflEvent : Event := ⟨shfl,.shfl .idx col 0 31 reply ok⟩
  have hGet : X.get (g,base) = some shflEvent := by
    change (X.tr g)[base]? = _
    rw [← Nat.add_zero base,← List.getElem?_drop,hSplit,List.getElem?_cons_zero]
    unfold shflEvent
    rw [hs.1]
  obtain rfl := Option.some.inj hu
  have hElectAt : At (next (setReg s (tailOutReply stage) reply))
      (electSite (tailDestinationElection stage)).pc [] := by
    rw [tailElectionSite]
    have ht := (hs.mono (G := []) trivial).set (r := tailOutReply stage) (v := reply) (by simp)
    exact ht.mono trivial
  have hLaterElect : (next (setReg s (tailOutReply stage) reply)).pc < e.pc := by
    change s.pc+1 < e.pc
    rw [hs.1,hPc]
    change shfl+1 < finish
    omega
  obtain ⟨_,_,_,_,hSplitElect,hEFire,_,_,_⟩ :=
    pvWalkEvent hWalk (electTemplate (g := g) (tailDestinationElection stage) hElectAt)
      hLater hLaterElect
  obtain ⟨inst,lead,rfl,_⟩ := hEFire
  have hElection : X.Elect (g,base+1) (shfl+1) (2^32-1) inst lead := by
    change (X.tr g)[base+1]? = _
    rw [← List.getElem?_drop,hSplit,List.getElem?_cons_succ,hSplitElect,
      List.getElem?_cons_zero]
    change some (Event.mk (s.pc+1) (.elect (2^32-1) inst lead)) = _
    rw [hs.1]
  have hWord : reply = col := receiveTailDestination hp hX stage hWarp hGet hElection
  have hU : (next (setReg s (tailOutReply stage) reply)).pc = shfl+1 :=
    congrArg (·+1) hs.1
  let F := [(tailOutReply stage,col)]
  have hKeep : Holds (next (setReg s (tailOutReply stage) reply)).regs F :=
    ⟨(Function.update_self _ _ _).trans (congrArg some hWord),trivial⟩
  have hShape := (mmaCutStep (by rw [hs.1]; omega) (by rw [hs.1]; omega)
      (.inr ⟨_,rfl,hStep⟩)
      ⟨⟨hs.2.1.symm ▸ by decide,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.2.1⟩).2
  have hAudit : ((kernel.code.drop (shfl+1)).take (start-(shfl+1))).all
      (pvCutCode (shfl+1) start (F.map Prod.fst)) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v,_,suffix,vs',_,hv,hShape',hRegs,hWalk',hEvent,_⟩ :=
    pvWalkCut (show 1907 ≤ shfl+1 by omega) (show start < 2768 by omega) hAudit hWalk
      (by rw [hU]; exact ⟨le_rfl,hBounds.2.1⟩) hShape hKeep hLater
      (show start ≤ e.pc by rw [hPc]; change start ≤ finish; omega)
  have hV : At v start [(tailOutReply stage,col),(1062,b32 12)] :=
    ⟨hv,hShape'.1.2.2 (by omega),hShape'.1.2.1,
      normalBeforeLaterEvent hWalk' hEvent (by rw [hv,hPc]; change start < finish; omega),
      hRegs.1,hShape'.2,trivial⟩
  obtain ⟨w,hLocal,hw⟩ := setDestinationForIssue l g stage v hV
  have hr := localRun (show 1904 ≤ start by omega) (show start+1 ≤ 2768 by omega)
    hV.1 rfl hLocal
  rcases advanceWalkLocals hr hWalk' with rfl | ⟨visits,_,_,hAtWalk⟩
  · cases hEvent
  let G := [((pvSite (tailBlock stage)).dst,col)]
  have hAudit' : ((kernel.code.drop (start+1)).take (finish-(start+1))).all
      (pvCutCode (start+1) finish (G.map Prod.fst)) = true := by
    fin_cases stage <;> fin_cases step <;> set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t,_,rem,visits,_,ht,_,hRegs,hWalk,hFound,_⟩ :=
    pvWalkCut (show 1907 ≤ start+1 by omega) (show finish < 2768 by omega) hAudit'
      hAtWalk (by rw [hw.1]; exact ⟨le_rfl,hBounds.2.2.1⟩)
      ⟨⟨hw.2.1.symm ▸ by decide,hw.2.2.1,fun _ => hw.2.1⟩,hw.2.2.2.2.2.1⟩
      (show Holds w.regs G from ⟨hw.2.2.2.2.1,trivial⟩) hEvent hPc.symm.le
  exact ⟨t,rem,visits,ht.trans hPc.symm,hRegs.1,hWalk,hFound⟩

set_option maxRecDepth 100000 in
private theorem afterTailIssueFloor (stage : Fin 2) (step : Fin 8) :
    (kernel.code.drop (pvPc (tailBlock stage) step+1)).all
      (fun i => staysPastEvent (pvPc (tailBlock stage) step+1) i.op) = true := by
  fin_cases stage <;> fin_cases step <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem tailSegAudit :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2635 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem afterTailIssueSegments (stage : Fin 2) (step : Fin 8) :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (pvPc (tailBlock stage) step+1 ≤ seg.stop)
      | none => false) = true := by
  apply List.all_eq_true.mpr
  intro site hm
  have h := List.all_eq_true.mp tailSegAudit site hm
  have hBound : pvPc (tailBlock stage) step+1 ≤ 2635 := by
    fin_cases stage <;> fin_cases step <;> decide
  cases he : cuteExp2.matchAt kernel site with
  | none => simp only [he,Bool.false_eq_true] at h
  | some seg =>
    simp only [he] at h
    change decide (pvPc (tailBlock stage) step+1 ≤ seg.stop) = true
    exact decide_eq_true (hBound.trans (of_decide_eq_true h))

private theorem tailIssueAtCut {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {vs : List Visit} (stage : Fin 2) (step : Fin 8)
    (ht : t.pc = pvPc (tailBlock stage) step)
    (hw : Walk kernel Assumptions.all l g t es vs)
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (he : ⟨pvPc (tailBlock stage) step,.tc (.mma d op accum mask)⟩ ∈ es) :
    ∃ u, EStep kernel Assumptions.all l g t
      ⟨pvPc (tailBlock stage) step,.tc (.mma d op accum mask)⟩ (some u) := by
  let site := pvPc (tailBlock stage) step
  let target : Event := ⟨site,.tc (.mma d op accum mask)⟩
  change target ∈ es at he
  have hRange : 1904 ≤ site ∧ site < 2768 := by fin_cases stage <;> fin_cases step <;> decide
  have hc : kernel.code[t.pc]? = some _ := ht.symm ▸ pvCode (tailBlock stage) step
  have hBad {u : TState} {es : List Event} {vs : List Visit}
      (hPc : u.pc = t.pc+1) (hw : Walk kernel Assumptions.all l g u es vs) :
      target ∉ es := by
    intro hMem
    have h := eventTailEvents (afterTailIssueFloor stage step)
      (afterTailIssueSegments stage step) hw (show site+1 ≤ u.pc by rw [hPc,ht]) target hMem
    change site + 1 ≤ site at h
    omega
  cases hw with
  | stop => cases he
  | tau h hWalk =>
    have hCore := out_eq_core (ht.symm ▸ hRange.1) (ht.symm ▸ hRange.2)
      (l := l) (g := g) (t := t)
    rw [Tau,hCore] at h
    rcases tau_core_frame hc h with rfl | hFrame
    · exact (hBad rfl hWalk he).elim
    · exact (hBad (hFrame.pc.resolve_right id) hWalk he).elim
  | ev hEvent hw =>
    rcases List.mem_cons.mp he with rfl | hMem
    · exact ⟨_,hEvent⟩
    obtain ⟨ins,hGet,_,hFire⟩ := estep_event_source hEvent
    obtain rfl := Option.some.inj (hGet.symm.trans hc)
    obtain rfl := fires_tcMmaTs hFire
    exact (hBad rfl hw hMem).elim
  | last hEvent =>
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨tm,_,hf⟩ := hEvent
    rcases fires_none_ends hf with ⟨_,h⟩ | h <;> cases h

private def templateDestination (col : Nat) : Tmpl → Prop
  | .tc (.mma dst _ _ _) _ => dst = col
  | .ub _ => True
  | _ => False

private theorem destinationTemplate {l : Launch} {g d ta rb ri : Nat} {s : TState} {off : Int}
    {col : Nat} {en : Opnd} (hg : g < l.threads) (hCol : col < 2^32)
    (hReg : s.regs d = some (b32 col)) :
    templateDestination col (eventTmpl Assumptions.all l g s
      (.tcMma (.dense .one false .f16 d (.tmem ta off) (.reg rb) (.reg ri)
        (List.replicate 4 (.imm 0)) en))) := by
  have hRead := readBits_b32 (L := l) (g := g) hReg hCol
  have hNat := toNat_ofNat_lt (show col < 2^64 by omega)
  have hExec {r : Exec Tmpl} (h : AllOk (templateDestination col) r) :
      templateDestination col (ofExec r) := by
    cases r
    · trivial
    · exact h
  have hBind {α β : Type} (a : α) (f : α → Exec β) :
      (Except.ok a : Exec α) >>= f = f a := rfl
  simp only [eventTmpl,tcTmpl_tcMma_tmem (.inr (.inl rfl)),mmaTmemTmpl,hg,↓reduceIte,hRead,
    hBind,hNat]
  apply hExec
  apply allOk_bind
  intro a
  apply allOk_bind (r := tmemOffset a.toNat off)
  intro tmem
  apply allOk_bind (r := readBits l g s 64 (.reg rb))
  intro b
  apply allOk_bind (r := readBits l g s 32 (.reg ri))
  intro id
  simp only [List.length_replicate,CtaGroup.size,Nat.reduceMul,↓reduceIte]
  apply allOk_bind (r := (List.replicate 4 (.imm 0 : Opnd)).mapM (readBits l g s 32))
  intro masks
  apply allOk_bind (r := mmaEnable s en)
  intro useAcc
  apply allOk_bind (r := zeroColumnMaskOk l g s none)
  intro zcm
  cases TcShared.decode b.toNat with
  | none => trivial
  | some dB =>
    cases TcMma.decode .one false .f16 id.toNat with
    | none => trivial
    | some desc =>
      simp only
      split
      · trivial
      · cases TcMma.makeOperands l (g/l.block) desc dB dB <;> simp only <;> trivial

private theorem firedDestination {pc col d : Nat} {t : Tmpl} {u : Option TState}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (h : templateDestination col t) (hf : Fires pc t ⟨pc,.tc (.mma d op accum mask)⟩ u) :
    d = col := by
  cases t <;> simp only [templateDestination] at h
  case tc k _ =>
    cases k <;> try contradiction
    cases congrArg Event.kind hf.1
    exact h
  case ub => cases congrArg Event.kind hf.1

/-- A nonfaulting MMA role event comes from its decoded instruction, even when the
execution prefix stops at the event. -/
theorem mmaRoleEventSource {l : Launch} {g : Nat} {t : TState} {e : Event}
    {u : Option TState} (hStep : EStep kernel Assumptions.all l g t e u)
    (hNonfault : ∀ f, e.kind ≠ .ub f) :
    ∃ ins, kernel.code[t.pc]? = some ins ∧
      Fires t.pc (eventTmpl Assumptions.all l g t ins.op) e u := by
  obtain ⟨tmpl,ho,hFire⟩ := hStep
  unfold out at ho
  split at ho
  · cases ho
    exact (hNonfault _ (congrArg Event.kind hFire.1)).elim
  · split at ho
    · cases ho
      exact (hNonfault _ (congrArg Event.kind hFire.1)).elim
    · rename_i ins hCode
      split at ho
      · cases ho
        exact (hNonfault _ (congrArg Event.kind hFire.1)).elim
      · cases ho
      · split at ho
        · split at ho
          · cases ho
          · cases ho
            exact (hNonfault _ (congrArg Event.kind hFire.1)).elim
        · cases ho
          exact ⟨ins,hCode,hFire⟩

/-- The actual destination of a PV issue is the 32-bit column word at its source. -/
theorem pvDestinationOfRegister {l : Launch} {g : Nat} (hg : g < l.threads)
    (block : Fin 4) (step : Fin 8) {t : TState} {u : Option TState} {d col : Nat}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} (hCol : col < 2^32)
    (hReg : t.regs (pvSite block).dst = some (b32 col))
    (hStep : EStep kernel Assumptions.all l g t
      ⟨pvPc block step,.tc (.mma d op accum mask)⟩ u) : d = col := by
  have hPc := (estep_source_pc hStep).symm
  obtain ⟨ins,hCode,hFires⟩ := mmaRoleEventSource hStep (by intro f h; contradiction)
  change t.pc = pvPc block step at hPc
  rw [hPc,pvCode block step] at hCode
  obtain rfl := Option.some.inj hCode
  rw [hPc] at hFires
  exact firedDestination (destinationTemplate hg hCol hReg) hFires

/-- The decoded destination of a tail PV fragment is the published output column
of its phase, matched by the following full-warp election. -/
theorem PvInstruction.tailOutputDestination {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {issue : EvId} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : PvInstruction X issue (firstPvBlock false stage) step d op accum mask) :
    d = outputColumn stage := by
  obtain ⟨g,j⟩ := issue
  let target : Event := ⟨pvPc (tailBlock stage) step,.tc (.mma d op accum mask)⟩
  have hGet : X.get (g,j) = some target := hIssue.decoded
  have hg := event_thread_lt hX hGet
  have hRange : 2534 < target.pc ∧ target.pc < 2768 ∧ target.pc ∉ registerHintSites := by
    change 2534 < pvPc (tailBlock stage) step ∧ pvPc (tailBlock stage) step < 2768 ∧
      pvPc (tailBlock stage) step ∉ registerHintSites
    fin_cases stage <;> fin_cases step <;> decide
  have hRole := roleBodyPcOfEvent hp hX hGet (by omega) hRange.2.2
  have hWarp : warpIndex l g = 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  obtain ⟨t,es,vs,hPc,hReg,hWalk,hFound⟩ :=
    pendingTailDestination hp hX stage step hWarp hGet rfl
  obtain ⟨u,hFire⟩ := tailIssueAtCut stage step hPc hWalk hFound
  have hCol : outputColumn stage < 2^32 := by fin_cases stage <;> decide
  exact pvDestinationOfRegister hg (tailBlock stage) step hCol hReg hFire

end
end PTX.Kernels.TmlFa4Fwd.Thread
