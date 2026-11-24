-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyBroadcast
import Kernels.TmlFa4Fwd.Proof.MmaInitialValueCursor
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
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
import Lemmas.Order.ElectOrdinal
import Lemmas.Flow.PollRendezvous
import Lemmas.Flow.Tc

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.EventFrame Prologue _root_.PTX.Kernels.TmlFa4Fwd.Mma

private def secondScoreElection (e : Event) : Option Event :=
  if e.pc = 2215 then some e else none

set_option maxRecDepth 100000 in
private theorem secondScoreElectionTail :
    (kernel.code.drop 2216).all (fun i => staysPastEvent 2216 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem secondScoreElectionSegments :
    Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (2216 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem secondScoreBroadcastSplit {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 1908 [(1062,b32 12)]) (hw : Walk kernel Assumptions.all l g s es vs)
    {inst leader : Nat} (he : (⟨2215,.elect (2^32-1) inst leader⟩ : Event) ∈ es) :
    ∃ pre score ok tail, es = pre ++ ⟨2214,.shfl .idx (b32 128) 0 31 score ok⟩ ::
      ⟨2215,.elect (2^32-1) inst leader⟩ :: tail ∧
      (∀ e ∈ pre, e.pc ≠ 2215) ∧ (∀ e ∈ tail, 2216 ≤ e.pc) := by
  let target : Event := ⟨2215,.elect (2^32-1) inst leader⟩
  have hSome : es.filterMap secondScoreElection ≠ [] := by
    have hm : target ∈ es.filterMap secondScoreElection :=
      List.mem_filterMap.mpr ⟨target,he,rfl⟩
    exact fun hn => by rw [hn] at hm; cases hm
  obtain ⟨t,pre,rest,visits,hExit,ht,hSplit,hPre,hWalk⟩ :=
    requireReadyIntervalWith secondScoreElection 0 (fun e h => by
      have hHi : e.pc < 2140 := h.2
      simp [secondScoreElection,show e.pc ≠ 2215 by omega])
      (by rw [hs.1]; decide) ⟨rfl,hs.2⟩ (by simp)
      (by simp) hw hSome
  have hRest : target ∈ rest := by
    rw [hSplit] at he
    apply (List.mem_append.mp he).resolve_left
    intro h
    have hBad := List.filterMap_eq_nil_iff.mp hPre target h
    cases hBad
  have hSite : t.pc = 2140 ∨ t.pc = 2763 := by simpa [readyInterval] using hExit
  rcases hSite with hSite | hSite
  swap
  · have hProjection : rest.filterMap secondScoreElection ≠ [] := by
      have hm : target ∈ rest.filterMap secondScoreElection :=
        List.mem_filterMap.mpr ⟨target,hRest,rfl⟩
      exact fun hn => by rw [hn] at hm; cases hm
    obtain ⟨u,skip,suffix,post,huExit,huAt,hSplit',hSkip,huW⟩ :=
      requireReadyIntervalWith secondScoreElection 8 (fun e h => by
        have hLo : 2548 ≤ e.pc := h.1
        simp [secondScoreElection,show e.pc ≠ 2215 by omega])
        (by rw [hSite]; decide) ht (by simp) (by decide) hWalk hProjection
    have hU : u.pc = 3099 := by simpa [readyInterval] using huExit
    have hFound : target ∈ suffix := by
      rw [hSplit'] at hRest
      apply (List.mem_append.mp hRest).resolve_left
      intro h
      have hBad := List.filterMap_eq_nil_iff.mp hSkip target h
      cases hBad
    have hh := mmaEpilogueExitEvents hU huAt.2.2.2.1 (.inl rfl) huAt.2.2.2.2.1
      huW target hFound
    exact ((by decide : (2215 : Nat) ≠ 9205) hh).elim
  have hAudit : ((kernel.code.drop 2140).take (2213-2140)).all
      (pvCutCode 2140 2213 [1062]) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hShape : RoleShape t ∧ t.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩,ht.2.2.2.2.1⟩
  obtain ⟨u,skip,suffix,post,hRestSplit,huPc,huShape,_,huWalk,huMem,hEarly⟩ :=
    pvWalkCut (by decide) (by decide) hAudit hWalk (by rw [hSite]; decide) hShape
      ht.2.2.2.2 hRest (show 2213 ≤ 2215 by decide)
  have huAt : At u 2213 [] := ⟨huPc,huShape.1.2.2 (by rw [huPc]; decide),
    huShape.1.2.1,normalBeforeLaterEvent huWalk huMem
      (huPc.symm ▸ (show 2213 < 2215 by decide)),trivial⟩
  have hLocal : Seg kernel Assumptions.all l g 1 2213 [] 2214 [(2565,b32 128)] := by
    intro v hv
    seg_fp hv using decide
  obtain ⟨v,_,hv,hvWalk⟩ := requireReadySegmentNonempty hLocal huAt huWalk
    (fun hn => by rw [hn] at huMem; cases huMem)
  obtain ⟨w,_,more,_,hSecond,hFires,_,hwWalk,hwMem⟩ :=
    pvWalkEvent hvWalk (laneZeroBroadcast hp (by decide) hv Flow.code_2214) huMem
      (hv.1.symm ▸ (show 2214 < 2215 by decide))
  obtain ⟨score,ok,rfl,hAfter⟩ := hFires
  obtain rfl := Option.some.inj hAfter
  let w := next (setReg v 2602 score)
  have hwAt : At w 2215 [] := (hv.set (r := 2602) (v := score) (by simp)).mono trivial
  have hOut := electTemplate (l := l) (g := g) 2 hwAt
  cases hwWalk with
  | stop => cases hwMem
  | tau h _ =>
    unfold Tau at h
    change out kernel Assumptions.all l g w = _ at h
    rw [hOut] at h
    cases h
  | @ev _ u e es vs h hTail =>
    obtain ⟨tm,ho,hf⟩ := h
    obtain rfl := Out.ev.inj (hOut.symm.trans ho)
    obtain ⟨i,lead,rfl,hAfter⟩ := hf
    obtain rfl := Option.some.inj hAfter
    have hPc : 2216 ≤ (electState l g w 2 lead).pc := by
      change 2216 ≤ w.pc+1
      rw [hwAt.1]
    have hAfter := eventTailEvents secondScoreElectionTail secondScoreElectionSegments hTail hPc
    rcases List.mem_cons.mp hwMem with h | h
    · refine ⟨pre++skip,score,ok,es,?_,?_,hAfter⟩
      · change suffix = ⟨v.pc,.shfl .idx (b32 128) 0 31 score ok⟩ ::
          ⟨w.pc,.elect (2^32-1) i lead⟩ :: es at hSecond
        rw [← h,hv.1] at hSecond
        simp [hSplit,hRestSplit,hSecond,target,List.append_assoc]
      · intro e he
        rcases List.mem_append.mp he with he | he
        · intro hEq
          have hBad := List.filterMap_eq_nil_iff.mp hPre e he
          simp [secondScoreElection,hEq] at hBad
        · have := hEarly e he
          omega
    · exact ((by decide : ¬ 2216 ≤ 2215) (hAfter _ h)).elim
  | last h =>
    obtain ⟨tm,ho,hf⟩ := h
    obtain rfl := Out.ev.inj (hOut.symm.trans ho)
    obtain ⟨_,_,_,hNone⟩ := hf
    cases hNone

/-- The second initial score election immediately follows the broadcast of column 128. -/
theorem initialScoreShuffleOneBeforeElection {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index inst leader : Nat} (he : X.Elect (g,index) 2215 (2^32-1) inst leader) :
    ∃ j score ok, j+1 = index ∧
      X.get (g,j) = some ⟨2214,.shfl .idx (b32 128) 0 31 score ok⟩ := by
  let target : Event := ⟨2215,.elect (2^32-1) inst leader⟩
  obtain ⟨base,s,_,hBase,hs,hWalk⟩ :=
    initialMmaTrace hp hX he (show 2145 ≤ 2215 by decide) (show 2215 < 2768 by decide)
  let es := (X.tr g).drop (base+1)
  have hGet : es[index-(base+1)]? = some target := by
    dsimp only [es]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  obtain ⟨pre,score,ok,tail,hSplit,hBefore,hAfter⟩ :=
    secondScoreBroadcastSplit hp (hs.mono ⟨hs.2.2.2.2.1,trivial⟩) hWalk
      (List.mem_of_getElem? hGet)
  change es = _ at hSplit
  have hEq : index-(base+1) = pre.length+1 := by
    by_cases hEarly : index-(base+1) < pre.length
    · rw [hSplit,List.getElem?_append_left hEarly] at hGet
      exact (hBefore target (List.mem_of_getElem? hGet) rfl).elim
    rw [hSplit,List.getElem?_append_right (by omega : pre.length ≤ index-(base+1))] at hGet
    generalize hPos : index-(base+1)-pre.length = i at hGet
    cases i with
    | zero =>
      have ht := congrArg Event.pc (Option.some.inj hGet)
      exact ((by decide : (2214 : Nat) ≠ 2215) ht).elim
    | succ i =>
      cases i with
      | zero => omega
      | succ i =>
        have hTail : tail[i]? = some target := hGet
        exact ((by decide : ¬ 2216 ≤ 2215) (hAfter _ (List.mem_of_getElem? hTail))).elim
  refine ⟨base+1+pre.length,score,ok,by omega,?_⟩
  change (X.tr g)[base+1+pre.length]? = _
  rw [← List.getElem?_drop]
  change es[pre.length]? = _
  rw [hSplit,List.getElem?_append_right le_rfl,Nat.sub_self]
  rfl

private theorem adjacentShuffleOrdinal {X : Execution}
    {g j pc col : Nat} {recv : Value} {ok : Bool}
    (he : X.get (g,j) = some ⟨pc,.shfl .idx (b32 col) 0 31 recv ok⟩) :
    X.ShflK (g,j) (((X.tr g).take (j+1)).countP Execution.isShfl-1) := by
  have h := shfl_count_succ (n := ((X.tr g).take j).countP Execution.isShfl)
    (show X.ShflK (g,j) _ from ⟨⟨pc,.idx,b32 col,0,31,recv,ok,he⟩,rfl⟩)
  exact ⟨⟨pc,.idx,b32 col,0,31,recv,ok,he⟩,by rw [h,Nat.add_sub_cancel]⟩

/-- The full-warp QK election matches the preceding score broadcast to its lane-zero sender. -/
theorem initialScoreBroadcastOfElection {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g j inst leader : Nat}
    (hElect : X.Elect (g,j) (2153+62*stage.val) (2^32-1) inst leader) :
    ∃ k ok, X.get (g,k) =
      some ⟨2152+62*stage.val,.shfl .idx (b32 (scoreColumn stage)) 0 31
        (b32 (scoreColumn stage)) ok⟩ ∧ k+1 = j := by
  let pc := 2152+62*stage.val
  let col := scoreColumn stage
  have hGate : pc+1 = 2153+62*stage.val := by dsimp only [pc]; omega
  rw [← hGate] at hElect
  have hAdjacent {g j i d : Nat} (he : X.Elect (g,j) (pc+1) (2^32-1) i d) :
      ∃ k recv ok, k+1 = j ∧ X.get (g,k) = some ⟨pc,.shfl .idx (b32 col) 0 31 recv ok⟩ := by
    fin_cases stage
    · exact initialScoreShuffleZeroBeforeElection hp hX he
    · exact initialScoreShuffleOneBeforeElection hp hX he
  obtain ⟨k,recv,ok,hNext,hSend⟩ := hAdjacent hElect
  let peer := g-laneOf l g
  obtain ⟨hw,_⟩ := laneZero_sameWarp (show 0 < l.block by rw [hp.block]; decide)
    (event_thread_lt hX hSend)
  have hMember : electMember (2^32-1) (laneOf l peer) := by
    refine ⟨Nat.mod_lt _ (by decide),?_⟩
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (Nat.mod_lt _ (by decide))
  obtain ⟨peerIndex,hPair⟩ := ElectOrd.partner hX hw hElect hMember
  have hSame := shuffleCountAtMatchedElection hX hw hPair
  obtain ⟨pc₀,pc₁,mask₀,mask₁,inst',lead,lead',hA,hB⟩ := hPair
  have hFix := Option.some.inj (hA.symm.trans hElect)
  have hSite : pc₀ = pc+1 := congrArg Event.pc hFix
  have hMask : mask₀ = 2^32-1 := by
    have hKind := congrArg Event.kind hFix
    injection hKind
  obtain ⟨hPcEq,hMaskEq,_⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hA hB hw
  have hPeer : X.Elect (peer,peerIndex) (pc+1) (2^32-1) inst' lead' := by
    rw [← hSite,← hMask,hPcEq,hMaskEq]
    exact hB
  obtain ⟨a,peerRecv,peerOk,hPeerNext,hPeerSend⟩ := hAdjacent hPeer
  let n := ((X.tr g).take j).countP Execution.isShfl-1
  have hOrd : X.ShflK (g,k) n := by
    dsimp only [n]
    rw [← hNext]
    exact adjacentShuffleOrdinal hSend
  have hOrdPeer : X.ShflK (peer,a) n := by
    dsimp only [n]
    change ((X.tr g).take j).countP _ = ((X.tr peer).take peerIndex).countP _ at hSame
    rw [hSame,← hPeerNext]
    exact adjacentShuffleOrdinal hPeerSend
  have hSource : g-laneOf l g+(shflSource .idx (laneOf l g) 0 31).1 = peer := by
    simp [peer,shflSource_idx (laneOf l g) (show 0 < 32 by decide)]
  obtain ⟨_,⟨b,_,_,_,_,_,hb,hGet⟩ | hExit⟩ := hX.shfl g k n pc .idx _ 0 31 recv ok hSend hOrd
  · rw [hSource] at hb hGet
    obtain rfl := ShflK.eq_of_ord hb hOrdPeer
    have hWord := congrArg Event.kind (Option.some.inj (hGet.symm.trans hPeerSend))
    have hReply : recv = b32 col := (Kind.shfl.inj hWord).2.1
    exact ⟨k,ok,hReply ▸ hSend,hNext⟩
  · rw [hSource] at hExit
    obtain ⟨b,site,hExit,hCount⟩ := hExit
    have hLast : b+1 = (X.tr peer).length := Execution.exit_last hX hw.1.2.1 hExit
    have hLen : a < (X.tr peer).length := hOrdPeer.lt
    have hNe : a ≠ b := by
      rintro rfl
      cases congrArg Event.kind (Option.some.inj (hPeerSend.symm.trans hExit))
    have hEarlier : a+1 ≤ b := by omega
    have hMore := shfl_count_succ hOrdPeer
    have hMono := countP_take_mono Execution.isShfl (X.tr peer) hEarlier
    omega

/-- The selected initial QK bank's observed broadcast receives its configured score column. -/
theorem initialScoreBroadcastBeforeSecondOutputCommit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec)
    (stage : Fin 2) : ∃ j ok, X.get (commit.1,j) =
      some ⟨2152+62*stage.val,.shfl .idx (b32 (scoreColumn stage)) 0 31
        (b32 (scoreColumn stage)) ok⟩ ∧ TraceBefore X (commit.1,j) commit := by
  obtain ⟨g,index⟩ := commit
  let pc := 2152+62*stage.val
  let col := scoreColumn stage
  have hElection : ∃ j inst leader, j < index ∧ X.Elect (g,j) (pc+1) (2^32-1) inst leader := by
    fin_cases stage
    · exact firstQkElectionBeforeFinalCommit hp hX (hCommit.issuerWarp hp hX)
        (.inr rfl) hCommit.decoded
    · exact secondQkElectionBeforeFinalCommit hp hX (.inr rfl) hCommit.decoded
  obtain ⟨j,inst,leader,hBefore,hElect⟩ := hElection
  have hGate : pc+1 = 2153+62*stage.val := by dsimp only [pc]; omega
  rw [hGate] at hElect
  obtain ⟨k,ok,hReply,hNext⟩ := initialScoreBroadcastOfElection hp hX stage hElect
  exact ⟨k,ok,hReply,⟨rfl,by omega,len_of_get hCommit.decoded⟩⟩

def scoreBroadcastRegister (stage : Fin 2) : Nat := if stage = 0 then 2574 else 2602

set_option maxRecDepth 100000 in
theorem initialScoreBroadcastFrame {l : Launch} {g : Nat} {t u : TState}
    (stage : Fin 2) (ok : Bool)
    (hStep : EStep kernel Assumptions.all l g t
      ⟨2152+62*stage.val,.shfl .idx (b32 (scoreColumn stage)) 0 31 (b32 (scoreColumn stage)) ok⟩
      (some u)) :
    u.pc = 2153+62*stage.val ∧ u.regs (scoreBroadcastRegister stage) =
      some (b32 (scoreColumn stage)) := by
  have ht := (estep_source_pc hStep).symm
  obtain ⟨i,hCode,_,hFires⟩ := estep_event_source hStep
  rw [ht] at hCode
  fin_cases stage
  all_goals
    first
    | change kernel.code[2152]? = some i at hCode
      rw [Flow.code_2152] at hCode
    | change kernel.code[2214]? = some i at hCode
      rw [Flow.code_2214] at hCode
    obtain rfl := Option.some.inj hCode
    obtain ⟨sent,b,c,recv,valid,hEvent,hu⟩ := fires_shfl (p := none) hFires
    have hWord := (Kind.shfl.inj (congrArg Event.kind hEvent)).2.2.2.2.1.symm
    subst recv
    rw [hu]
    refine ⟨?_,?_⟩
    · exact congrArg (·+1) ht
    · simp [scoreBroadcastRegister,next,setReg]

set_option maxRecDepth 100000 in
private theorem initialScoreIssueFloor (stage : Fin 2) :
    (kernel.code.drop (2153+62*stage.val)).all
      (fun i => staysPastEvent (2153+62*stage.val) i.op) = true := by
  fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem initialScoreIssueSegments (stage : Fin 2) :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2153+62*stage.val ≤ seg.stop)
      | none => false) = true := by
  fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem initialScoreSetDestination {l : Launch} {g : Nat} (stage : Fin 2) :
    Seg kernel Assumptions.all l g 1 (2154+62*stage.val)
      [(scoreBroadcastRegister stage,b32 (scoreColumn stage)),(1062,b32 12)]
      (2155+62*stage.val)
        [(qkDestination (initialQkBlock stage),b32 (scoreColumn stage)),(1062,b32 12)] := by
  intro t ht
  fin_cases stage
  · change At t 2154 [(2574,b32 0),(1062,b32 12)] at ht
    change ∃ u, run kernel Assumptions.all l g 1 t = some u ∧ At u 2155 [(9638,b32 0),(1062,b32 12)]
    seg_fp ht using skip
  · change At t 2216 [(2602,b32 128),(1062,b32 12)] at ht
    change ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 2217 [(9655,b32 128),(1062,b32 12)]
    seg_fp ht using skip

set_option maxRecDepth 100000 in
/-- Each initial QK fragment carries the destination column of its actual matched shuffle. -/
theorem initialScoreDestinationFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec)
    (stage : Fin 2) (step : Fin 8) {j : Nat} {e : Event}
    (he : X.get (commit.1,j) = some e) (hPc : e.pc = qkPc (initialQkBlock stage)+step.val) :
    ∃ t es vs, t.pc = e.pc ∧ t.regs (qkDestination (initialQkBlock stage)) =
      some (b32 (scoreColumn stage)) ∧ Walk kernel Assumptions.all l commit.1 t es vs ∧ e ∈ es := by
  let g := commit.1
  let pc := 2152+62*stage.val
  let col := scoreColumn stage
  let dst := qkDestination (initialQkBlock stage)
  have hLo : 2145 ≤ pc := by fin_cases stage <;> decide
  have hHi : pc < 2768 := by fin_cases stage <;> decide
  have hTarget : pc+2 < e.pc ∧ e.pc < 2768 := by
    rw [hPc]
    fin_cases stage <;> fin_cases step <;> decide
  obtain ⟨index,ok,hBroadcast,_⟩ :=
    initialScoreBroadcastBeforeSecondOutputCommit hp hX hCommit stage
  let sent : Event := ⟨pc,.shfl .idx (b32 col) 0 31 (b32 col) ok⟩
  have hSend : X.get (g,index) = some sent := hBroadcast
  have hBefore : index < j := by
    apply traceOrderOfPcFloor hX (initialScoreIssueFloor stage)
      (initialScoreIssueSegments stage) hSend he
    · change pc < 2153+62*stage.val
      omega
    · omega
  have hLength : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨base,s,_,hBase,hs,hWalk⟩ := initialMmaTrace hp hX hSend hLo hHi
  let es := (X.tr g).drop (base+1)
  have hLookup : es[index-(base+1)]? = some sent := by
    dsimp only [es]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  have hRel : index-(base+1)+1 < es.length := by
    dsimp only [es]
    rw [List.length_drop]
    omega
  have hSRole : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  obtain ⟨t,u,vs,hStep,hShape,hUWalk⟩ :=
    pvRoleAfterEvent hWalk (by rw [hs.1]; decide) hSRole hLookup hRel hHi
  obtain ⟨hU,hReg⟩ := initialScoreBroadcastFrame stage ok hStep
  have hSuffix : es.drop (index-(base+1)+1) = (X.tr g).drop (index+1) := by
    rw [show es = (X.tr g).drop (base+1) from rfl,List.drop_drop,
      show base+1+(index-(base+1)+1) = index+1 by omega]
  rw [hSuffix] at hUWalk
  have hLater : e ∈ (X.tr g).drop (index+1) := by
    apply List.mem_of_getElem? (i := j-(index+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBefore]
  let F := [(scoreBroadcastRegister stage,b32 col)]
  have hAudit : ((kernel.code.drop (pc+1)).take (pc+2-(pc+1))).all
      (pvCutCode (pc+1) (pc+2) (F.map Prod.fst)) = true := by
    fin_cases stage <;> kernel_rfl
  have hUPc : u.pc = pc+1 := by omega
  obtain ⟨v,_,rem,_,_,hV,hVShape,hVF,hVWalk,hVMem,_⟩ :=
    pvWalkCut (F := F) (show 1907 ≤ pc+1 by omega) (show pc+2 < 2768 by omega) hAudit hUWalk
      (by rw [hUPc]; omega) hShape (show Holds u.regs F from ⟨hReg,trivial⟩) hLater
      hTarget.1.le
  have hvAt : At v (2154+62*stage.val) (F++[(1062,b32 12)]) :=
    ⟨show v.pc = _ by omega,hVShape.1.2.2 (by omega),hVShape.1.2.1,
      normalBeforeLaterEvent hVWalk hVMem (by omega),hVF.1,hVShape.2,trivial⟩
  obtain ⟨w,_,hwAt,hwWalk⟩ :=
    requireReadySegmentNonempty (initialScoreSetDestination stage) hvAt hVWalk
      (fun hn => by rw [hn] at hVMem; cases hVMem)
  let begin := 2155+62*stage.val
  let finish := qkPc (initialQkBlock stage)+step.val
  have hBank : begin ≤ finish := by fin_cases stage <;> fin_cases step <;> decide
  have hWrites : ((kernel.code.drop begin).take (finish-begin)).all
      (pvCutCode begin finish [dst]) = true := by
    fin_cases stage <;> fin_cases step <;> kernel_rfl
  have hwShape : RoleShape w ∧ w.regs 1062 = some (b32 12) :=
    ⟨⟨hwAt.2.1.symm ▸ Nat.zero_le _,hwAt.2.2.1,fun _ => hwAt.2.1⟩,hwAt.2.2.2.2.2.1⟩
  obtain ⟨z,_,es,vs,_,hz,_,hZ,hZWalk,hMem,_⟩ :=
    pvWalkCut (F := [(dst,b32 col)]) (show 1907 ≤ begin by omega)
      (show finish < 2768 by omega) hWrites hwWalk
      (by rw [hwAt.1]; exact ⟨le_rfl,hBank⟩) hwShape ⟨hwAt.2.2.2.2.1,trivial⟩
      hVMem hPc.symm.le
  exact ⟨z,es,vs,hz.trans hPc.symm,hZ.1,hZWalk,hMem⟩

end PTX.Kernels.TmlFa4Fwd.Thread
