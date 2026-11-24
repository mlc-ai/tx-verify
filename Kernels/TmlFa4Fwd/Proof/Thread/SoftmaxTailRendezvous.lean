-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailIssuer
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
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
import Lemmas.Order.WarpBarOrdinal
import Lemmas.Flow.NotWarpBar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.AsyncCopy Softmax

private def barHead (r : Round) : Nat := probabilityWaitPc r true + 1
private def electHead (r : Round) : Nat := barHead r + 1

private theorem barCode (r : Round) :
    kernel.code[barHead r]? = some ⟨none,.warp ⟨.barWarp,none,[],[],some (.imm (-1))⟩⟩ := by
  cases r
  · exact Flow.code_4858
  · exact Flow.code_6543
  · exact Flow.code_7448

private theorem electCode (r : Round) :
    kernel.code[electHead r]? = some ⟨none,.warp ⟨.elect,none,
      [some (tailElectLane r),some (tailElectPred r)],[],some (.imm (-1))⟩⟩ := by
  cases r
  · exact Flow.code_4859
  · exact Flow.code_6544
  · exact Flow.code_7449

private def jumpsAround (r : Round) (i : Instr) : Bool :=
  match i.op with
  | .bra dst _ => dst != electHead r
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem noJumpToTailElection (r : Round) :
    kernel.code.all (jumpsAround r) = true := by
  cases r <;> kernel_rfl

private theorem noSegmentToTailElection (r : Round) {site : Nat} {seg : SegMatch CuteSlot}
    (hSite : site ∈ Assumptions.swExp2Sites) (hMatch : cuteExp2.matchAt kernel site = some seg) :
    seg.stop ≠ electHead r := by
  have audit : Assumptions.swExp2Sites.all (fun i =>
      match cuteExp2.matchAt kernel i with
      | some s => s.stop != electHead r
      | none => false) = true := by
    cases r <;> set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp audit site hSite
  simpa [hMatch] using h

private theorem noTauToTailElection {l : Launch} {g : Nat} {s u : TState} (r : Round)
    (hTau : Tau kernel Assumptions.all l g s u) : u.pc ≠ electHead r := by
  intro hDest
  obtain ⟨i,hCode,_,hExec⟩ := tauScoreSource hTau
  have hNext : u.pc = s.pc+1 := by
    rcases hExec with ⟨rfl,_⟩ | ⟨_,_,hLocal⟩
    · rfl
    rcases scoreExecLocal hLocal with hFrame | ⟨seg,hSite,hMatch,hSeg⟩
    · have hAudit := List.all_eq_true.mp (noJumpToTailElection r) i (List.mem_of_getElem? hCode)
      have hPc := hFrame.pc
      cases hop : i.op <;> simp only [hop,nextPc,BrxTarget,or_false] at hPc
      case bra dst uni =>
        rw [hPc] at hDest
        simp [jumpsAround,hop,hDest] at hAudit
      case brx => simp [jumpsAround,hop] at hAudit
      all_goals exact hPc
    · exact (noSegmentToTailElection r hSite hMatch ((scoreSegmentFrame hSeg).1 ▸ hDest)).elim
  have hSource : s.pc = barHead r := by unfold electHead at hDest; omega
  rw [hSource,barCode r] at hCode
  obtain rfl := Option.some.inj hCode.symm
  rcases hExec with ⟨_,hSkip⟩ | ⟨_,hLocal,_⟩
  · cases hSkip
  · cases hLocal

/-- Every lane participates in the full mask of the softmax tail barrier. -/
theorem allLanesInTailMask (l : Launch) (g : Nat) :
    electMember (2^32-1) (laneOf l g) := by
  have h (lane : Fin 32) : electMember (2^32-1) lane.val := by
    fin_cases lane <;> decide
  exact h ⟨_,Nat.mod_lt _ (by decide)⟩

private theorem tailBarReturn {l : Launch} {g : Nat} {s u : TState} {e : Event} (r : Round)
    (hPc : s.pc = barHead r) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ inst, e = ⟨barHead r,.warpBar (2^32-1) inst⟩ ∧ u.pc = electHead r := by
  obtain ⟨_,hc,_,hf⟩ := estep_event_source he
  rw [hPc,barCode r] at hc
  obtain rfl := Option.some.inj hc.symm
  change Fires s.pc (warpBarTmpl l g s (.imm (-1))) e (some u) at hf
  have hMask : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2^32-1 := by decide
  simp only [warpBarTmpl,readBits,pure,Except.pure,hMask,allLanesInTailMask,↓reduceIte] at hf
  obtain ⟨inst,hEvent,hNext⟩ := hf
  obtain rfl := Option.some.inj hNext
  exact ⟨inst,hPc ▸ hEvent,congrArg (· + 1) hPc⟩

private theorem eventToTailElection {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (r : Round) (he : EStep kernel Assumptions.all l g s e (some u))
    (hDest : u.pc = electHead r) : ∃ inst, e = ⟨barHead r,.warpBar (2^32-1) inst⟩ := by
  obtain ⟨i,hCode,hLocal,hFire⟩ := estep_event_source he
  have audit : kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true :=
    by decide +kernel
  have hOp := List.all_eq_true.mp audit i (List.mem_of_getElem? hCode)
  have hFrame : ReturnedFrame s.pc (eventTmpl Assumptions.all l g s i.op) :=
    Epilogue.ordinaryEventFrame (by simpa only [hLocal,Bool.false_or] using hOp)
  rcases callbackFrame_fires hFrame hFire with hSame | hNext
  · have hPc := hSame.symm.trans hDest
    rw [hPc,electCode r] at hCode
    obtain rfl := Option.some.inj hCode.symm
    change Fires s.pc (eventTmpl Assumptions.all l g s (.warp ⟨.elect,none,
      [some (tailElectLane r),some (tailElectPred r)],[],some (.imm (-1))⟩)) e (some u) at hFire
    obtain ⟨_,_,leader,_,hAfter⟩ := fires_elect hFire
    rw [hAfter] at hSame
    change s.pc+1 = s.pc at hSame
    omega
  · have hPc : s.pc = barHead r := by unfold electHead at hDest; omega
    obtain ⟨inst,hE,_⟩ := tailBarReturn r hPc he
    exact ⟨inst,hE⟩

private theorem lastEventBeforeTailElection {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (r : Round) (hReach : TraceReach kernel Assumptions.all l g s es u)
    {eventsBefore : List Event}
    (hStart : s.pc = electHead r → ∃ xs inst,
      eventsBefore = xs ++ [⟨barHead r,.warpBar (2^32-1) inst⟩])
    (hEnd : u.pc = electHead r) :
    ∃ xs inst, eventsBefore ++ es = xs ++ [⟨barHead r,.warpBar (2^32-1) inst⟩] := by
  induction hReach generalizing eventsBefore with
  | refl => simpa using hStart hEnd
  | tau ht _ ih => exact ih (fun h => (noTauToTailElection r ht h).elim) hEnd
  | @event s t u es e ht _ ih =>
    rw [← List.singleton_append, ← List.append_assoc]
    apply ih (eventsBefore := eventsBefore ++ [e]) _ hEnd
    intro h
    obtain ⟨inst,rfl⟩ := eventToTailElection r ht h
    exact ⟨eventsBefore,inst,rfl⟩

/-- Each actual tail election immediately follows its full-warp barrier. -/
theorem tailBarrierBeforeElection {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (r : Round)
    {g j inst leader : Nat}
    (he : X.Elect (g,j) (probabilityWaitPc r true+2) (2^32-1) inst leader) :
    ∃ k barInst, k+1 = j ∧ X.WarpBar (g,k) (2^32-1) barInst := by
  obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s,_,hReach,hStep⟩ := hRun.before_event he
  have hSite : s.pc = electHead r := by
    exact (estep_source_pc hStep).symm
  obtain ⟨xs,bar,hSplit⟩ := lastEventBeforeTailElection r hReach (eventsBefore := [])
    (fun h => by cases r <;> cases h) hSite
  simp only [List.nil_append] at hSplit
  have hSize := congrArg List.length hSplit
  have hj := len_of_get he
  simp only [List.length_take,List.length_append,List.length_singleton,Nat.min_eq_left hj.le]
    at hSize
  refine ⟨xs.length,bar,hSize.symm,barHead r,?_⟩
  have hk : xs.length < j := by omega
  change (X.tr g)[xs.length]? = _
  rw [← List.getElem?_take_of_lt hk,hSplit,List.getElem?_append_right le_rfl,Nat.sub_self]
  rfl

private def isWarpBarrierOp : Op → Bool
  | .warp w => match w.kind with | .barWarp => true | _ => false
  | _ => false

/-- The decoded softmax tail sites are the kernel's only warp barriers. -/
theorem warpBarrierSite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {pc mask inst : Nat} (he : X.get i = some ⟨pc,.warpBar mask inst⟩) :
    pc ∈ [4858,6543,7448] := by
  rcases get_source hX he with ⟨_,hBad⟩ | ⟨_,ins,_,_,hCode,hFire⟩
  · cases hBad
  have hOp : isWarpBarrierOp ins.op = true := by
    cases h : isWarpBarrierOp ins.op
    · have notBar (w : WarpInstr) (he : ins.op = .warp w) (hk : w.kind = .barWarp) : False := by
        simp [he,isWarpBarrierOp,hk] at h
      exact (fires_notWarpBar_op notBar hFire mask inst rfl).elim
    · rfl
  have hAudit : OpPcsFast kernel.code isWarpBarrierOp [4858,6543,7448] = true :=
    by decide +kernel
  exact OpPcsFast.mem hAudit hCode hOp

/-- Actual warp rendezvous events use all 32 lanes. -/
theorem actualFullWarpBarrier {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {mask inst : Nat} (h : X.WarpBar i mask inst) : mask = 2^32-1 := by
  obtain ⟨source,he⟩ := h
  have hSite := warpBarrierSite hX he
  have hDecoded : ∃ r : Round, source = barHead r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
    rcases hSite with rfl | rfl | rfl
    · exact ⟨.first,rfl⟩
    · exact ⟨.biased,rfl⟩
    · exact ⟨.unbiased,rfl⟩
  obtain ⟨r,rfl⟩ := hDecoded
  rcases get_source hX he with ⟨_,hBad⟩ | ⟨s,ins,u,_,hCode,hFire⟩
  · cases hBad
  change kernel.code[barHead r]? = some ins at hCode
  rw [barCode r] at hCode
  obtain rfl := Option.some.inj hCode.symm
  change Fires (barHead r) (warpBarTmpl l i.1 s (.imm (-1))) _ u at hFire
  have hMask : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2^32-1 := by decide
  simp only [warpBarTmpl,readBits,pure,Except.pure,hMask,allLanesInTailMask,↓reduceIte,Fires]
    at hFire
  obtain ⟨_,hKind,_⟩ := hFire
  exact (Kind.warpBar.inj (congrArg Event.kind hKind)).1

private theorem firstTailBarFloor :
    (kernel.code.drop 4859).all (fun i => staysPastEvent 4859 i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem firstTailBarSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (4859 ≤ seg.stop)
      | none => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem firstTailBarIsFirst {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j k inst mask other : Nat}
    (he : X.get (g,j) = some ⟨4858,.warpBar (2^32-1) inst⟩)
    (hOther : X.WarpBar (g,k) mask other) : j ≤ k := by
  by_contra! hEarly
  obtain ⟨pc,hGet⟩ := hOther
  by_cases hPc : pc = 4858
  · subst pc
    obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX he)
    have hLength : j < (X.tr g).length := len_of_get he
    obtain ⟨s,u,hStep,hAfter⟩ := hRun.after_event hGet (by omega)
    have hSource : s.pc = barHead .first := (estep_source_pc hStep).symm
    obtain ⟨_,_,hNext⟩ := tailBarReturn .first hSource hStep
    obtain ⟨_,hWalk⟩ := Mma.walkFromRun hAfter
    have hMem : ⟨4858,.warpBar (2^32-1) inst⟩ ∈ (X.tr g).drop (k+1) := by
      apply List.mem_of_getElem? (i := j-(k+1))
      rwa [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
    have hBound := eventTailEvents firstTailBarFloor firstTailBarSegments hWalk
      (show 4859 ≤ u.pc from hNext.symm ▸ le_rfl) _ hMem
    exact (by decide : ¬ (4859 : Nat) ≤ 4858) hBound
  · have hSite := warpBarrierSite hX hGet
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hSite
    have hAfter := traceOrderOfPcFloor hX firstTailBarFloor firstTailBarSegments he hGet
      (show 4858 < 4859 by decide) (by dsimp; omega)
    omega

/-- The first-round tail store wait orders its writes before the elected credit
of the same warp, using the real full-warp barrier of the first round. -/
theorem firstTailBarrierBeforeWarpCredit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j inst : Nat} {credit : EvId} {stage : Fin 2}
    (hSame : SameWarp l g credit.1)
    (hBar : X.get (g,j) = some ⟨4858,.warpBar (2^32-1) inst⟩)
    (hCredit : ProbabilityCredit l X credit (g/l.block) stage 1) {before : Nat}
    (hBefore : before < j) : baseCausality l X (g,before) credit := by
  obtain ⟨h,k⟩ := credit
  obtain ⟨r,e,hE,elect,hElect⟩ := tailCreditElectionBefore hp hX stage hCredit
  obtain ⟨y,peerInst,hY,hPeerBar⟩ := tailBarrierBeforeElection hX r hElect
  have hOwn : X.WarpBar (g,j) (2^32-1) inst := ⟨4858,hBar⟩
  obtain ⟨x,hMatch⟩ := WarpBar.partner hX hSame hOwn (allLanesInTailMask l h)
  obtain ⟨other,hPeerMatch⟩ := WarpBar.partner hX (sameWarp_symm hSame)
    hPeerBar (allLanesInTailMask l g)
  obtain ⟨mask,instanceId,hPeer,hOther⟩ := hPeerMatch
  have hFirst := firstTailBarIsFirst hX hBar hOther
  have hOrder : x ≤ y := by
    rcases Nat.eq_or_lt_of_le hFirst with rfl | hLt
    · obtain ⟨mask',instanceId',hA,hB⟩ := hMatch
      obtain ⟨_,hSameA⟩ := hA
      obtain ⟨_,hSameB⟩ := hOther
      rw [hSameA] at hSameB
      obtain ⟨rfl,rfl⟩ := Kind.warpBar.inj (congrArg Event.kind (Option.some.inj hSameB))
      have hEq := (hX.warpBar.2 (h,x) (h,y) _ _ _ hB hPeer
        (sameWarp_self hSame.1.2.1)).2 rfl
      exact (congrArg Prod.snd hEq).le
    · exact (WarpBar.mono hX hSame hMatch ⟨mask,instanceId,hOther,hPeer⟩ hLt).le
  obtain ⟨_,hNotice⟩ := hCredit
  have hK : k < (X.tr h).length := len_of_get hNotice
  exact WarpBar.sync hSame hMatch hBefore (by omega) hK

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
