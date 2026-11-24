-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady
import Kernels.TmlFa4Fwd.Proof.MmaInitialValueCursor
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.NotClc
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.EventFrame

private def bySite (target : Event) (e : Event) : Option Event :=
  if e.pc = target.pc then some e else none

private theorem targeted {e : Event} {es : List Event} (he : e ∈ es) :
    es.filterMap (bySite e) ≠ [] := by
  have h : e ∈ es.filterMap (bySite e) := List.mem_filterMap.mpr ⟨e,he,by simp [bySite]⟩
  exact fun hNil => by rw [hNil] at h; cases h

private theorem targetInTail {e : Event} {es pre tail : List Event} (h : es = pre ++ tail)
    (hPre : pre.filterMap (bySite e) = []) (he : e ∈ es) : e ∈ tail := by
  rw [h] at he
  apply (List.mem_append.mp he).resolve_left
  intro hm
  exact targeted hm hPre

private theorem readyIntervalBefore {l : Launch} {g : Nat} (i : Fin 9)
    {t : TState} {F : List (Nat × Value)} {es : List Event} {vs : List Visit} {e : Event}
    (hPc : (readyInterval i).lo ≤ t.pc ∧ t.pc < (readyInterval i).hi)
    (ht : At t t.pc F) (hWarp : (1062,b32 12) ∈ F)
    (hKeep : ∀ r ∈ F.map Prod.fst, r = 1062 ∨ r ∈ (readyInterval i).keep)
    (hw : Walk kernel Assumptions.all l g t es vs)
    (he : e ∈ es) (hLater : (readyInterval i).hi ≤ e.pc) :
    ∃ u pre tail visits, u.pc ∈ (readyInterval i).exits ∧ At u u.pc F ∧
      es = pre ++ tail ∧ e ∈ tail ∧ Walk kernel Assumptions.all l g u tail visits := by
  obtain ⟨u,pre,tail,visits,hExit,hu,hSplit,hPre,hWalk⟩ :=
    requireReadyIntervalWith (bySite e) i (fun event h => by
      have hHi := h.2
      simp [bySite,show event.pc ≠ e.pc by omega])
      hPc ht hWarp hKeep hw (targeted he)
  exact ⟨u,pre,tail,visits,hExit,hu,hSplit,targetInTail hSplit hPre he,hWalk⟩

private theorem readyPollBefore {l : Launch} {g addr phase : Nat} {t : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit} {target : Event}
    (i : Fin 14) (ha : addr < 2^32) (hal : addr % 8 = 0) (hp : phase < 2)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (waitSite i).result)
    (hBase : ((waitSite i).base,b32 addr) ∈ F) (hPar : ((waitSite i).phase,b32 phase) ∈ F)
    (ht : At t (waitSite i).pc F) (hw : Walk kernel Assumptions.all l g t es vs)
    (he : target ∈ es) (hLate : (waitSite i).pc < target.pc) :
    let event := Event.mk (waitSite i).pc
      (.wait ⟨.shared,g/l.block,addr⟩ phase true true .cta)
    ∃ u pre tail visits, es = pre ++ event :: tail ∧ At u ((waitSite i).pc+3) F ∧
      Walk kernel Assumptions.all l g u tail visits ∧ target ∈ tail := by
  dsimp only
  let event (ok : Bool) :=
    Event.mk (waitSite i).pc (.wait ⟨.shared,g/l.block,addr⟩ phase ok true .cta)
  have hNo (ok : Bool) : target ≠ event ok := by
    intro h
    have hPc := congrArg Event.pc h
    change target.pc = (waitSite i).pc at hPc
    omega
  rcases waitWalk i ha hal hp hFresh hBase hPar ht hw with ⟨n,hSplit⟩ |
      ⟨n,tail,hSplit,hTail⟩
  · change es = List.replicate n (event false) at hSplit
    rw [hSplit] at he
    exact (hNo false (List.mem_replicate.mp he).2).elim
  · change es = List.replicate n (event false) ++ event true :: tail at hSplit
    have hFound : target ∈ tail := by
      rw [hSplit] at he
      have h₁ := (List.mem_append.mp he).resolve_left
        (fun h => hNo false (List.mem_replicate.mp h).2)
      exact (List.mem_cons.mp h₁).resolve_left (hNo true)
    rcases hTail with rfl | ⟨u,post,_,hu,hWalk⟩
    · cases hFound
    · exact ⟨u,_,tail,post,hSplit,hu,hWalk,hFound⟩

set_option maxRecDepth 100000 in
private theorem afterTailBranch :
    (kernel.code.drop 2534).all (fun i => Thread.staysPastEvent 2534 i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterTailSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2534 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem noEarlierExitCode :
    (kernel.code.take 2355).all
      (fun i => match i.op with | .exit | .ret => false | _ => true) = true := by
  kernel_rfl

private theorem exitFloor {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g index pc : Nat}
    (he : X.get (g,index) = some ⟨pc,.exit⟩) : 2355 ≤ pc := by
  by_contra! hEarly
  obtain ⟨_,hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s,_,_,hStep⟩ := hRun.before_event he
  have hPc : s.pc = pc := (estep_source_pc hStep).symm
  obtain ⟨tm,hOut,hFire⟩ := hStep
  rcases out_ev hOut with ⟨fault,rfl⟩ | ⟨i,hCode,rfl⟩
  · cases (congrArg Event.kind hFire.1)
  · have hMem : i ∈ kernel.code.take 2355 := by
      apply List.mem_of_getElem? (i := pc)
      rw [List.getElem?_take, ite_eq_left hEarly]
      simpa only [hPc] using hCode
    have hNot := List.all_eq_true.mp noEarlierExitCode i hMem
    rcases fires_exit_op hFire rfl with h | h <;> simp [h] at hNot

private theorem suffixLast {α : Type} {pre tail : List α} {event : α}
    (h : (pre ++ tail).getLast? = some event) (hNonempty : tail ≠ []) :
    tail.getLast? = some event := by
  rw [List.getLast?_append] at h
  cases hTail : tail.getLast? with
  | none => exact (hNonempty (List.getLast?_eq_none_iff.mp hTail)).elim
  | some _ => simpa [hTail] using h

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e)
include hp hX he

private theorem thirdReadyOfSteadyEvent (hBounds : 2295 ≤ e.pc ∧ e.pc < 2534)
    (hFinishes : 2355 ≤ e.pc ∨ ∃ pc, (X.tr g).getLast? = some ⟨pc,.exit⟩) :
    ∃ j, Thread.Mma.ReadyPoll l X g j 2 0 true .cta := by
  obtain ⟨base,t,_,hIndex,ht,hWalk⟩ :=
    initialMmaTrace hp hX he (by omega) (by omega)
  let trail := (X.tr g).drop (base+1)
  have hEvent : e ∈ trail := by
    apply List.mem_of_getElem? (i := index-(base+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hIndex]
  have ht' : At t 1908 (readyFrame l) :=
    ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2.2.1,ht.2.2.2.2.1,by simp⟩
  obtain ⟨u,pre,suffix,_,huPc,hu,hSplit,hRest,huWalk⟩ :=
    readyIntervalBefore 0 (by rw [ht'.1]; decide) ⟨rfl,ht'.2⟩
      (by simp [readyFrame]) (by simp [readyFrame,readyInterval]) hWalk hEvent
      (show 2140 ≤ e.pc by omega)
  have huSite : u.pc = 2140 ∨ u.pc = 2763 := by simpa [readyInterval] using huPc
  rcases huSite with huSite | huSite
  swap
  · have hBad := Thread.eventTailEvents afterTailBranch afterTailSegments huWalk
      (show 2534 ≤ u.pc by omega) _ hRest
    omega
  obtain ⟨v,_,hv,hvWalk⟩ :=
    requireReadySegmentNonempty (readyInitialPhase l g) ⟨huSite,hu.2⟩ huWalk
      (by intro h; rw [h] at hRest; cases hRest)
  obtain ⟨w,pre',suffix',_,hwPc,hw,hSplit',hRest',hwWalk⟩ :=
    readyIntervalBefore 1 (by rw [hv.1]; decide) ⟨rfl,hv.2⟩
      (by simp [readyFrame]) (by simp [readyFrame,readyInterval]) hvWalk hRest
      (show 2144 ≤ e.pc by omega)
  have hw' : At w 2144 ((2536,b32 0)::readyFrame l) :=
    ⟨by simpa [readyInterval] using hwPc,hw.2⟩
  obtain ⟨z,_,hz,hzWalk⟩ :=
    requireReadySegmentNonempty (readyInitialAddress hp g) hw' hwWalk
      (by intro h; rw [h] at hRest'; cases hRest')
  have ha : l.sharedBase+32 < 2^32 := by have := hp.shared.2.1; omega
  have hal : (l.sharedBase+32) % 8 = 0 := by have := hp.shared.1; omega
  obtain ⟨k,kPre,kTail,_,hkSplit,hk,hkWalk,hKMem⟩ :=
    readyPollBefore 1 ha hal (show 0 < 2 by decide)
      (by simp [waitSite,readyFrame]) (by simp [waitSite]) (by simp [waitSite])
      hz hzWalk hRest' (show 2145 < e.pc by omega)
  have hk' : At k 2148 (readyFrame l) :=
    ⟨hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.2.2⟩
  obtain ⟨steady,c,cPre,cTail,_,hcSplit,hCPre,hc,hcWalk⟩ :=
    initialValueWaitThroughRoute (bySite e) (fun i event h => by
      have hn : event.pc ≠ e.pc := by
        fin_cases i
        · change 2148 ≤ event.pc ∧ event.pc < 2280 at h
          omega
        · change 2284 ≤ event.pc ∧ event.pc < 2287 at h
          omega
        · change 2534 ≤ event.pc ∧ event.pc < 2542 at h
          omega
      simp [bySite,hn]) ⟨rfl,hk'.2⟩ (by rw [hk'.1]; decide) hkWalk (targeted hKMem) hp
  have hCMem := targetInTail hcSplit hCPre hKMem
  cases steady
  · have hcPc : c.pc = 2545 := hc.1
    have hBad := Thread.eventTailEvents afterTailBranch afterTailSegments hcWalk
      (show 2534 ≤ c.pc by omega) _ hCMem
    omega
  · have hAddr : readyAddr l 1 < 2^32 := by
      have := hp.shared.2.1
      unfold readyAddr
      omega
    have hAlign : readyAddr l 1 % 8 = 0 := by
      have := hp.shared.1
      unfold readyAddr
      omega
    obtain ⟨val,valPre,valTail,_,hValSplit,hVal,hValWalk,hValMem⟩ :=
      readyPollBefore 3 hAddr hAlign (readyWord_lt 1)
        (by simp [waitSite,initialValueWaitFacts,initialValueWaitSite,ringFrame,readyFrame])
        (by simp [waitSite,initialValueWaitFacts,initialValueWaitSite])
        (by simp [waitSite,initialValueWaitFacts,initialValueWaitSite,ringFrame])
        hc hcWalk hCMem (show 2294 < e.pc by omega)
    obtain ⟨target,hTarget,hTargetPc⟩ : ∃ target : Event, target ∈ valTail ∧ 2355 ≤ target.pc := by
      rcases hFinishes with hLate | ⟨pc,hExit⟩
      · exact ⟨e,hValMem,hLate⟩
      · let exit : Event := ⟨pc,.exit⟩
        have hNonempty {xs : List Event} (hm : e ∈ xs) : xs ≠ [] :=
          fun h => by rw [h] at hm; cases hm
        have hLen : index < (X.tr g).length := PTX.len_of_get he
        have hTrailExit : ((X.tr g).drop (base+1)).getLast? = some exit := by
          rw [List.getLast?_drop,ite_eq_right (by omega),hExit]
        rw [hSplit] at hTrailExit
        have hSuffixExit := suffixLast hTrailExit (hNonempty hRest)
        rw [hSplit'] at hSuffixExit
        have hSuffixExit' := suffixLast hSuffixExit (hNonempty hRest')
        rw [hkSplit] at hSuffixExit'
        have hKHeadExit := suffixLast hSuffixExit' (List.cons_ne_nil _ _)
        rw [List.getLast?_cons_of_ne_nil (hNonempty hKMem)] at hKHeadExit
        have hKTailExit := hKHeadExit
        rw [hcSplit] at hKTailExit
        have hCTailExit := suffixLast hKTailExit (hNonempty hCMem)
        rw [hValSplit] at hCTailExit
        have hValExit := suffixLast hCTailExit (List.cons_ne_nil _ _)
        rw [List.getLast?_cons_of_ne_nil (hNonempty hValMem)] at hValExit
        have hExitGet : X.get (g,(X.tr g).length-1) = some ⟨pc,.exit⟩ := by
          change (X.tr g)[(X.tr g).length-1]? = some ⟨pc,.exit⟩
          simpa only [List.getLast?_eq_getElem?] using hExit
        exact ⟨exit,List.mem_of_getLast? hValExit,exitFloor hX hExitGet⟩
    have hVal' : At val 2297 (ringFrame l 7207 7208 1) := hVal.mono hVal.2.2.2.2.2
    obtain ⟨d,dPre,dTail,_,hdPc,hd,hDSplit,hDMem,hdWalk⟩ :=
      readyIntervalBefore 4 (by rw [hVal'.1]; decide) ⟨rfl,hVal'.2⟩
        (by simp [ringFrame,readyFrame]) (by simp [ringFrame,readyFrame,readyInterval])
        hValWalk hTarget (show 2344 ≤ target.pc by omega)
    have hd' : At d 2344 (ringFrame l 7207 7208 1) :=
      ⟨by simpa [readyInterval] using hdPc,hd.2⟩
    obtain ⟨f,_,hf,hfWalk⟩ :=
      requireReadySegmentNonempty (readyAdvanceFramed l g 0 1) hd' hdWalk
        (by intro h; rw [h] at hDMem; cases hDMem)
    obtain ⟨a,_,ha,haWalk⟩ :=
      requireReadySegmentNonempty (readyAddress hp g 1 2) hf hfWalk
        (by intro h; rw [h] at hDMem; cases hDMem)
    have hAddr : readyAddr l 2 < 2^32 := by
      have := hp.shared.2.1
      unfold readyAddr
      omega
    have hAlign : readyAddr l 2 % 8 = 0 := by
      have := hp.shared.1
      unfold readyAddr
      omega
    obtain ⟨_,keyPre,keyTail,_,hKeySplit,_,_,_⟩ :=
      readyPollBefore 6 hAddr hAlign (readyWord_lt 2)
        (by simp [waitSite,readyAddressSite,ringFrame,readyFrame])
        (by simp [waitSite,readyAddressSite])
        (by simp [waitSite,readyAddressSite,ringFrame])
        ha haWalk hDMem (show 2352 < target.pc by omega)
    let evt : Event := ⟨2352,.wait ⟨.shared,g/l.block,readyAddr l 2⟩ 0 true true .cta⟩
    have hKey : evt ∈ dTail := by
      rw [hKeySplit]
      exact List.mem_append_right _ List.mem_cons_self
    have hInValTail : evt ∈ valTail := by
      rw [hDSplit]
      exact List.mem_append_right _ hKey
    have hInCTail : evt ∈ cTail := by
      rw [hValSplit]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hInValTail)
    have hInKTail : evt ∈ kTail := by
      rw [hcSplit]
      exact List.mem_append_right _ hInCTail
    have hInSuffix' : evt ∈ suffix' := by
      rw [hkSplit]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hInKTail)
    have hTrace : evt ∈ (X.tr g) := by
      apply (List.drop_sublist (base+1) (X.tr g)).subset
      rw [hSplit,hSplit']
      exact List.mem_append_right _ (List.mem_append_right _ hInSuffix')
    obtain ⟨j,hj,hGet⟩ := List.getElem_of_mem hTrace
    have hLookup : (X.tr g)[j]? = some evt := by rw [List.getElem?_eq_getElem hj,hGet]
    refine ⟨j,evt,hLookup,?_⟩
    simp [evt, Thread.Mma.Observation.readyObject, Loader.readySlot_address, readyAddr,
      readyStage, Nat.add_assoc]
    decide

/-- A late steady event forces completion of the third logical K/V acquire, in slot two. -/
theorem thirdReadyBeforeSteadyEvent (hBounds : 2355 ≤ e.pc ∧ e.pc < 2534) :
    ∃ j, Thread.Mma.ReadyPoll l X g j 2 0 true .cta :=
  thirdReadyOfSteadyEvent hp hX he ⟨by omega,hBounds.2⟩ (.inl hBounds.1)

/-- A normal exit after entry to the steady PV body requires the third K/V acquire. -/
theorem thirdReadyOfFinishingSteadyEvent (hBounds : 2295 ≤ e.pc ∧ e.pc < 2534)
    (hExit : ∃ pc, (X.tr g).getLast? = some ⟨pc,.exit⟩) :
    ∃ j, Thread.Mma.ReadyPoll l X g j 2 0 true .cta :=
  thirdReadyOfSteadyEvent hp hX he hBounds (.inr hExit)

end PTX.Kernels.TmlFa4Fwd.Mma
