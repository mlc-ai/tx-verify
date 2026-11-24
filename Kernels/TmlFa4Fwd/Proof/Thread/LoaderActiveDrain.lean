-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWitness
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainNoReentry
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader
  (actualAsyncArrival actualEmptySeedPrefix actualPrimingEmptyPrefix prefixStableCut
    loaderPipelineCutOp)

noncomputable section

private theorem runFromWalkExit {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (he : (⟨9205,.exit⟩ : Event) ∈ es) : Run kernel Assumptions.all l g s es none := by
  induction hw with
  | stop => cases he
  | tau ht _ ih =>
    cases ih he with
    | step hstep hEvent hTail => exact .step (.head ht hstep) hEvent hTail
    | last hstep hEvent => exact .last (.head ht hstep) hEvent
  | ev hEvent _ ih =>
    have ⟨_, _, hFired⟩ := hEvent
    exact .step .refl hEvent (ih ((List.mem_cons.mp he).resolve_left (Ne.symm hFired.not_exit)))
  | last hEvent => exact .last .refl hEvent

private theorem exitInDrop {X : Execution} {g start finish : Nat}
    (he : X.get (g,finish) = some ⟨9205,.exit⟩) (hStart : start ≤ finish) :
    (⟨9205,.exit⟩ : Event) ∈ (X.tr g).drop start := by
  apply List.mem_of_getElem? (i := finish - start)
  rw [List.getElem?_drop, Nat.add_sub_of_le hStart]
  exact he

private theorem exitAfterPublication {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i site : Nat} {loc : Loc}
    (hPub : X.get (g,i) = some ⟨site,.asyncArrive loc true⟩)
    (hExit : Thread.Exited X g) :
    ∃ finish, i < finish ∧ X.get (g,finish) = some ⟨9205,.exit⟩ := by
  obtain ⟨exitSite,hLast⟩ := hExit.lastEvent hX (event_thread_lt hX hPub)
  let finish := (X.tr g).length - 1
  have he : X.get (g,finish) = some ⟨exitSite,.exit⟩ := by
    change (X.tr g)[finish]? = _
    rwa [← List.getLast?_eq_getElem?]
  obtain rfl := actualExitPc hX he
  refine ⟨finish, ?_, he⟩
  have hLen := (List.getElem?_eq_some_iff.mp hPub).1
  by_contra! h
  have hSame : i = finish := by dsimp [finish] at *; omega
  rw [hSame,he] at hPub
  cases hPub

private theorem primingToDrainSeed {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g i finish : Nat} {loc : Loc}
    (hPub : X.get (g,i) = some ⟨(if stage = 0 then 674 else 904), .asyncArrive loc true⟩)
    (hLater : i < finish) (he : X.get (g,finish) = some ⟨9205,.exit⟩) :
    ∃ pos t visits, pos ≤ finish ∧ At t 909 [(2535,b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop pos) visits := by
  obtain ⟨start,s,vs,hStart,hs,hw,_⟩ := actualPrimingEmptyPrefix hp hX stage hPub
  have hExit := exitInDrop he (hStart.trans hLater.le)
  have hRun := runFromWalkExit hw hExit
  let lower := if stage = 0 then 515 else 780
  have hBounds : 174 ≤ lower ∧ lower ≤ 909 ∧ 909 ≤ 1901 := by
    fin_cases stage <;> (decide +revert)
  have hAudit : ∀ branch, ((kernel.code.drop lower).take (909 - lower)).all
      (fun ins => loaderPipelineCutOp lower 909 branch [2535] ins.op) = true := by
    intro branch
    fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨t,pre,result,_,ht,hRun,_,hPos⟩ :=
    prefixStableCut (F := [(2535,b32 l.sharedBase)]) hBounds hAudit hs hRun he
      (hStart.trans hLater.le) (by intro f h; cases h)
      (fun _ => 0) (fun _ => false) (.inl (show 909 ≤ 9205 by decide))
      (by intros; rfl) (by intros; rfl) (by intros; simp)
  obtain ⟨visits,hWalk⟩ := Mma.walkFromRun hRun
  exact ⟨start+pre.length,t,visits,hPos,ht,hWalk⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {loc : Loc}
    (hPub : X.AsyncArrive (g,index) loc true)
include hp hX hPub

private theorem actualDrainSeed (hExit : Thread.Exited X g) :
    ∃ pos finish t visits, pos ≤ finish ∧ X.get (g,finish) = some ⟨9205,.exit⟩ ∧
      At t 909 [(2535,b32 l.sharedBase)] ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop pos) visits ∧
      (∀ e, X.get (g,index) = some e → recurringPublicationEvent e → pos ≤ index) := by
  obtain ⟨site,hGet⟩ := hPub
  obtain ⟨⟨packet,rfl⟩,_,_,_⟩ := actualAsyncArrival hX hGet
  obtain ⟨finish,hLater,he⟩ := exitAfterPublication hX hGet hExit
  have prime (stage : Fin 2)
      (hs : X.get (g,index) = some ⟨(if stage = 0 then 674 else 904), .asyncArrive loc true⟩) :
      ∃ pos finish t visits, pos ≤ finish ∧ X.get (g,finish) = some ⟨9205,.exit⟩ ∧
        At t 909 [(2535,b32 l.sharedBase)] ∧
        Walk kernel Assumptions.all l g t ((X.tr g).drop pos) visits ∧
      (∀ e, X.get (g,index) = some e → recurringPublicationEvent e → pos ≤ index) := by
    obtain ⟨pos,t,vs,hPos,ht,hw⟩ := primingToDrainSeed hp hX stage hs hLater he
    refine ⟨pos,finish,t,vs,hPos,he,ht,hw,?_⟩
    intro e hAt hRecur
    obtain ⟨site, target, rfl⟩ := hRecur
    have hPc := congrArg Event.pc (Option.some.inj (hs.symm.trans hAt))
    have hLower : 909 ≤ Loader.reuseArrival site := by fin_cases site <;> decide
    have hUpper : (if stage = 0 then 674 else 904) ≤ 904 := by split <;> decide
    change (if stage = 0 then 674 else 904) = Loader.reuseArrival site at hPc
    omega
  have recurring (site : Fin 4)
      (hs : X.get (g,index) = some ⟨Loader.reuseArrival site, .asyncArrive loc true⟩) :
      ∃ pos finish t visits, pos ≤ finish ∧ X.get (g,finish) = some ⟨9205,.exit⟩ ∧
        At t 909 [(2535,b32 l.sharedBase)] ∧
        Walk kernel Assumptions.all l g t ((X.tr g).drop pos) visits ∧
      (∀ e, X.get (g,index) = some e → recurringPublicationEvent e → pos ≤ index) := by
    obtain ⟨pos,t,vs,hPos,ht,hw,_⟩ := actualEmptySeedPrefix hp hX site hs
    exact ⟨pos,finish,t,vs,hPos.trans hLater.le,he,ht,hw,fun _ _ _ => hPos⟩
  fin_cases packet
  · exact prime 0 hGet
  · exact prime 1 hGet
  · exact recurring 0 hGet
  · exact recurring 1 hGet
  · exact recurring 2 hGet
  · exact recurring 3 hGet

/-- The exact recurring packet prefix ends at the active loader drain scheduler. -/
theorem actualDrainFrontierOfPublication (hExit : Thread.Exited X g) :
    ∃ seed final finish t packetsFront,
      (X.tr g).drop seed = packetsFront ++ (X.tr g).drop (seed + packetsFront.length) ∧
      PacketsBeforeDrain l g 2 final packetsFront ∧
      seed + packetsFront.length ≤ finish ∧ X.get (g,finish) = some ⟨9205,.exit⟩ ∧
      At t 1744 (drainCarry l final) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (seed + packetsFront.length)) none ∧
      (∀ e, X.get (g,index) = some e → recurringPublicationEvent e → seed ≤ index) ∧
      (∀ e ∈ (X.tr g).drop (seed + packetsFront.length), ¬ recurringPublicationEvent e) := by
  obtain ⟨start,finish,s,vs,hStart,he,hs,hw,hSelected⟩ := actualDrainSeed hp hX hPub hExit
  obtain ⟨a,pre,tail,post,hSplit,ha,hTail,hQuiet,hEnd⟩ :=
    seedToDrainFrontier hs hw (exitInDrop he hStart)
  obtain ⟨final,b,packets,body,visits,hBody,hPackets,hb,hWalk,hExitBody⟩ :=
    packetsToDrain hp ha hTail hEnd
  let packetsFront := pre ++ packets
  let beforeDrain := start + packetsFront.length
  have hFull : (X.tr g).drop start = packetsFront ++ body := by
    rw [hSplit,hBody]
    simp only [packetsFront,List.append_assoc]
  have hDrop : (X.tr g).drop beforeDrain = body := by
    rw [← List.drop_drop, hFull, List.drop_left]
  have hBefore : beforeDrain ≤ finish := by
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hExitBody
    rw [← hDrop, List.getElem?_drop] at hi
    have hLen := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
    have hUnique := hRun.exit_last hi
    have hFinish := hRun.exit_last he
    omega
  have hRun : Run kernel Assumptions.all l g b ((X.tr g).drop beforeDrain) none :=
    hDrop ▸ runFromWalkExit hWalk hExitBody
  have hQuietAfter : ∀ e ∈ (X.tr g).drop beforeDrain, ¬ recurringPublicationEvent e := by
    rw [hDrop]
    exact noRecurringAfterDrain hb.1.ge hWalk
  exact ⟨start,final,finish,b,packetsFront,hDrop.symm ▸ hFull,
    .gap hQuiet hPackets,hBefore,he,hb,hRun,hSelected,hQuietAfter⟩

/-- Recover the final K/V cursor from an actual publication, including a lane that
published only its priming packets. The drain suffix is an indexed run to exit. -/
theorem actualDrainEntryOfPublication (hExit : Thread.Exited X g) :
    ∃ seed final pos finish t packetsFront,
      (X.tr g).drop seed = packetsFront ++ (X.tr g).drop (seed + packetsFront.length) ∧
      PacketsBeforeDrain l g 2 final packetsFront ∧
      seed + packetsFront.length ≤ pos ∧ pos ≤ finish ∧ X.get (g,finish) = some ⟨9205,.exit⟩ ∧
      At t 1863 (drainCarry l final) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) none ∧
      (∀ e, X.get (g,index) = some e → recurringPublicationEvent e → seed ≤ index) ∧
      (∀ e ∈ (X.tr g).drop (seed + packetsFront.length), ¬ recurringPublicationEvent e) := by
  obtain ⟨seed,final,finish,b,packets,hSplit,hPackets,hBefore,he,hb,hRun,hSelected,hQuiet⟩ :=
    actualDrainFrontierOfPublication hp hX hPub hExit
  obtain ⟨t,pos,hLo,hHi,ht,hSuffix⟩ := drainEntryBeforeExit hb hRun he hBefore 1
  exact ⟨seed,final,pos,finish,t,packets,hSplit,hPackets,hLo,hHi,he,ht,hSuffix,hSelected,hQuiet⟩


end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
