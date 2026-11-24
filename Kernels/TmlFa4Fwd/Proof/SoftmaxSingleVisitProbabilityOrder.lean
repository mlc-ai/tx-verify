-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstLoopEntry
import Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityStoreOrder
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

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

set_option maxRecDepth 100000 in
private theorem terminalBranches :
    (kernel.code.drop 7605).all (fun i => Thread.staysPastEvent 7605 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem terminalSegments :
    ∀ site, 7605 ≤ site → site ∈ Assumptions.swExp2Sites →
      ∀ seg, cuteExp2.matchAt kernel site = some seg → 7605 ≤ seg.stop := by
  intro site hSite hMem
  have hAudit : Assumptions.swExp2Sites.all (· < 7605) = true := by kernel_rfl
  have hLo := of_decide_eq_true (List.all_eq_true.mp hAudit site hMem)
  omega

private theorem singleVisitTerminalContinuation {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g cap past : Nat} {s : TState} {es : List Event}
    {mx : Option ℝ} {mass : ℝ} (hCap : 0 < cap) (hBound : cap < 2^31)
    (hPast : past+256 < 2^31)
    (hs : At s 5006 ((1228,b32 cap) :: firstLoopStable 1 past mx mass))
    (hr : Run kernel Assumptions.all l g s es none) :
    ∃ t, t.pc = 7605 ∧ Run kernel Assumptions.all l g t es none := by
  have hPlain : firstPlainSplit 1 cap = 0 := by unfold firstPlainSplit; omega
  have hBiased : firstBiasedRepeats 1 cap = 0 := by unfold firstBiasedRepeats; omega
  obtain ⟨u,hRun,hAt⟩ := firstLoopEntryTrace 1 cap past mx mass (by decide) (by decide)
    hCap hBound hPast hs hr
  change Run kernel Assumptions.all l g u es none at hRun
  have hu : At u 6654 (firstLoopChoiceFacts 1 0 past mx mass) := by
    simpa only [hPlain,hBiased,ite_true] using hAt
  obtain ⟨t,hR,hT⟩ := firstPlainEntryTrace hp 1 0 past mx mass (by decide) (by decide) hu hRun
  exact ⟨t,hT.1,hR⟩

def probabilityTraceIndex (q : Fin 4) : Nat := if q.val = 3 then 6 else q.val+1

private def storeSite (e : Event) : Option Nat :=
  match e.kind with
  | .tc (.st ..) => some e.pc
  | _ => none

private def firstStoreTraceSite : Fin 10 → Option Nat
  | 1 => some 4826
  | 2 => some 4835
  | 3 => some 4844
  | 6 => some 4856
  | _ => none

private theorem firstPublicationStoreSites (l : Launch) (g : Nat) (stage : Fin 2)
    (weights : Fin 4 → Nat → ℝ) (bar elect leader : Nat) (k : Fin 10) :
    ((firstPublicationEvents l g stage weights bar elect leader)[k.val]?).bind storeSite =
      firstStoreTraceSite k := by
  fin_cases k <;> rfl

private theorem firstStoreTraceIndexOfSite (k : Fin 10) (round : Round) (q : Fin 4)
    (h : firstStoreTraceSite k = some (probabilityPc round q)) :
    round = .first ∧ k.val = probabilityTraceIndex q := by
  cases round <;> fin_cases q <;> fin_cases k <;> first
    | exact ⟨rfl,rfl⟩
    | contradiction

/-- In an actual one-visit trace, only the four stores in the first publication
can write the probability banks. -/
theorem firstProbabilityStoresUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {warp : Fin 8} {g j batch head row cap past : Nat}
    (hCap : 0 < cap) (hBound : cap < 2^31) (hPast : past+256 < 2^31)
    (hRound : FirstRoundProgress p l X warp g j batch head row 1 cap past)
    {round : Round} (q : Fin 4) {store addr : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get (g,store) = some ⟨probabilityPc round q,.tc (.st addr vals shape)⟩) :
    round = .first ∧ store = j+1+probabilityTraceIndex q := by
  obtain ⟨s,bInst,eInst,leader,failed,_,hPub,hLead,hAck,hs,hRun⟩ := hRound
  let event : Event := ⟨probabilityPc round q,.tc (.st addr vals shape)⟩
  let post := if laneOf l g = leader then j+12 else j+11
  have hW : X.get (g,j+1) = some ⟨4826,.tc .waitLd⟩ := hPub 0
  have hEarlier := Thread.Scores.firstProbabilityWaitBeforeStore hX q hW he
  have hPC : event.pc < 7605 := by
    change probabilityPc round q < 7605
    cases round <;> fin_cases q <;> decide
  by_cases hIn : store < j+11
  · let k : Fin 10 := ⟨store-(j+1),by omega⟩
    have hGet := hPub k
    have hIndex : j+1+k.val = store := by dsimp [k]; omega
    rw [hIndex,he] at hGet
    have hSite := congrArg (fun v : Option Event => v.bind storeSite) hGet.symm
    rw [firstPublicationStoreSites] at hSite
    have hPubKind := firstStoreTraceIndexOfSite k round q hSite
    exact ⟨hPubKind.1,by rw [← hPubKind.2]; exact hIndex.symm⟩
  have hAfter : post ≤ store := by
    by_cases hL : laneOf l g = leader
    · have hNe : store ≠ j+11 := by
        intro h
        rw [h, hLead hL] at he
        exact Kind.noConfusion (congrArg Event.kind (Option.some.inj he))
      simp only [post,hL,ite_true]
      omega
    · simpa [post,hL] using Nat.le_of_not_gt hIn
  have hSuffix : ((X.tr g).drop post)[store-post]? = some event := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hAfter]
    exact he
  change (X.tr g).drop post = _ at hAck
  rw [hAck] at hSuffix
  have hAckPassed : failed+1 ≤ store-post := by
    by_contra! hMiss
    by_cases hFail : store-post < failed
    · rw [List.getElem?_append_left (by simpa using hFail)] at hSuffix
      have hRetry := (List.mem_replicate.mp (List.mem_of_getElem? hSuffix)).2
      exact Kind.noConfusion (congrArg Event.kind hRetry)
    · have hEq : store-post = failed := by omega
      rw [hEq,List.getElem?_append_right (by simp),List.length_replicate,Nat.sub_self] at hSuffix
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj hSuffix))
  have hAt : At s 5006 ((1228,b32 cap) :: firstLoopStable 1 past
      (scoreMax (fun c => maskedLogit p batch head row (visitKey 1 0 c)) (List.range 128))
      ((2:ℝ)^(-firstReference p batch head row 1) *
        maskedBlockSum (p.keyCount batch row) 1 0 (weight p batch head row))) := by
    refine hs.mono ⟨hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1,
      hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.1,trivial⟩
  obtain ⟨u,hFloor,hR⟩ := singleVisitTerminalContinuation hp hCap hBound hPast hAt hRun
  have hTarget : event ∈ (X.tr g).drop (post+failed+1) := by
    apply List.mem_of_getElem? (i := store-(post+failed+1))
    rw [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
    exact he
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hR
  exact (Nat.not_le_of_lt hPC
    (Thread.eventTailEventsOfSegmentFloor terminalBranches terminalSegments hWalk hFloor.ge
      event hTarget)).elim

end PTX.Kernels.TmlFa4Fwd.Softmax
